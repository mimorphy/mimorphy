#include "LambdaCalculus"
#include "Basic"
#include "FixedLengthString"
#include "RuntimeException"
#include "vector"
#include "set"
#include "map"
#include "memory"
#include "variant"

using std::vector;
using std::set;
using std::map;
using std::variant;
using std::isalnum;
using std::isdigit;
using std::isalpha;
using std::make_shared;

bool is_symbol(str_view symbol);
lambda_element lambda_variable_dot(str_view expression, sizevalue& index);
lambda_element free_variable_symbol(str_view expression, sizevalue& index);
lambda_element subexpression_in_brackets(str_view expression, sizevalue& index);

bool is_symbol(str_view symbol)
{
	if (symbol.empty()) {
		return false;
	}
	if (isdigit(symbol[0]) or not (isalpha(symbol[0]) or symbol[0] == STR("_")[0])) {
		return false;
	}
	for (sizevalue i = 1; i < symbol.size(); ++i) {
		if (not (isalnum(symbol[0]) or symbol[0] == STR("_")[0])) {
			return false;
		}
	}
	return true;
}

lambda_expression::lambda_expression(str_view expression)
{
	bool last_is_lambda_variable_dot = false;
	for (sizevalue i = 0; i < expression.size(); ++i) {
		if (expression[i] == STR(" ")[0]) {
			continue;
		}
		if (expression[i] == STR("λ")[0]) {
			elements.push_back(lambda_variable_dot(expression, i));
			last_is_lambda_variable_dot = true;
			continue;
		}
		if (expression[i] == STR("(")[0]) {
			elements.push_back(subexpression_in_brackets(expression, i));
			last_is_lambda_variable_dot = false;
			continue;
		}
		elements.push_back(free_variable_symbol(expression, i));
		last_is_lambda_variable_dot = false;
	}
	runtime_assert(not last_is_lambda_variable_dot, "λ表达式中存在非法的抽象('λ'后无函数体)");
}

str lambda_expression::get_element_string(const lambda_element& element) const
{
	if (const auto* bound = std::get_if<bound_variable>(&element)) {
		return STR("λ").data() + bound->name + STR(".").data();
	}
	else if (const auto* free = std::get_if<free_variable>(&element)) {
		return free->name;
	}
	else if (const auto* subexpr = std::get_if<lambda_subexpression>(&element)) {
		return STR("(").data() + subexpr->expr->get() + STR(")").data();
	}
	runtime_assert(false, "在 get_element_string 中执行到了不应该执行的地方");
	return {};
}

lambda_element lambda_variable_dot(str_view expression, sizevalue& index)
{
	++index;
	str_view variable_name = expression.substr(index);
	runtime_assert(not variable_name.empty(), "λ表达式中存在非法的抽象('λ'后无内容)");
	for (sizevalue i = 0; i < variable_name.size(); ++i) {
		if (variable_name[i] == STR(".")[0]) {
			variable_name = variable_name.substr(0, i);
			break;
		}
		++index;
	}
	runtime_assert(expression[index] == STR(".")[0], "λ表达式中存在非法的抽象('λ'后无'.')");
	runtime_assert(not variable_name.empty(), "λ表达式中存在非法的抽象('λ'与'.'之间没有标识符)");
	runtime_assert(is_symbol(variable_name), "λ表达式中存在非法的抽象('λ'与'.'之间的字符串" + variable_length(str(variable_name)) + "不满足标识符的要求)");
	return bound_variable(str(variable_name));
}

lambda_element free_variable_symbol(str_view expression, sizevalue& index)
{
	str_view variable_name = expression.substr(index);
	for (sizevalue i = 0; i < variable_name.size(); ++i) {
		if (variable_name[i] == STR(" ")[0] or variable_name[i] == STR(")")[0]) {
			variable_name = variable_name.substr(0, i);
			break;
		}
		++index;
	}
	runtime_assert(is_symbol(variable_name), "自由变量的名称" + variable_length(str(variable_name)) + "不满足标识符的要求");
	return std::move(free_variable(str(variable_name)));
}

lambda_element subexpression_in_brackets(str_view expression, sizevalue& index)
{
	++index;
	sizevalue nested_count = 1;
	str_view subexpression = expression.substr(index);
	for (sizevalue i = 0; i < subexpression.size(); ++i) {
		if (subexpression[i] == STR("(")[0]) {
			++nested_count;
			goto next;
		}
		if (subexpression[i] == STR(")")[0]) {
			--nested_count;
			if (nested_count == 0) {
				subexpression = subexpression.substr(0, i);
				break;
			}
			goto next;
		}
		next:
		++index;
	}
	return std::move(lambda_subexpression(make_shared<lambda_expression>(subexpression)));
}

str lambda_expression::get() const
{
	str result{};
	for (const auto& element : elements) {
		if (not result.empty()) {
			result += STR(" ").data();
		}
		result += get_element_string(element);
	}
	return std::move(result);
}

void lambda_expression::applicate()
{
	sizevalue index_of_first_bound_variable = sizevalue_max;
	set<str> bound_variables{};
	bool changes_exist = true;
	while (changes_exist) {
		index_of_first_bound_variable = sizevalue_max;
		bound_variables.clear();
		changes_exist = false;
		for (sizevalue i = 0; i < elements.size(); ++i) {
			// 查找第一个λ抽象
			if (holds_alternative<bound_variable>(elements[i])) {
				if (index_of_first_bound_variable == sizevalue_max) {
					index_of_first_bound_variable = i;
				}
				bound_variables.emplace(std::get<bound_variable>(elements[i]).name);
				continue;
			}
			// 在已发现左边的λ抽象的情况下，又发现右边的自由变量，那么进行应用
			if (index_of_first_bound_variable != sizevalue_max and holds_alternative<free_variable>(elements[i])) {
				if (bound_variables.contains(std::get<free_variable>(elements[i]).name)) {
					continue;
				}
				process_free_variable_in_application(elements, index_of_first_bound_variable, i);
				changes_exist = true;
				continue;
			}
			// 在已发现左边的λ抽象的情况下，又发现右边的子表达式，那么进行应用
			if (index_of_first_bound_variable != sizevalue_max and holds_alternative<lambda_subexpression>(elements[i])) {
				process_subexpression_in_application(elements, index_of_first_bound_variable, i);
				changes_exist = true;
				continue;
			}
			// 对嵌套λ表达式的处理
			if (holds_alternative<lambda_subexpression>(elements[i])) {
				process_nested_expression_in_application(elements, index_of_first_bound_variable, i);
				continue;
			}
		}
	}
}

void lambda_expression::process_free_variable_in_application(vector<lambda_element>& elements, sizevalue& index_of_first_bound_variable, sizevalue& index)
{
	if (holds_alternative<lambda_subexpression>(elements[index_of_first_bound_variable])) {
		applicate_between_subexpression(elements[index_of_first_bound_variable], elements[index]);
		if (std::get<lambda_subexpression>(elements[index_of_first_bound_variable]).expr->elements.size() == 1) {
			elements[index_of_first_bound_variable] = std::get<lambda_subexpression>(elements[index_of_first_bound_variable]).expr->elements[0];
		}
		lambda_element element = elements[index];
		bool first_element_is_bound = start_is_bound(element);
		if (not first_element_is_bound) {
			index_of_first_bound_variable = sizevalue_max;
		}
		elements.erase(elements.begin() + index);
		--index;
		return;
	}
	str_view bound_variable_name = std::get<bound_variable>(elements[index_of_first_bound_variable]).name;
	for (sizevalue j = index_of_first_bound_variable; j < elements.size(); ++j) {
		if (holds_alternative<free_variable>(elements[j])) {
			if (std::get<free_variable>(elements[j]).name == bound_variable_name) {
				elements[j] = elements[index];
			}
			continue;
		}
		// 检测变量遮蔽
		if (holds_alternative<bound_variable>(elements[j])) {
			if (std::get<bound_variable>(elements[j]).name == bound_variable_name) {
				return;
			}
		}
	}
	elements.erase(elements.begin() + index);
	elements.erase(elements.begin() + index_of_first_bound_variable);
	index -= 2;
	if (index_of_first_bound_variable < elements.size()) {
		if (not holds_alternative<bound_variable>(elements[index_of_first_bound_variable])) {
			index_of_first_bound_variable = sizevalue_max;
		}
	}
}

void lambda_expression::process_subexpression_in_application(vector<lambda_element>& elements, sizevalue& index_of_first_bound_variable, sizevalue& index)
{
	if (holds_alternative<lambda_subexpression>(elements[index_of_first_bound_variable])) {
		applicate_between_subexpression(elements[index_of_first_bound_variable], elements[index]);
		if (std::get<lambda_subexpression>(elements[index_of_first_bound_variable]).expr->elements.size() == 1) {
			elements[index_of_first_bound_variable] = std::get<lambda_subexpression>(elements[index_of_first_bound_variable]).expr->elements[0];
		}
		lambda_element element = elements[index];
		bool first_element_is_bound = start_is_bound(element);
		if (not first_element_is_bound) {
			index_of_first_bound_variable = sizevalue_max;
		}
		elements.erase(elements.begin() + index);
		--index;
		return;
	}
	str_view bound_variable_name = std::get<bound_variable>(elements[index_of_first_bound_variable]).name;
	for (sizevalue j = index_of_first_bound_variable; j < elements.size(); ++j) {
		if (holds_alternative<free_variable>(elements[j])) {
			if (std::get<free_variable>(elements[j]).name == bound_variable_name) {
				elements[j] = elements[index];
			}
			continue;
		}
		// 检测变量遮蔽
		if (holds_alternative<bound_variable>(elements[j])) {
			if (std::get<bound_variable>(elements[j]).name == bound_variable_name) {
				return;
			}
		}
	}
	elements.erase(elements.begin() + index);
	elements.erase(elements.begin() + index_of_first_bound_variable);
	index -= 2;
	if (index_of_first_bound_variable < elements.size()) {
		if (not holds_alternative<bound_variable>(elements[index_of_first_bound_variable])) {
			index_of_first_bound_variable = sizevalue_max;
		}
	}
}

void lambda_expression::process_nested_expression_in_application(vector<lambda_element>& elements, sizevalue& index_of_first_bound_variable, sizevalue& index)
{
	lambda_element element = elements[index];
	if (elements.size() == 1) {
		vector<lambda_element>& sub_elements = std::get<lambda_subexpression>(element).expr->elements;
		elements = vector<lambda_element>(sub_elements.begin(), sub_elements.end());
		index = sizevalue_max;
		return;
	}
	bool first_element_is_bound = start_is_bound(element);
	if (first_element_is_bound) {
		index_of_first_bound_variable = index;
		return;
	}
	if (holds_alternative<free_variable>(element)) {
		return;
	}
	if (std::get<lambda_subexpression>(element).expr->elements.size() == 1) {
		elements[index] = std::get<lambda_subexpression>(element).expr->elements[0];
	}
}

void lambda_expression::applicate_between_subexpression(lambda_element& left, lambda_element& right)
{
	lambda_subexpression left_expr = std::get<lambda_subexpression>(left);
	str bound_name = std::get<bound_variable>(left_expr.expr->elements[0]).name;
	for (sizevalue i = 1; i < left_expr.expr->elements.size(); ++i) {
		if (holds_alternative<free_variable>(left_expr.expr->elements[i])) {
			if (std::get<free_variable>(left_expr.expr->elements[i]).name == bound_name) {
				left_expr.expr->elements[i] = right;
			}
			continue;
		}
		// 检测变量遮蔽
		if (holds_alternative<bound_variable>(left_expr.expr->elements[i])) {
			if (std::get<bound_variable>(left_expr.expr->elements[i]).name == bound_name) {
				return;
			}
		}
	}
	left_expr.expr->elements.erase(left_expr.expr->elements.begin());
}

bool lambda_expression::start_is_bound(lambda_element& element)
{
	while (holds_alternative<lambda_subexpression>(element)) {
		runtime_assert(not std::get<lambda_subexpression>(element).expr->elements.empty(), "λ表达式在应用的过程中产生了空表达式");
		element = std::get<lambda_subexpression>(element).expr->elements[0];
	}
	return holds_alternative<bound_variable>(element);
}

void lambda_expression::applicate(const lambda_expression& right)
{
	elements = { lambda_element(lambda_subexpression(make_shared<lambda_expression>(*this))) };
	elements.insert(elements.end(), right.elements.begin(), right.elements.end());
	applicate();
}

void lambda_expression::applicate(lambda_expression&& right)
{
	elements = { lambda_element(lambda_subexpression(make_shared<lambda_expression>(*this))) };
	elements.insert(elements.end(), right.elements.begin(), right.elements.end());
	applicate();
}

static byte_array output_information(set<str>& object)
{
	byte_array information = "{ ";
	for (auto& element : object) {
		if (information != "{ ") {
			information += ", ";
		}
		information += variable_length(element);
	}
	information += " }";
	return std::move(information);
}

void lambda_expression::replace(map<str, lambda_expression>& definitions, set<str>& already_appeared_definitions)
{
	for (sizevalue i = 0; i < elements.size(); ++i) {
		if (holds_alternative<free_variable>(elements[i])) {
			str free_variable_name = std::get<free_variable>(elements[i]).name;
			runtime_assert(not already_appeared_definitions.contains(free_variable_name), "λ表达式在应用的过程中产生了死循环，应用展开的定义有" + output_information(already_appeared_definitions) + "，截止于第二次\"" + variable_length(free_variable_name) + "\"");
			if (definitions.contains(free_variable_name)) {
				lambda_expression expression = definitions[free_variable_name];
				already_appeared_definitions.emplace(free_variable_name);
				expression.replace(definitions, already_appeared_definitions);
				already_appeared_definitions.erase(free_variable_name);
				elements[i] = expression.elements.size() == 1 ? expression.elements[0] : std::move(lambda_subexpression(make_shared<lambda_expression>(expression)));
			}
		}
	}
}

void lambda_expression::applicate(map<str, lambda_expression>& definitions)
{
	expand(definitions);
	applicate();
}

void lambda_expression::applicate(const lambda_expression& right, map<str, lambda_expression>& definitions)
{
	elements.insert(elements.end(), right.elements.begin(), right.elements.end());
	applicate(definitions);
}

void lambda_expression::applicate(lambda_expression&& right, map<str, lambda_expression>& definitions)
{
	elements.insert(elements.end(), right.elements.begin(), right.elements.end());
	applicate(definitions);
}

void lambda_expression::expand(map<str, lambda_expression>& definitions)
{
	set<str> already_appeared_definitions{};
	replace(definitions, already_appeared_definitions);
}

bool lambda_expression::operator==(const lambda_expression& right) const
{
	if (elements.size() != right.elements.size()) {
		return false;
	}
	set<str> appeared_left_bound_variable{};
	map<str, str> right_bound_variable_to_left_bound_variable{};
	for (sizevalue i = 0; i < elements.size(); ++i) {
		if (elements[i].index() != right.elements[i].index()) {
			return false;
		}
		if (holds_alternative<bound_variable>(elements[i])) {
			str left_bound_name = std::get<bound_variable>(elements[i]).name;
			str right_bound_name = std::get<bound_variable>(right.elements[i]).name;
			bool left_existed = appeared_left_bound_variable.contains(left_bound_name);
			bool right_existed = right_bound_variable_to_left_bound_variable.contains(right_bound_name);
			if (left_existed != right_existed) {
				return false;
			}
			if (left_existed and right_bound_variable_to_left_bound_variable[right_bound_name] != left_bound_name) {
				return false;
			}
			right_bound_variable_to_left_bound_variable[right_bound_name] = left_bound_name;
			appeared_left_bound_variable.emplace(left_bound_name);
		}
		else if (holds_alternative<free_variable>(elements[i])) {
			str left_free_name = std::get<free_variable>(elements[i]).name;
			str right_free_name = std::get<free_variable>(right.elements[i]).name;
			if (right_bound_variable_to_left_bound_variable[right_free_name] != left_free_name) {
				return false;
			}
		}
		else if (holds_alternative<lambda_subexpression>(elements[i])) {
			if (std::get<lambda_subexpression>(elements[i]).expr != std::get<lambda_subexpression>(right.elements[i]).expr) {
				return false;
			}
		}
	}
	return true;
}