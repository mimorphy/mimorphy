#include <build-regular-table>
#include <basic>
#include <fixed-length-string>
#include <runtime-exception>
#include <state-transition>
#include <concatenate-regular-table>
#include <execution>
#include <algorithm>
#include <vector>

// 自动机上下文：用于表示一个虚转移节点未展开的自动机
struct regular_table_context
{
    regular_table regular_table{};
    vector<vector<state_transition>> virtual_transitions_table{};
};

// character_symbol 结构：
// 当 c != character_max 时，character_symbol 实例代表字面字符 c
// 当 c == character_max 时，character_symbol 实例代表特殊操作 functional
struct character_symbol
{
    character c = 0;
    sizevalue functional = 0;
    bool is_functional_symbol() const { return c == character_max; }
};

// ewp_with_index 结构：
// - ewp 为一个 expression_with_operation 实例
// - index 为在上下文中的索引(即第几个 ewp)
struct ewp_with_index
{
    expression_with_operation ewp;
    sizevalue index;
};

static character escape_character(character c);
static character_symbol next_symbol_of_expression(str_view expression, sizevalue& index, span<functional_operation> functional_operations, sizevalue index_of_exception_pool);
static expression_with_operation determine_prefix_range(str_view expression, character_symbol& prefix_symbol, sizevalue& index, sizevalue preindex, span<functional_operation> functional_operations, sizevalue index_of_exception_pool);
static expression_with_operation build_prefix(str_view expression, character_symbol& symbol, sizevalue& index, sizevalue preindex, sizevalue index_of_exception_pool);
static void build_literal_charcater(vector<ewp_with_index>& ewpwis, str_view expression, sizevalue& index, sizevalue preindex, sizevalue index_of_exception_pool);
static expression_information build_literal_expression(str_view expression, sizevalue index_of_exception_pool);
static void join_expression_information(expression_information& target, expression_information& source);
static void connect_predecessors_and_successors(regular_table& regular_table, vector<vector<state_transition>>& virtual_transitions_table, vector<sizevalue>& index_of_predecessors, vector<sizevalue> index_of_successors, sizevalue index_of_exception_pool);
static regular_table_context information_to_regular_table_context(expression_information& information, sizevalue index_of_exception_pool);
static void expand_virtual_transition(regular_table_context& context);
static expression_information build_expression_information(API::expression_information api_information);

// 逻辑规范：
// 前置条件：expression 是一个合法的表达式
// 后置条件：输出 expression 对应的自动机
regular_table build_regular_table(str_view expression, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    if (expression.empty()) {
        return { state_transition(1), state_transition(sizevalue_max) };
    }
    expression_information information = build_expression_information(expression, functional_operations, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    // 后续处理
    regular_table_context context = information_to_regular_table_context(information, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    expand_virtual_transition(context);
    return std::move(context.regular_table);
}

// 逻辑规范：
// 前置条件：无
// 后置条件：输出 escape(c)
//     escape(c: character) -> character 定义为
//     '\0', 且 c == '0' 时
//     '\a', 且 c == 'a' 时
//     '\b', 且 c == 'b' 时
//     '\t', 且 c == 't' 时
//     '\n', 且 c == 'n' 时
//     '\v', 且 c == 'v' 时
//     '\f', 且 c == 'f' 时
//     '\e', 且 c == 'e' 时
//     c, 当以上条件均不被满足时
static character escape_character(character c)
{
    switch (c) {
    case STR("0")[0]:
        c = STR("\0")[0];
        break;
    case STR("a")[0]:
        c = STR("\a")[0];
        break;
    case STR("b")[0]:
        c = STR("\b")[0];
        break;
    case STR("t")[0]:
        c = STR("\t")[0];
        break;
    case STR("n")[0]:
        c = STR("\n")[0];
        break;
    case STR("v")[0]:
        c = STR("\v")[0];
        break;
    case STR("f")[0]:
        c = STR("\f")[0];
        break;
    case STR("e")[0]:
        c = STR("\e")[0];
        break;
    }
    return c;
}

// 逻辑规范：
// 前置条件：!expression.empty()
// 后置条件：判断 expression 的开头往后是否存在符合 functional_operations 任意一个操作的字面形式，若存在，输出这个操作在 functional_operations 中的索引，否则输出 sizevalue_max，同时将 offset 赋值为这个匹配形式的长度
static sizevalue find_match_operation(str_view expression, sizevalue& offset, span<functional_operation> functional_operations)
{
    for (sizevalue i = 0; i < functional_operations.size(); ++i) {
        if (functional_operations[i].form == expression.front()) {
            offset += 2;
            return i;
        }
    }
    return sizevalue_max;
}

// 逻辑规范：
// 前置条件：index < expression.size()
// 后置条件：输出 expression 中以 index 为起始，往后的第一个字面字符标记或特殊字符标记，同时 index 被更新为在代表这个字符标记之后的第一个字符的索引 (一种特殊情况：一个字面字符后紧接闭包运算，此时输出的标记中不仅含有字面字符，也含有特殊字符闭包)
static character_symbol next_symbol_of_expression(str_view expression, sizevalue& index, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    runtime_assert(index < expression.size(), "next_symbol_of_expression 的前置条件不被满足");
    character_symbol symbol{};
    // 当满足以下条件时，说明这是转义字符，要求 index + 1 < expression.size()
    if (expression[index] == STR("\\")[0]) {
        runtime_assert(index + 1 < expression.size(), "禁止出现没有后继内容的转义字符", index_of_exception_pool);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        sizevalue offset = 0;
        sizevalue index_of_operation = find_match_operation(expression.substr(index + 1), offset, functional_operations);
        // 是转义的特殊字符
        if (index_of_operation != sizevalue_max) {\
            symbol.c = character_max;
            symbol.functional = index_of_operation;
            index += offset;
        }
        // 是转义的字面字符
        else {
            symbol = { escape_character(expression[index + 1]) };
            index += 2;
        }
        return std::move(symbol);
    }
    // expression[index] != STR("\\")[0]，只能是非转义字面字符
    index += 1;
    symbol = { expression[index - 1] };
    return std::move(symbol);
}

// 逻辑规范：
// 前置条件：expression 有效
// 后置条件：输出 expression 对应的 expression_information
expression_information build_expression_information(str_view expression, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    expression_information information{};
    information.content.reserve(expression.size());
    sizevalue i = 0;
    vector<ewp_with_index> ewpwis{};
    // 主循环：
    while (i < expression.size()) {
        sizevalue preindex = i;
        character_symbol symbol = next_symbol_of_expression(expression, i, functional_operations, index_of_exception_pool);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        expression_with_operation ewp{};
        // 如果是特殊字符标记，进行特殊处理
        if (symbol.is_functional_symbol()) {
            byte_array temp{};
            switch (functional_operations[symbol.functional].type) {
            case operation_type::DEFAULT:
                ewpwis.push_back({ { str_view(expression.data() + preindex, 0), 0, symbol.functional }, ewpwis.size() });
                build_literal_charcater(ewpwis, expression, i, preindex, index_of_exception_pool);
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
                break;
            case operation_type::PREFIX:
                temp = "在处理\"" + variable_length(expression.data()) + "\"的前缀运算时，禁止前缀运算的右侧没有表达式";
                runtime_assert(i < expression.size(), temp.c_str(), index_of_exception_pool);
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
                // 获取前缀运算为主要运算的 ewp
                ewp = build_prefix(expression, symbol, i, preindex, index_of_exception_pool);
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
                ewpwis.push_back({ std::move(ewp), ewpwis.size() }); // 添加到数组中
                break;
            case operation_type::INFIX:
                temp = "在处理\"" + variable_length(expression.data()) + "\"的中缀运算时，禁止中缀运算的左侧没有表达式";
                runtime_assert(!ewpwis.empty(), temp.c_str(), index_of_exception_pool);
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
                temp = "在处理\"" + variable_length(expression.data()) + "\"的中缀运算时，禁止中缀运算的右侧没有表达式";
                runtime_assert(i < expression.size(), temp.c_str(), index_of_exception_pool);
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
                ewpwis.clear(); // 中缀运算的处理优先级最高，清空所有的其他 ewp
                ewp = { expression, preindex, symbol.functional };
                ewpwis.push_back({ std::move(ewp), ewpwis.size() }); // 使此 ewp 成为数组中的唯一一个 ewp，跳出循环
                goto finish_loop;
            case operation_type::POSTFIX:
                temp = "在处理\"" + variable_length(expression.data()) + "\"的后缀运算时，禁止后缀运算不修饰其他部分单独出现";
                runtime_assert(false, temp.c_str(), index_of_exception_pool);
                break;
            }
            continue;
        }
        if (ewpwis.empty()) {
            // 如果为空，添加保底的一个元素作为容器
            ewpwis.push_back({ { str_view(expression.data(), 0), sizevalue_max, sizevalue_max }, 0 });
        }
        if (ewpwis.back().ewp.operation_id != sizevalue_max) {
            // 若满足 operation_id != sizevalue_max，说明最后一个 ewp 是有主要运算的 ewp，那么添加一个新 ewp 用于字面字符
            ewpwis.push_back({ { str_view(expression.data() + preindex, 0), sizevalue_max, sizevalue_max }, ewpwis.size() });
        }
        // 否则是字面字符标记
        build_literal_charcater(ewpwis, expression, i, preindex, index_of_exception_pool);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
    }
    finish_loop:
    vector<expression_information> subexpressions(ewpwis.size());
    if (subexpressions.size() == 1 && ewpwis.front().ewp.operation_id == sizevalue_max) {
        // 如果满足以上条件，说明这是一个不存在主要运算的表达式，那么直接进行字面字符式的解析
        subexpressions = { build_literal_expression(ewpwis.front().ewp.expression, index_of_exception_pool) };
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
    }
    else {
        // 否则根据主要运算编译表达式
        auto compile = [&subexpressions, &functional_operations, &index_of_exception_pool](ewp_with_index& ewpwi) {
            if (ewpwi.ewp.operation_id == sizevalue_max) {
                subexpressions[ewpwi.index] = build_expression_information(ewpwi.ewp.expression, functional_operations, index_of_exception_pool);
            }
            else {
                auto result = reinterpret_cast<API::expression_information* (*)(address, sizevalue, sizevalue, sizevalue, address, sizevalue, sizevalue)>(functional_operations[ewpwi.ewp.operation_id].func)(reinterpret_cast<address>(ewpwi.ewp.expression.data()), ewpwi.ewp.expression.size(), ewpwi.ewp.index_of_operation, ewpwi.ewp.operation_id, reinterpret_cast<address>(functional_operations.data()), functional_operations.size(), index_of_exception_pool);
                subexpressions[ewpwi.index] = build_expression_information(*result);
                API::release_expression_information(result);
            }
        };
        std::for_each(std::execution::par, ewpwis.begin(), ewpwis.end(), compile);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        // 按顺序连接编译过的信息
        for (sizevalue i = 1; i < subexpressions.size(); ++i) {
            concatenate_expression_information(subexpressions.front(), subexpressions[i]);
        }
    }
    return std::move(subexpressions.front());
}

constexpr sizevalue LEFT_BRACKET_ID = 2;
constexpr sizevalue RIGHT_BRACKET_ID = 3;
// 逻辑规范：
// 前置条件：expression, symbol, pre_index 皆有效
// 后置条件：根据 expression，输出对应操作在 expression 中的对应范围的 expression_with_operation，并更新 index 为范围之后的第一个索引
static expression_with_operation determine_prefix_range(str_view expression, character_symbol& prefix_symbol, sizevalue& index, sizevalue preindex, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    expression_with_operation ewp{};
    sizevalue nested_count = 0;
    if (prefix_symbol.functional == LEFT_BRACKET_ID) {
        nested_count += 1;
    }
    bool is_failed = true;
    bool is_first_symbol = true;
    while (index < expression.size()) {
        character_symbol symbol = next_symbol_of_expression(expression, index, functional_operations, index_of_exception_pool);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        if (is_first_symbol) {
            is_first_symbol = false;
            // 如果前缀运算之后的第一个符号是前揣、中缀、后缀运算的其中一种，那么抛出错误，因为这种写法不被允许 (除了一个左括号配一个前缀运算的情况，这种情况是合法的)
            if (symbol.is_functional_symbol() && !(functional_operations[prefix_symbol.functional].type == operation_type::PREFIX && symbol.functional == LEFT_BRACKET_ID) && !(functional_operations[symbol.functional].type == operation_type::PREFIX && prefix_symbol.functional == LEFT_BRACKET_ID)) {
                byte_array temp = "在处理\"" + variable_length(expression.data()) + "\"的前缀运算时，禁止直接后继前中后缀的任意运算";
                runtime_assert(functional_operations[symbol.functional].type != operation_type::PREFIX && functional_operations[symbol.functional].type != operation_type::INFIX && functional_operations[symbol.functional].type != operation_type::POSTFIX, temp.c_str(), index_of_exception_pool);
            }
        }
        // 如果遇到左括号
        if (symbol.functional == LEFT_BRACKET_ID) {
            nested_count += 1;
        }
        // 如果遇到右括号
        else if (symbol.functional == RIGHT_BRACKET_ID) {
            byte_array temp = "在处理\"" + variable_length(expression.data()) + "\"的前缀运算时出现了无左括号对应的右括号";
            runtime_assert(nested_count != 0, temp.c_str(), index_of_exception_pool);
            nested_count -= 1;
        }
        // 满足以下条件时说明作用域结束，跳出循环
        if (nested_count == 0) {
            is_failed = false;
            break;
        }
    }
    byte_array temp = "在处理\"" + variable_length(expression.data()) + "\"的前缀运算时，由于表达式不完整而无法正确解析";
    runtime_assert(!is_failed, temp.c_str(), index_of_exception_pool);
    ewp.expression = str_view(expression.data() + preindex, index - preindex);
    ewp.index_of_operation = 0;
    ewp.operation_id = prefix_symbol.functional;
    return std::move(ewp);
}

// build_expression_information 用于构建前缀运算 ewp 的分函数
static expression_with_operation build_prefix(str_view expression, character_symbol& symbol, sizevalue& index, sizevalue preindex, sizevalue index_of_exception_pool)
{
    // 获取前缀运算为主要运算的 ewp
    expression_with_operation ewp = determine_prefix_range(expression, symbol, index, preindex, functional_operations, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    bool has_postfix = false;
    // 判断之后是否存在后缀运算
    if (index < expression.size()) {
        preindex = index;
        character_symbol test_symbol = next_symbol_of_expression(expression, index, functional_operations, index_of_exception_pool);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        if (test_symbol.is_functional_symbol()) {
            if (functional_operations[test_symbol.functional].type == operation_type::POSTFIX) {
                // 存在后缀运算，那么将 ewp 的主要运算改为后缀运算，并更新表达式范围
                has_postfix = true;
                ewp.expression = str_view(ewp.expression.data(), ewp.expression.size() + (index - preindex));
                ewp.index_of_operation = ewp.expression.size() - (index - preindex);
                ewp.operation_id = test_symbol.functional;
            }
        }
        if (!has_postfix) {
            index = preindex;
        }
    }
    return std::move(ewp);
}

// build_expression_information 用于构建字面字符 ewp 的分函数
static void build_literal_charcater(vector<ewp_with_index>& ewpwis, str_view expression, sizevalue& index, sizevalue preindex, sizevalue index_of_exception_pool)
{
    bool has_postfix = false;
    // 判断之后是否存在后缀运算
    if (index < expression.size()) {
        sizevalue new_preindex = index;
        character_symbol test_symbol = next_symbol_of_expression(expression, index, functional_operations, index_of_exception_pool);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return;
        }
        if (test_symbol.is_functional_symbol()) {
            if (functional_operations[test_symbol.functional].type == operation_type::POSTFIX) {
                // 存在后缀运算
                has_postfix = true;
                if (ewpwis.back().ewp.expression.empty()) {
                    ewpwis.back().ewp.expression = str_view(ewpwis.back().ewp.expression.data(), index - preindex);
                    ewpwis.back().ewp.index_of_operation = new_preindex;
                    ewpwis.back().ewp.operation_id = test_symbol.functional;
                }
                else {
                    ewpwis.push_back({ { str_view(ewpwis.back().ewp.expression.data() + preindex, index - preindex), new_preindex - preindex, test_symbol.functional }, ewpwis.size() });
                }
            }
        }
        if (!has_postfix) {
            index = new_preindex;
        }
    }
    if (!has_postfix) {
        // 不存在后缀运算，正常处理
        ewpwis.back().ewp.expression = str_view(ewpwis.back().ewp.expression.begin(), ewpwis.back().ewp.expression.size() + (index - preindex)); // 往后递增此字面字符所占的长度
    }
}

// 逻辑规范：
// 前置条件：expression 中的所有符号都被视为字面字符，且 expression 不为空
// 后置条件：输出 expression 对应的 expression_information
static expression_information build_literal_expression(str_view expression, sizevalue index_of_exception_pool)
{
    runtime_assert(!expression.empty(), "build_literal_expression 的前置条件不被满足");
    expression_information expr{};
    sizevalue i = 0;
    // 主循环：
    while (i < expression.size()) {
        character_symbol symbol = next_symbol_of_expression(expression, i, functional_operations, index_of_exception_pool);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        state_transition st = state_transition(symbol.c, state_transition_type::DEFAULT);
        expr.content.push_back(std::move(st));
    }
    expr.index_of_heads = { 0 };
    expr.index_of_tails = { expr.content.size() - 1 };
    return std::move(expr);
}

expression_information nothing(expression_with_operation ewp, span<functional_operation> functional_operations, sizevalue index_of_exception_pool) { return {}; }

// 逻辑规范：
// 前置条件：无
// 后置条件：输出 'ε' 对应的 expression_information
expression_information epsilon(expression_with_operation ewp, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    return expression_information{ {}, {}, {}, {}, true };
}

// 逻辑规范：
// 前置条件：无
// 后置条件：输出 '·' 对应的 expression_information
expression_information center_dot(expression_with_operation ewp, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    return expression_information{ { state_transition(0, state_transition_type::ANY) }, { 0 }, { 0 }, {}, false };
}

// 逻辑规范：
// 前置条件：ewp 有效
// 后置条件：输出 "(expr)" 中 expr 的 expression_information
expression_information left_bracket(expression_with_operation ewp, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    return build_expression_information(ewp.expression.substr(2, ewp.expression.size() - 4), functional_operations, index_of_exception_pool);
}

// 逻辑规范：
// 前置条件：ewp 有效
// 后置条件：输出 "left|right" 对应的 expression_information
expression_information alternation(expression_with_operation ewp, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    expression_information left = build_expression_information(ewp.expression.substr(0, ewp.index_of_operation), functional_operations, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    expression_information right = build_expression_information(ewp.expression.substr(ewp.index_of_operation + 2), functional_operations, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    join_expression_information(left, right);
    return std::move(left);
}

// 逻辑规范：
// 前置条件：target, source 皆有效
// 后置条件：target 和 source 取并集作为结果赋值到 target 中
static void join_expression_information(expression_information& target, expression_information& source)
{
    // 如果 target 为空，直接复制返回
    if (target.content.empty()) {
        bool target_has_escape_transition = target.exists_escape_transition;
        target = source;
        target.exists_escape_transition = target_has_escape_transition || source.exists_escape_transition;
        return;
    }
    // 如果 source 为空，直接返回
    if (source.content.empty()) {
        target.exists_escape_transition = target.exists_escape_transition || source.exists_escape_transition;
        return;
    }
    // 如果 target 不为空，且最后一个节点不是虚转移节点，添加末尾的虚转移节点
    if (!target.content.back().is_transfer_transition()) {
        target.content.push_back(target.virtual_transitions_table.size());
        target.virtual_transitions_table.push_back({});
    }
    sizevalue offset_of_source = target.content.size();
    sizevalue offset_of_virtual_table = target.virtual_transitions_table.size();
    // 进行节点衔接
    target.content.insert(target.content.end(), source.content.begin(), source.content.end());
    // 进行虚转移表的衔接
    target.virtual_transitions_table.insert(target.virtual_transitions_table.end(), source.virtual_transitions_table.begin(), source.virtual_transitions_table.end());
    // 遍历新部分的状态节点
    for (sizevalue i = offset_of_source; i < target.content.size(); ++i) {
        // 如果是虚转移节点，修正索引为其在新虚转移表中的索引
        if (target.content[i].is_transfer_transition()) {
            target.content[i] = state_transition(target.content[i].index() + offset_of_virtual_table);
        }
    }
    // 遍历新部分的虚转移表
    for (sizevalue i = offset_of_virtual_table; i < target.virtual_transitions_table.size(); ++i) {
        // 修正新部分虚转移表中的转移路径的索引
        std::for_each(target.virtual_transitions_table[i].begin(), target.virtual_transitions_table[i].end(), [&offset_of_source](state_transition& st) { st = state_transition(st.index() + offset_of_source); });
    }
    // 进行首尾的叠加
    vector<sizevalue> new_index_of_heads_of_source = source.index_of_heads;
    std::for_each(new_index_of_heads_of_source.begin(), new_index_of_heads_of_source.end(), [&offset_of_source](sizevalue& index) { index += offset_of_source; });
    target.index_of_heads.insert(target.index_of_heads.end(), new_index_of_heads_of_source.begin(), new_index_of_heads_of_source.end());
    vector<sizevalue> new_index_of_tails_of_source = source.index_of_tails;
    std::for_each(new_index_of_tails_of_source.begin(), new_index_of_tails_of_source.end(), [&offset_of_source](sizevalue& index) { index += offset_of_source; });
    target.index_of_tails.insert(target.index_of_tails.end(), new_index_of_tails_of_source.begin(), new_index_of_tails_of_source.end());
    // 判断是否存在贯穿的转移路径
    target.exists_escape_transition = target.exists_escape_transition || source.exists_escape_transition;
}

// 逻辑规范：
// 前置条件：ewp 有效
// 后置条件：输出 expr* 对应的 expression_information
expression_information kleene_star(expression_with_operation ewp, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    expression_information expr = build_expression_information(ewp.expression.substr(0, ewp.index_of_operation), functional_operations, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    expr.exists_escape_transition = true;
    if (!expr.content.back().is_transfer_transition()) {
        expr.content.push_back(state_transition(expr.virtual_transitions_table.size()));
        expr.virtual_transitions_table.push_back({});
    }
    connect_predecessors_and_successors(expr.content, expr.virtual_transitions_table, expr.index_of_tails, expr.index_of_heads, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    return std::move(expr);
}

// 逻辑规范：
// 前置条件：index_of_predecessors 中不存在自身不为虚转移节点且后继节点也不为虚转移节点，但是需要转移到 index_of_successors 中不直接相邻的节点的节点
// 后置条件：index_of_predecessors 中指向的所有的虚转移表，其中包含所有指向 index_of_successors 中索引的转移节点 (连接的两个节点直接相邻时省略转移)
static void connect_predecessors_and_successors(regular_table& regular_table, vector<vector<state_transition>>& virtual_transitions_table, vector<sizevalue>& index_of_predecessors, vector<sizevalue> index_of_successors, sizevalue index_of_exception_pool)
{
    for (auto index_of_predecessor : index_of_predecessors) {
        for (auto index_of_successor : index_of_successors) {
            if (regular_table[index_of_predecessor].is_transfer_transition()) {
                virtual_transitions_table[regular_table[index_of_predecessor].index()].push_back(state_transition(index_of_successor));
            }
            else if (index_of_predecessor + 1 < regular_table.size()) {
                if (regular_table[index_of_predecessor + 1].is_transfer_transition()) {
                    virtual_transitions_table[regular_table[index_of_predecessor + 1].index()].push_back(state_transition(index_of_successor));
                }
                else {
                    goto last;
                }
            }
            else {
                last:
                // index_of_predecessor + 1 == index_of_successor 成立时即连接的两个节点直接相邻，此时省略转移
                runtime_assert(index_of_predecessor + 1 == index_of_successor, "禁止为没有特殊转移路径的节点添加新的转移路径", index_of_exception_pool);
            }
        }
    }
}

// 逻辑规范：
// 前置条件：information 有效
// 后置条件：输出 information 对应的 regular_table_context
static regular_table_context information_to_regular_table_context(expression_information& information, sizevalue index_of_exception_pool)
{
    regular_table_context context{};
    if (information.content.empty()) {
        return std::move(context);
    }
    bool start_is_transfer = information.content.front().is_transfer_transition();
    // 初始化
    context.virtual_transitions_table = std::move(information.virtual_transitions_table);
    if (!start_is_transfer) {
        vector<state_transition> temp{};
        context.virtual_transitions_table.insert(context.virtual_transitions_table.begin(), temp); // 在开头添加一个虚转移组
    }
    // 进行主要节点的移动
    context.regular_table = std::move(information.content);
    if (!start_is_transfer) {
        context.regular_table.insert(context.regular_table.begin(), state_transition(0)); // 在表开头添加第一个虚转移节点
        // 由于开头添加了一个虚转移组，将正则表中的除开头外的虚转移节点的索引+1
        for (sizevalue i = 1; i < context.regular_table.size(); ++i) {
            if (context.regular_table[i].is_transfer_transition()) {
                context.regular_table[i] = state_transition(context.regular_table[i].index() + 1);
            }
        }
        // 由于在表开头添加了第一个虚转移节点，所有虚转移组中的索引递增 1
        std::for_each(context.virtual_transitions_table.begin(), context.virtual_transitions_table.end(), [](vector<state_transition>& group) {
            std::for_each(group.begin(), group.end(), [](state_transition& st) {st = state_transition(st.index() + 1); });
        });
        // 且 index_of_heads 和 index_of_tails 的所有元素向后递增 1
        std::for_each(information.index_of_heads.begin(), information.index_of_heads.end(), [](sizevalue& index) { index += 1; });
        std::for_each(information.index_of_tails.begin(), information.index_of_tails.end(), [](sizevalue& index) { index += 1; });
    }
    // 将 index_of_heads 变为转移节点
    for (sizevalue i = 0; i < information.index_of_heads.size(); ++i) {
        if (std::count(context.virtual_transitions_table.front().begin(), context.virtual_transitions_table.front().end(), state_transition(information.index_of_heads[i])) == 0) {
            context.virtual_transitions_table.front().push_back(state_transition(information.index_of_heads[i]));
        }
    }
    // 将尾部节点连接到自动机的结束状态
    if (!context.regular_table.back().is_transfer_transition()) {
        // 如果末尾不是虚转移节点，添加虚转移节点用于连接结束状态
        context.regular_table.push_back(context.virtual_transitions_table.size());
        context.virtual_transitions_table.push_back({});
    }
    vector<sizevalue> index_of_end_transition = { sizevalue_max };
    if (information.exists_escape_transition) {
        // 如果需要存在贯穿路径，将起始节点视为尾部，使在连接时出现贯穿转移路径
        information.index_of_tails.push_back(0);
    }
    connect_predecessors_and_successors(context.regular_table, context.virtual_transitions_table, information.index_of_tails, index_of_end_transition, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    // 输出
    return std::move(context);
}

// 逻辑规范：
// 前置条件：无
// 后置条件：context.regular_table 中的所有虚转移节点都展开为转移节点，且自动机整体的转移路径不变
static void expand_virtual_transition(regular_table_context& context)
{
    // 第一遍遍历，建立映射表
    vector<sizevalue> original_index_to_expanded_index(context.regular_table.size(), 0); // 索引代表 original_index，值代表 expanded_index
    intmax current_offset = 0;
    for (sizevalue i = 0; i < context.regular_table.size(); ++i) {
        // 处理自动机中的虚转移节点
        if (context.regular_table[i].is_transfer_transition() && context.regular_table[i].index() != sizevalue_max) {
            auto& transitions = context.virtual_transitions_table[context.regular_table[i].index()];
            intmax offset_of_this = -1;
            // 如果 transitions 为空，则说明这个虚转移节点不指代任何实际的转移节点，进行直接处理
            if (transitions.empty()) {
                current_offset -= 1;
                continue;
            }
            // 如果虚转移节点修饰的节点的只有到下一个直接相邻节点的转移路径，则跳过处理，采用默认连接的模式。
            auto previous_meaningful_it = context.regular_table.begin() + i;
            while (previous_meaningful_it->is_transfer_transition() && previous_meaningful_it != context.regular_table.begin()) {
                previous_meaningful_it -= 1;
            }
            if (previous_meaningful_it != context.regular_table.begin()) {
                if (previous_meaningful_it - context.regular_table.begin() + 1 + 1 == transitions.front().index() && transitions.size() == 1 && transitions.front().is_transfer_transition()) {
                    offset_of_this -= 1;
                }
            }
            // 计算偏移
            offset_of_this += transitions.size();
            current_offset += offset_of_this;
            continue;
        }
        // 如果是普通节点，根据 current_offset 进行索引的映射
        original_index_to_expanded_index[i] = i + current_offset;
    }

    // 第二遍遍历，展开虚转移节点
    vector<state_transition> expanded_regular_table{};
    for (sizevalue i = 0; i < context.regular_table.size(); ++i) {
        // 如果是虚转移节点，进行展开处理
        if (context.regular_table[i].is_transfer_transition() && context.regular_table[i].index() != sizevalue_max) {
            sizevalue index_of_virtual_transition = context.regular_table[i].index();
            auto& virtual_transitions = context.virtual_transitions_table[index_of_virtual_transition];
            // 如果 virtual_transitions 为空，则说明这个虚转移节点不指代任何实际的转移节点，进行跳过处理
            if (virtual_transitions.empty()) {
                continue;
            }
            // 如果虚转移节点修饰的节点的只有到下一个直接相邻节点的转移路径，则跳过处理，采用默认连接的模式。
            auto previous_meaningful_it = context.regular_table.begin() + i;
            while (previous_meaningful_it->is_transfer_transition() && previous_meaningful_it != context.regular_table.begin()) {
                previous_meaningful_it -= 1;
            }
            if (previous_meaningful_it != context.regular_table.begin()) {
                if (previous_meaningful_it - context.regular_table.begin() + 1 + 1 == virtual_transitions.front().index() && virtual_transitions.size() == 1 && virtual_transitions.front().is_transfer_transition()) {
                    continue;
                }
            }
            // 否则全部正常展开
            expanded_regular_table.insert(expanded_regular_table.end(), virtual_transitions.begin(), virtual_transitions.end());
        }
        // 否则正常添加
        else {
            expanded_regular_table.push_back(context.regular_table[i]);
        }
    }
    context.regular_table = std::move(expanded_regular_table); // 将展开后的结果载入上下文

    // 第三遍遍历，将所有的转移路径映射到新转移路径
    for (sizevalue i = 0; i < context.regular_table.size(); ++i) {
        if (context.regular_table[i].is_transfer_transition() && context.regular_table[i].index() >= original_index_to_expanded_index.size()) {
            context.regular_table[i] = state_transition(sizevalue_max);
            continue; // 不处理指向结束状态的转移路径
        }
        else if (context.regular_table[i].is_transfer_transition()) {
            context.regular_table[i] = state_transition(original_index_to_expanded_index[context.regular_table[i].index()]);
        }
    }
}

static API::expression_information* build_api_expression_information(expression_information information)
{
    API::expression_information* result = new API::expression_information();
    // 初始化 table
    result->pointer_of_table = reinterpret_cast<address>(new state_transition[information.content.size()]());
    std::memcpy(reinterpret_cast<void*>(result->pointer_of_table), information.content.data(), information.content.size() * sizeof(state_transition));
    result->length_of_table = information.content.size();
    // 初始化尾部
    result->pointer_of_index_of_tails = reinterpret_cast<address>(new sizevalue[information.index_of_tails.size()]());
    std::memcpy(reinterpret_cast<void*>(result->pointer_of_index_of_tails), information.index_of_tails.data(), information.index_of_tails.size() * sizeof(sizevalue));
    result->length_of_index_of_tails = information.index_of_tails.size();
    // 初始化头部
    result->pointer_of_index_of_heads = reinterpret_cast<address>(new sizevalue[information.index_of_heads.size()]());
    std::memcpy(reinterpret_cast<void*>(result->pointer_of_index_of_heads), information.index_of_heads.data(), information.index_of_heads.size() * sizeof(sizevalue));
    result->length_of_index_of_heads = information.index_of_heads.size();
    // 初始化虚转移表
    result->pointer_of_virtual_transitions_table = reinterpret_cast<address>(new API::regular_table[information.virtual_transitions_table.size()]());
    result->length_of_virtual_transitions_table = information.virtual_transitions_table.size();
    API::regular_table* virtual_transitions_table = reinterpret_cast<API::regular_table*>(result->pointer_of_virtual_transitions_table);
    for (sizevalue i = 0; i < result->length_of_virtual_transitions_table; ++i) {
        virtual_transitions_table[i].pointer_of_table = reinterpret_cast<address>(new state_transition[information.virtual_transitions_table[i].size()]());
        memcpy(reinterpret_cast<void*>(virtual_transitions_table[i].pointer_of_table), information.virtual_transitions_table[i].data(), information.virtual_transitions_table[i].size() * sizeof(state_transition));
        virtual_transitions_table[i].length_of_table = information.virtual_transitions_table[i].size();
    }
    // 初始化被贯穿标志
    result->exists_escape_transition = information.exists_escape_transition;
    return result;
};

static expression_information build_expression_information(API::expression_information api_information)
{
    expression_information result{};
    result.content = vector<state_transition>(reinterpret_cast<state_transition*>(api_information.pointer_of_table), reinterpret_cast<state_transition*>(api_information.pointer_of_table) + api_information.length_of_table);
    result.index_of_tails = vector<sizevalue>(reinterpret_cast<sizevalue*>(api_information.pointer_of_index_of_tails), reinterpret_cast<sizevalue*>(api_information.pointer_of_index_of_tails) + api_information.length_of_index_of_tails);
    result.index_of_heads = vector<sizevalue>(reinterpret_cast<sizevalue*>(api_information.pointer_of_index_of_heads), reinterpret_cast<sizevalue*>(api_information.pointer_of_index_of_heads) + api_information.length_of_index_of_heads);
    result.virtual_transitions_table.resize(api_information.length_of_virtual_transitions_table);
    for (sizevalue i = 0; i < result.virtual_transitions_table.size(); ++i) {
        API::regular_table* table = reinterpret_cast<API::regular_table*>(api_information.pointer_of_virtual_transitions_table);
        result.virtual_transitions_table[i] = vector<state_transition>(reinterpret_cast<state_transition*>(table[i].pointer_of_table), reinterpret_cast<state_transition*>(table[i].pointer_of_table) + table[i].length_of_table);
    }
    result.exists_escape_transition = api_information.exists_escape_transition;
    return std::move(result);
}

namespace API
{
    API::expression_information* nothing(address pointer_of_expression, sizevalue length_of_expression, sizevalue index_of_operation, sizevalue operation_id, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto information = nothing(::expression_with_operation{str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), index_of_operation, operation_id}, span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        return build_api_expression_information(information);
    }

    API::expression_information* epsilon(address pointer_of_expression, sizevalue length_of_expression, sizevalue index_of_operation, sizevalue operation_id, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto information = epsilon(::expression_with_operation{str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), index_of_operation, operation_id}, span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        return build_api_expression_information(information);
    }

    API::expression_information* center_dot(address pointer_of_expression, sizevalue length_of_expression, sizevalue index_of_operation, sizevalue operation_id, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto information = center_dot(::expression_with_operation{str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), index_of_operation, operation_id}, span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        return build_api_expression_information(information);
    }

    API::expression_information* left_bracket(address pointer_of_expression, sizevalue length_of_expression, sizevalue index_of_operation, sizevalue operation_id, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto information = left_bracket(::expression_with_operation{str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), index_of_operation, operation_id}, span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        return build_api_expression_information(information);
    }

    API::expression_information* right_bracket(address pointer_of_expression, sizevalue length_of_expression, sizevalue index_of_operation, sizevalue operation_id, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto information = nothing(::expression_with_operation{str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), index_of_operation, operation_id}, span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        return build_api_expression_information(information);
    }

    API::expression_information* alternation(address pointer_of_expression, sizevalue length_of_expression, sizevalue index_of_operation, sizevalue operation_id, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto information = alternation(::expression_with_operation{str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), index_of_operation, operation_id}, span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        return build_api_expression_information(information);
    }

    API::expression_information* kleene_star(address pointer_of_expression, sizevalue length_of_expression, sizevalue index_of_operation, sizevalue operation_id, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto information = kleene_star(::expression_with_operation{str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), index_of_operation, operation_id}, span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        return build_api_expression_information(information);
    }
    
    API::regular_table* build_regular_table(address pointer_of_expression, sizevalue length_of_expression, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto table = build_regular_table(str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        API::regular_table* result = new API::regular_table();
        result->pointer_of_table = reinterpret_cast<address>(new state_transition[table.size()]());
        std::memcpy(reinterpret_cast<void*>(result->pointer_of_table), table.data(), table.size() * sizeof(state_transition));
        result->length_of_table = table.size();
        return result;
    }
    
    API::expression_information* build_expression_information(address pointer_of_expression, sizevalue length_of_expression, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto information = build_expression_information(str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        return build_api_expression_information(information);
    }
    
    void release_regular_table(API::regular_table* instance)
    {
        if (reinterpret_cast<state_transition*>(instance->pointer_of_table) != nullptr) {
            delete reinterpret_cast<state_transition*>(instance->pointer_of_table);
            instance->pointer_of_table = 0;
        }
        instance->length_of_table = 0;
    }

    void release_expression_information(API::expression_information* instance)
    {
        if (reinterpret_cast<state_transition*>(instance->pointer_of_table) != nullptr) {
            delete reinterpret_cast<state_transition*>(instance->pointer_of_table);
            instance->pointer_of_table = 0;
        }
        instance->length_of_table = 0;
        if (reinterpret_cast<sizevalue*>(instance->pointer_of_index_of_tails) != nullptr) {
            delete reinterpret_cast<state_transition*>(instance->pointer_of_index_of_tails);
            instance->pointer_of_index_of_tails = 0;
        }
        instance->length_of_index_of_tails = 0;
        if (reinterpret_cast<state_transition*>(instance->pointer_of_index_of_heads) != nullptr) {
            delete reinterpret_cast<state_transition*>(instance->pointer_of_index_of_heads);
            instance->length_of_index_of_tails = 0;
        }
        instance->length_of_index_of_heads = 0;
        regular_table* group = reinterpret_cast<regular_table*>(instance->pointer_of_virtual_transitions_table);
        for (sizevalue i = 0; i < instance->length_of_virtual_transitions_table; ++i) {
            if (reinterpret_cast<state_transition*>(group[i].pointer_of_table) != nullptr) {
                delete reinterpret_cast<state_transition*>(group[i].pointer_of_table);
                group[i].pointer_of_table = 0;
            }
            group[i].length_of_table = 0;
        }
        if (group != nullptr) {
            delete group;
            group = nullptr;
        }
        instance->length_of_virtual_transitions_table = 0;
    }
}