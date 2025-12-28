#include <numerical-cell>
#include <bit-span>
#include <runtime-exception>

using std::vector;
using std::span;
using std::runtime_error;
using std::memset;
using std::memcpy;
using std::min;
using std::to_string;
using std::weak_ordering;

numerical_cell::numerical_cell(const vector<natmax>& upper_bound) noexcept
{
	span<natmax> upper_bound_span(const_cast<natmax*>(upper_bound.data()), find_if(upper_bound.rbegin(), upper_bound.rend(), [](natmax x) { return x != 0; }).base() - upper_bound.begin());
	content.resize(upper_bound_span.size() * 2, 0);
	memcpy(content.data() + upper_bound_span.size(), upper_bound_span.data(), upper_bound_span.size() * sizeof(natmax));
}

numerical_cell::numerical_cell(vector<natmax>&& upper_bound) noexcept
{
	span<natmax> upper_bound_span(const_cast<natmax*>(upper_bound.data()), find_if(upper_bound.rbegin(), upper_bound.rend(), [](natmax x) { return x != 0; }).base() - upper_bound.begin());
	content.resize(upper_bound_span.size() * 2, 0);
	memcpy(content.data() + upper_bound_span.size(), upper_bound_span.data(), upper_bound_span.size() * sizeof(natmax));
}

span<natmax> numerical_cell::value() const noexcept
{
	if (content.empty()) {
		return span<natmax>{};
	}
	size_t half_size = content.size() / 2;
	return span<natmax>(const_cast<natmax*>(content.data()), half_size);
}

span<natmax> numerical_cell::number_of_states() const noexcept
{
	if (content.empty()) {
		return span<natmax>{};
	}
	size_t half_size = content.size() / 2;
	return span<natmax>(const_cast<natmax*>(content.data() + half_size), half_size);
}

static vector<natmax> mod_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept;
static vector<natmax> div_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept;
template <typename T> bool bit_is_less(T&& l, T&& r) noexcept;
static void decrease_between_bit_spans(bit_span& minuend, const bit_span& subtrahend) noexcept;
template <typename T> bool is_equal(T&& l, T&& r) noexcept;
template <typename T> bool is_less(T&& l, T&& r) noexcept;
template <typename T> bool is_less_or_equal(T&& l, T&& r) noexcept;
template <typename T> bool is_greater_or_equal(T&& l, T&& r) noexcept;

using nathalf = nat32;
static natmax NUMBER_OF_NATHALF_STATE = 4294967296;
static void propagate_carry_in_increase(span<natmax>&& parts, nat8& carry) noexcept;
static void limit_value_after_increase(span<natmax>&& number_of_states, span<natmax>&& value) noexcept;
static void propagate_borrow_in_decrease(span<natmax>&& parts, nat8& borrow) noexcept;
static void limit_value_after_decrease(span<natmax>&& number_of_states, span<natmax>&& value) noexcept;
static void propagate_carry_in_multiply(span<nathalf>&& parts, nathalf& carry) noexcept;

template <typename T>
byte_array generate_information_of_linear_table(T&& linear_table)
{
	byte_array information = "{ ";
	for (auto& element : linear_table) {
		information += to_string(element) + ", ";
	}
	information.erase(information.size() - 2);
	information += " }";
	return std::move(information);
}

bool numerical_cell::bad() const noexcept
{
	auto number_of_states = this->number_of_states();
	auto value = this->value();
	if (number_of_states.size() < value.size()) {
		return true;
	}
	else if (number_of_states.size() > value.size()) {
		return false;
	}
	auto iterator_of_units = number_of_states.rbegin();
	for (auto iterator_of_value = value.rbegin(); iterator_of_value != value.rend(); ++iterator_of_value) {
		if (*iterator_of_units < *iterator_of_value) {
			return true;
		}
		else if (*iterator_of_units > *iterator_of_value) {
			return false;
		}
		++iterator_of_units;
	}
	return true;
}

numerical_cell::numerical_cell(const numerical_cell& right) noexcept
{
	auto right_number_of_states = right.number_of_states();
	auto right_value = right.value();
	content.resize(right_number_of_states.size() * 2, 0);
	memcpy(content.data() + right_number_of_states.size(), right_number_of_states.data(), right_number_of_states.size() * sizeof(natmax));
	memcpy(content.data(), right_value.data(), right_number_of_states.size() * sizeof(natmax));
}

numerical_cell::numerical_cell(numerical_cell&& right) noexcept
{
	auto right_number_of_states = right.number_of_states();
	auto right_value = right.value();
	content.resize(right_number_of_states.size() * 2, 0);
	memcpy(content.data() + right_number_of_states.size(), right_number_of_states.data(), right_number_of_states.size() * sizeof(natmax));
	memcpy(content.data(), right_value.data(), right_number_of_states.size() * sizeof(natmax));
}

void numerical_cell::operator=(span<natmax> value) noexcept
{
	runtime_assert(not value.empty(), "数胞的=函数的前置条件不被满足");

	auto current_number_of_states = this->number_of_states();
	auto current_value = this->value();
	value = value.subspan(0, find_if(value.rbegin(), --value.rend(), [](natmax b) { return b != 0; }).base() - value.begin());
	if (current_number_of_states.empty()) {
		return;
	}
	else if (is_less_or_equal(span<natmax>(current_number_of_states), span<natmax>(value))) {
		vector<natmax> copy_value(value.begin(), value.end());
		vector<natmax> remainder{};
		try {
			remainder = mod_value_by_value(span<natmax>(const_cast<natmax*>(copy_value.data()), copy_value.size()), current_number_of_states);
		}
		catch (runtime_error& e) {
			link_runtime_error(e, "在数胞的赋值函数中，自身状态数为" + generate_information_of_linear_table(current_number_of_states) + "，赋予的值为" + generate_information_of_linear_table(value));
		}
		memset(current_value.data(), 0, current_value.size());
		memcpy(current_value.data(), remainder.data(), remainder.size() * sizeof(natmax));
	}
	else {
		memset(current_value.data(), 0, current_value.size());
		memcpy(current_value.data(), value.data(), value.size() * sizeof(natmax));
	}
}

void numerical_cell::operator=(const numerical_cell& right) noexcept
{
	content = right.content;
}

void numerical_cell::operator=(numerical_cell&& right) noexcept
{
	content = right.content;
}

// 逻辑规范：
// 前置条件 P: dividend 和 divisor 皆有效 (作为无符号数解释)，且 divisor != 0
// 后置条件 Q: 返回 dividend mod divisor (余数)
// 注意: dividend 在调用此函数之后可能会被改变
static vector<natmax> mod_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept
{
	runtime_assert(dividend.size() > 0 and divisor.size() > 0, "在 mod_value_by_value 中被除数与除数至少有一个是无效的");
	runtime_assert(not all_of(divisor.begin(), divisor.end(), [](const natmax value) { return value == 0; }), "在 mod_value_by_value 中发现除数为0");
	// 将输入转换为位跨度
	bit_span dividend_bit_span = bit_span(reinterpret_cast<::byte*>(dividend.data()), 0, dividend.size() * sizeof(natmax) * WORD_SIZE);
	bit_span divisor_bit_span = bit_span(reinterpret_cast<::byte*>(divisor.data()), 0, divisor.size() * sizeof(natmax) * WORD_SIZE);
	dividend_bit_span = dividend_bit_span.subspan(0, find_if(dividend_bit_span.rbegin(), --dividend_bit_span.rend(), [](::byte b) { return b != 0; }).base() - dividend_bit_span.begin());
	divisor_bit_span = divisor_bit_span.subspan(0, find_if(divisor_bit_span.rbegin(), --divisor_bit_span.rend(), [](::byte b) { return b != 0; }).base() - divisor_bit_span.begin());

	// 如果被除数位数小于除数位数，直接返回被除数
	if (dividend_bit_span.size() < divisor_bit_span.size()) {
		return vector<natmax>(dividend.begin(), dividend.end());
	}

	// 主循环：长除法求余数
	// 循环不变式: 
	//   dividend_bit_span 的当前值 = 原始被除数的高位部分
	//   且 0 ≤ 当前余数 < divisor
	for (sizevalue i = 0; i < dividend_bit_span.size(); ++i) {
		// 取当前子跨度：从最高位到当前位
		sizevalue start_index = dividend_bit_span.size() - 1 - i;
		sizevalue length = i + 1;
		auto sub_dividend = dividend_bit_span.subspan(start_index, length);
		sub_dividend = sub_dividend.subspan(0, find_if(sub_dividend.rbegin(), --sub_dividend.rend(), [](::byte b) { return b != 0; }).base() - sub_dividend.begin());

		// 循环不变式: 
		//   sub_dividend 表示当前被处理的位段
		//   该位段的值 >= divisor 或需要继续扩展

		// 比较当前子跨度与除数
		if (!is_less(bit_span(sub_dividend), bit_span(divisor_bit_span))) { // 即 sub_dividend >= divisor
			// 执行减法：sub_dividend = sub_dividend - divisor
			decrease_between_bit_spans(sub_dividend, divisor_bit_span);
		}
	}

	// 后置条件: 余数在 dividend 的低位部分
	// 计算余数的位数 (不超过除数的位数)
	vector<natmax> remainder(dividend.size());

	// 复制余数部分 (dividend 的低位)
	memcpy(remainder.data(), dividend.data(), remainder.size() * sizeof(natmax));

	// 删除结果中无用的0
	remainder.erase(find_if(remainder.rbegin(), --remainder.rend(), [](natmax value) { return value != 0; }).base(), remainder.end());
	return std::move(remainder);
}

// 逻辑规范：
// 前置条件 P: dividend 和 divisor 皆有效 (作为无符号数解释)，且 divisor != 0
// 后置条件 Q: 返回 dividend / divisor (整除)
// 注意: dividend 在调用此函数之后可能会被改变
static vector<natmax> div_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept
{
	runtime_assert(dividend.size() > 0 and divisor.size() > 0, "在 mod_value_by_value 中被除数与除数至少有一个是无效的");
	runtime_assert(not all_of(divisor.begin(), divisor.end(), [](const natmax value) { return value == 0; }), "在 mod_value_by_value 中发现除数为0");
	// 将被除数和除数转换为比特数组
	bit_span dividend_bit_span = bit_span(reinterpret_cast<::byte*>(dividend.data()), 0, dividend.size() * sizeof(natmax) * WORD_SIZE);
	bit_span divisor_bit_span = bit_span(reinterpret_cast<::byte*>(divisor.data()), 0, divisor.size() * sizeof(natmax) * WORD_SIZE);
	dividend_bit_span = dividend_bit_span.subspan(0, find_if(dividend_bit_span.rbegin(), dividend_bit_span.rend(), [](::byte b) { return b != 0; }).base() - dividend_bit_span.begin());
	divisor_bit_span = divisor_bit_span.subspan(0, find_if(divisor_bit_span.rbegin(), divisor_bit_span.rend(), [](::byte b) { return b != 0; }).base() - divisor_bit_span.begin());

	// 如果在二进制形式下被除数的长度小于除数的长度，则说明被除数一定小于除数，此时相除必定为0
	if (dividend_bit_span.size() < divisor_bit_span.size()) {
		return vector<natmax>(1, 0);
	}

	vector<natmax> result(dividend.size()); // 存储相除的结果的比特数组
	bit_span result_bitarray = bit_span(reinterpret_cast<::byte*>(result.data()), 0, result.size() * sizeof(natmax) * WORD_SIZE);
	auto iterator_of_result = result_bitarray.rbegin();
	// 主循环：长除法求商
	for (sizevalue i = 0; i < dividend_bit_span.size(); ++i) {
		// 取当前子跨度：从最高位到当前位
		sizevalue start_index = dividend_bit_span.size() - 1 - i;
		sizevalue length = i + 1;
		auto sub_dividend = dividend_bit_span.subspan(start_index, length);
		sub_dividend = sub_dividend.subspan(0, find_if(sub_dividend.rbegin(), sub_dividend.rend(), [](::byte b) { return b != 0; }).base() - sub_dividend.begin());
		// 如果目前循环取到的被除数部分小于除数，则不能进行相减计算，即不能在此位相除
		if (bit_is_less(sub_dividend, divisor_bit_span)) {
			*iterator_of_result = false;
			++iterator_of_result;
			continue;
		}
		// 如果可以，则将被除数的选择部分与除数对齐相减，为之后的计算奠定基础，并将此位的比特设置为true，说明可以在此位相除
		decrease_between_bit_spans(sub_dividend, divisor_bit_span);
		*iterator_of_result = true;
		++iterator_of_result;
	}
	// 删除结果中无用的0
	result.erase(find_if(result.rbegin(), --result.rend(), [](natmax value) { return value != 0; }).base(), result.end());
	return std::move(result);
}

// 逻辑规范：
// 前置条件 P: l,r 皆为有效的非空线性表 (两者均作为自然数解释, l.size() > 0, r.size() > 0)，且l,r均不存在高位无效0 (l.size() > 1 => l.back() != 0, r.size() > 1 => r.back() != 0)
// 后置条件 Q: 返回 l < r
template <typename T>
bool bit_is_less(T&& l, T&& r) noexcept
{
	// 前置条件: l.size() > 0, r.size() > 0, l.back() != 0, r.back() != 0
	if (l.size() < r.size()) {
		return true;
	}
	// l.size() < r.size() => 返回 true 或者 l.size() >= r.size()
	if (l.size() > r.size()) {
		return false;
	}
	// l.size() < r.size() => 返回 true 或者 l.size() > r.size() => 返回 false 或者 l.size() = r.size()
	// 主循环：满足 l.size() = r.size()
	// 循环不变式：
	//   设 L = l.size() = r.size()
	//   对于当前索引 i (0 <= i < L):
	//     High_{L-i-1}(l) = High_{L-i-1}(r) 并且 (i = sizevalue_max 或者 i < L)
	//   其中 High_k(X) 表示 X 的高 k (k >= 0) 位组成的自然数 (当 k=0 时定义为空，恒成立)
	for (sizevalue i = l.size() - 1; i < l.size(); --i) {
		if (l[i] < r[i]) {
			return true;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] < r[i] => l < r => 返回 true) 或者 (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] >= r[i])
		if (l[i] > r[i]) {
			return false;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] > r[i] => l > r => 返回 false) 或者 High_{L-i}(l) = High_{L-i}(r)
	}
	// l = r => 返回 false
	return false;
}

static vector<natmax> bit_span_to_number(bit_span bs)
{
	// 计算需要的 natmax 数量
	const size_t num_bits = bs.size();
	const size_t num_words = (num_bits + 63) / 64;
	vector<natmax> result(num_words, 0);

	if (result.empty()) {
		return result;
	}

	// 获取位迭代器
	auto bit_iter = bs.begin();
	// 逐位复制
	for (size_t i = 0; i < num_bits; ++i, ++bit_iter) {
		const size_t word_idx = i / 64;
		const size_t bit_idx = i % 64;

		if (*bit_iter) {
			result[word_idx] |= (static_cast<natmax>(1) << bit_idx);
		}
	}
	return result;
}

// 逻辑规范：
// 前置条件 P: minuend >= subtrahend (作为无符号整数解释)，且两者均为有效位跨度
// 后置条件 Q: minuend := minuend - subtrahend
static void decrease_between_bit_spans(bit_span& minuend, const bit_span& subtrahend) noexcept
{
	// 前置条件: minuend >= subtrahend
	sizevalue culculate_length = min(minuend.size(), subtrahend.size());
	// culculate_length := min(minuend.size(), subtrahend.size())
	bool borrow = false;

	vector<natmax> temp = bit_span_to_number(minuend);
	bit_span original_minuend(reinterpret_cast<::byte*>(temp.data()), 0, temp.size() * sizeof(natmax) * WORD_SIZE); // 原来的 minuend，用于断言
	// 主循环：处理公共位段 (0 到 culculate_length-1)
	// 循环不变式: 
	//   设 A = old(minuend), B = subtrahend, L = min(size)
	//   对于当前处理的位索引 i (0 ≤ i ≤ culculate_length):
	//     Low_i(minuend) = Low_i(A) - Low_i(B) - 2^i * borrow
	//   其中 Low_k(X) = X mod 2^k，表示 X 的低 k 位组成的自然数
	for (sizevalue i = 0; i < culculate_length; ++i) {
		if (minuend[i] == true) {
			if (subtrahend[i] == true) {
				minuend[i] = borrow ? true : false;
			}
			else {
				minuend[i] = borrow ? false : true;
				borrow = false;
			}
			// minuend[i] := (1 - subtrahend[i] - borrow) mod 2
		}
		else {
			if (subtrahend[i] == true) {
				minuend[i] = borrow ? false : true;
				borrow = true;
			}
			else {
				minuend[i] = borrow ? true : false;
			}
			// minuend[i] := (0 - subtrahend[i] - borrow) mod 2
		}
		// minuend[i] := (minuend[i] - subtrahend[i] - borrow) mod 2
		// borrow := (minuend[i] - subtrahend[i] - borrow) // 2
	}

	// 处理借位传播 (当 minuend 有更高位时)
	// 不变式: 
	//   minuend 的当前值 + 2^{culculate_length} * borrow = 
	//      old(minuend) - subtrahend (仅低 culculate_length 位部分)
	if (borrow) {
		sizevalue offset = 0;
		// 借位传播：从 culculate_length 开始向高位传播
		// 终止条件：当遇到一个位翻转后为 false (即原为 true)
		do {
			// 翻转当前高位位 (借位传播)
			minuend[culculate_length + offset] = not minuend[culculate_length + offset];
			++offset;
		} while (minuend[culculate_length + offset - 1] == true);
	}
	// 后置条件: minuend = old(minuend) - subtrahend
}

// 逻辑规范：
// 前置条件 P: l,r 皆为有效的非空线性表 (两者均作为自然数解释, l.size() > 0, r.size() > 0)，且l,r均不存在高位无效0 (l.size() > 1 => l.back() != 0, r.size() > 1 => r.back() != 0)
// 后置条件 Q: 返回 l = r
template <typename T>
bool is_equal(T&& l, T&& r) noexcept
{
	// 前置条件: l.size() > 0, r.size() > 0, l.back() != 0, r.back() != 0
	runtime_assert(l.size() > 0 and r.size() > 0 and (l.size() > 1 ? l.back() != 0 : true) and (r.size() > 1 ? r.back() != 0 : true), "is_equal 的前置条件不被满足");
	if (l.size() < r.size()) {
		return false;
	}
	// l.size() < r.size() => 返回 false 或者 l.size() >= r.size()
	if (l.size() > r.size()) {
		return false;
	}
	// l.size() < r.size() => 返回 false 或者 l.size() > r.size() => 返回 false 或者 l.size() = r.size()
	// 主循环：满足 l.size() = r.size()
	// 循环不变式：
	//   设 L = l.size() = r.size()
	//   对于当前索引 i (0 <= i < L):
	//     High_{L-i-1}(l) = High_{L-i-1}(r) 并且 (i = sizevalue_max 或者 i < L)
	//   其中 High_k(X) 表示 X 的高 k (k >= 0) 位组成的自然数 (当 k=0 时定义为空，恒成立)
	sizevalue L = l.size();
	for (sizevalue i = l.size() - 1; i < l.size(); --i) {
		T high_l(l.begin() + i + 1, l.end());
		T high_r(r.begin() + i + 1, r.end());
		for (sizevalue j = 0; j < L - i - 1; ++j) {
			runtime_assert(high_l[j] == high_r[j] and (i == sizevalue_max or i < L), "is_equal 的循环不变式不被满足");
		}
		if (l[i] < r[i]) {
			return false;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] < r[i] => l < r => 返回 false) 或者 (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] >= r[i])
		if (l[i] > r[i]) {
			return false;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] > r[i] => l > r => 返回 false) 或者 High_{L-i}(l) = High_{L-i}(r)
	}
	for (sizevalue j = 0; j < L; ++j) {
		runtime_assert(l[j] == r[j], "is_equal 的循环不变式不被满足");
	}
	// l = r => 返回 true
	return true;
}

// 逻辑规范：
// 前置条件 P: l,r 皆为有效的非空线性表 (两者均作为自然数解释, l.size() > 0, r.size() > 0)，且l,r均不存在高位无效0 (l.size() > 1 => l.back() != 0, r.size() > 1 => r.back() != 0)
// 后置条件 Q: 返回 l < r
template <typename T>
bool is_less(T&& l, T&& r) noexcept
{
	// 前置条件: l.size() > 0, r.size() > 0, l.back() != 0, r.back() != 0
	runtime_assert(l.size() > 0 and r.size() > 0 and (l.size() > 1 ? l.back() != 0 : true) and (r.size() > 1 ? r.back() != 0 : true), "is_less 的前置条件不被满足");
	if (l.size() < r.size()) {
		return true;
	}
	// l.size() < r.size() => 返回 true 或者 l.size() >= r.size()
	if (l.size() > r.size()) {
		return false;
	}
	// l.size() < r.size() => 返回 true 或者 l.size() > r.size() => 返回 false 或者 l.size() = r.size()
	// 主循环：满足 l.size() = r.size()
	// 循环不变式：
	//   设 L = l.size() = r.size()
	//   对于当前索引 i (0 <= i < L):
	//     High_{L-i-1}(l) = High_{L-i-1}(r) 并且 (i = sizevalue_max 或者 i < L)
	//   其中 High_k(X) 表示 X 的高 k (k >= 0) 位组成的自然数 (当 k=0 时定义为空，恒成立)
	sizevalue L = l.size();
	for (sizevalue i = l.size() - 1; i < l.size(); --i) {
		T high_l(l.begin() + i + 1, l.end());
		T high_r(r.begin() + i + 1, r.end());
		for (sizevalue j = 0; j < L - i - 1; ++j) {
			runtime_assert(high_l[j] == high_r[j] and (i == sizevalue_max or i < L), "is_less 的循环不变式不被满足");
		}
		if (l[i] < r[i]) {
			return true;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] < r[i] => l < r => 返回 true) 或者 (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] >= r[i])
		if (l[i] > r[i]) {
			return false;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] > r[i] => l > r => 返回 false) 或者 High_{L-i}(l) = High_{L-i}(r)
	}
	for (sizevalue j = 0; j < L; ++j) {
		runtime_assert(l[j] == r[j], "is_less 的循环不变式不被满足");
	}
	// l = r => 返回 false
	return false;
}

// 逻辑规范：
// 前置条件 P: l,r 皆为有效的非空线性表 (两者均作为自然数解释, l.size() > 0, r.size() > 0)，且l,r均不存在高位无效0 (l.size() > 1 => l.back() != 0, r.size() > 1 => r.back() != 0)
// 后置条件 Q: 返回 l <= r
template <typename T>
bool is_less_or_equal(T&& l, T&& r) noexcept
{
	// 前置条件: l.size() > 0, r.size() > 0, l.back() != 0, r.back() != 0
	runtime_assert(l.size() > 0 and r.size() > 0 and (l.size() > 1 ? l.back() != 0 : true) and (r.size() > 1 ? r.back() != 0 : true), "is_less_or_equal 的前置条件不被满足");
	if (l.size() < r.size()) {
		return true;
	}
	// l.size() < r.size() => 返回 true 或者 l.size() >= r.size()
	if (l.size() > r.size()) {
		return false;
	}
	// l.size() < r.size() => 返回 true 或者 l.size() > r.size() => 返回 false 或者 l.size() = r.size()
	// 主循环：满足 l.size() = r.size()
	// 循环不变式：
	//   设 L = l.size() = r.size()
	//   对于当前索引 i (0 <= i < L):
	//     High_{L-i-1}(l) = High_{L-i-1}(r) 并且 (i = sizevalue_max 或者 i < L)
	//   其中 High_k(X) 表示 X 的高 k (k >= 0) 位组成的自然数 (当 k=0 时定义为空，恒成立)
	sizevalue L = l.size();
	for (sizevalue i = l.size() - 1; i < l.size(); --i) {
		T high_l(l.begin() + i + 1, l.end());
		T high_r(r.begin() + i + 1, r.end());
		for (sizevalue j = 0; j < L - i - 1; ++j) {
			runtime_assert(high_l[j] == high_r[j] and (i == sizevalue_max or i < L), "is_less_or_equal 的循环不变式不被满足");
		}
		if (l[i] < r[i]) {
			return true;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] < r[i] => l < r => 返回 true) 或者 (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] >= r[i])
		if (l[i] > r[i]) {
			return false;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] > r[i] => l > r => 返回 false) 或者 High_{L-i}(l) = High_{L-i}(r)
	}
	for (sizevalue j = 0; j < L; ++j) {
		runtime_assert(l[j] == r[j], "is_less_or_equal 的循环不变式不被满足");
	}
	// l = r => 返回 true
	return true;
}

// 逻辑规范：
// 前置条件 P: l,r 皆为有效的非空线性表 (两者均作为自然数解释, l.size() > 0, r.size() > 0)，且l,r均不存在高位无效0 (l.size() > 1 => l.back() != 0, r.size() > 1 => r.back() != 0)
// 后置条件 Q: 返回 l >= r
template <typename T>
bool is_greater_or_equal(T&& l, T&& r) noexcept
{
	// 前置条件: l.size() > 0, r.size() > 0, l.back() != 0, r.back() != 0
	runtime_assert(l.size() > 0 and r.size() > 0 and (l.size() > 1 ? l.back() != 0 : true) and (r.size() > 1 ? r.back() != 0 : true), "is_less 的前置条件不被满足");
	if (l.size() < r.size()) {
		return false;
	}
	// l.size() < r.size() => 返回 false 或者 l.size() >= r.size()
	if (l.size() > r.size()) {
		return true;
	}
	// l.size() < r.size() => 返回 false 或者 l.size() > r.size() => 返回 true 或者 l.size() = r.size()
	// 主循环：满足 l.size() = r.size()
	// 循环不变式：
	//   设 L = l.size() = r.size()
	//   对于当前索引 i (0 <= i < L):
	//     High_{L-i-1}(l) = High_{L-i-1}(r) 并且 (i = sizevalue_max 或者 i < L)
	//   其中 High_k(X) 表示 X 的高 k (k >= 0) 位组成的自然数 (当 k=0 时定义为空，恒成立)
	sizevalue L = l.size();
	for (sizevalue i = l.size() - 1; i < l.size(); --i) {
		T high_l(l.begin() + i + 1, l.end());
		T high_r(r.begin() + i + 1, r.end());
		for (sizevalue j = 0; j < L - i - 1; ++j) {
			runtime_assert(high_l[j] == high_r[j] and (i == sizevalue_max or i < L), "is_greater_or_equal 的循环不变式不被满足");
		}
		if (l[i] < r[i]) {
			return false;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] < r[i] => l < r => 返回 false) 或者 (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] >= r[i])
		if (l[i] > r[i]) {
			return true;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] > r[i] => l > r => 返回 true) 或者 High_{L-i}(l) = High_{L-i}(r)
	}
	for (sizevalue j = 0; j < L; ++j) {
		runtime_assert(l[j] == r[j], "is_greater_or_equal 的循环不变式不被满足");
	}
	// l = r => 返回 true
	return true;
}

// 在运行 += 函数时，当 right 的值大于等于自身的状态数时，应调用此函数进行后续处理
// 逻辑规范：
// 前置条件 P: left, right 皆为有效的数胞 (not left.content.empty() and not right.content.empty())
// 后置条件 Q: left <- left + right
void numerical_cell::limit_right_value_then_increase(numerical_cell& left, const numerical_cell& right) noexcept
{
	// 前置条件: not left.content.empty() and not right.content.empty()
	runtime_assert(not left.content.empty() and not right.content.empty(), "limit_right_value_then_increase 的前置条件不被满足");
	vector<natmax> copy_right_value(right.value().begin(), right.value().end());
	// copy_right_value = right.value()
	vector<natmax> remainder = mod_value_by_value(span<natmax>(copy_right_value.data(), copy_right_value.size()), left.number_of_states());
	// remainder = copy_right_value mod left.number_of_states() = right.value() mod left.number_of_states()
	numerical_cell limited_right(right.number_of_states(), span<natmax>(remainder.data(), remainder.size()));
	// limited_right = numerical_cell(right.number_of_states(), remainder)
	left += limited_right;
	// 后置条件: left <- left + limited_right = left + right
}

// 在运行 += 函数时，当 right 的长度短于自身时，应调用此函数进行进位的传播
// 逻辑规范：
// 前置条件 P: parts 为有效的数胞的局部 (not parts.empty()) 并且 (carry = 0 或者 carry = 1)
// 后置条件 Q: 设 B 为 max(natmax) + 1, parts 以 natmax 为单位的数字向上对齐的结果为 U (U = (max(natmax) + 1)^{parts.size()})
//   (parts <- parts + carry, carry <- 0) 或者 (parts <- parts + carry - U, carry <- 1)
static void propagate_carry_in_increase(span<natmax>&& parts, nat8& carry) noexcept
{
	// 前置条件: not parts.empty()
	runtime_assert(not parts.empty() and (carry == 0 or carry == 1), "propagate_carry_in_increase 的前置条件不被满足");
	if (carry == 0) {
		return;
	}
	// 主循环：满足 carry = 1
	// 循环不变式：
	//   ∑_{k=0}^{i-1}(parts[k] * B^k) = ∑_{k=0}^{i-1}(parts_{old}[k] * B^k) + carry_{old} - carry_{current} * B^i
	for (sizevalue i = 0; i < parts.size(); ++i) {
		parts[i] += carry;
		if (parts[i] != 0) {
			carry = 0;
			break;
		}
	}
	// 后置条件: (parts <- parts + carry, carry <- 0) 或者 (parts <- parts + carry - U, carry <- 1)
}

// 在调用 += 函数后，当产生进位(carry == 1)或没有产生进位，但是自身的值溢出(产生进位时一定不会溢出)时，应调用此函数
// 逻辑规范：
// 前置条件 P: number_of_states, value 皆有效 (not number_of_states.empty() and not value.empty())，且满足 number_of_states.size() = value.size()
// 后置条件 Q: 设 number_of_states 以 natmax 为单位的数字向上对齐的结果为 U (U = (max(natmax) + 1)^{number_of_states.size()})
//   value <- value - number_of_states (当value >= number_of_states时)
//   value <- value + (U - number_of_states) (当value < number_of_states时)
static void limit_value_after_increase(span<natmax>&& number_of_states, span<natmax>&& value) noexcept
{
	// 前置条件: not number_of_states.empty() and not value.empty()
	runtime_assert(not number_of_states.empty() and not value.empty() and number_of_states.size() == value.size(), "limit_value_after_increase 的前置条件不被满足");
	// 当 number_of_states 的大小为1时，说明 value 的大小理应也为1，此时只需一次计算即可
	if (number_of_states.size() == 1) {
		value.front() -= (number_of_states.front());
		return;
	}
	// 如果value >= number_of_states: value <- value - number_of_states，返回
	// 如果value < number_of_states: value <- value - number_of_states + U (因为value - number_of_states < 0) = value + (U - number_of_states), 返回
	
	// 主循环：
	// 循环不变式：
	//   设 i = it - value.begin(), B 为 max(natmax) + 1
	//   value_{new} = value_{old} - Low_{i}(number_of_states) + borrow * B^i 并且 i <= value.size()
	//   其中 Low_k(X) 表示 X 的低 k 位组成的自然数
	auto iterator_of_right = number_of_states.begin();
	nat8 borrow = 0; // 借位
	for (auto it = value.begin(); it != value.end(); ++it) {
		sizevalue i = it - value.begin();

		natmax buffer = *it; // 临时存储减法前的值，稍后用于检查此次减法是否产生借位
		// buffer = value_i
		*it = *it - *iterator_of_right - borrow;
		// value_i <- value_i - number_of_states_i - borrow (当value_i >= number_of_states_i + borrow时)
		// value_i <- value_i + B - number_of_states_i - borrow (当value_i < number_of_states_i + borrow时)
		nat8 last_borrow = borrow;
		borrow = 0;
		// 检查此次减法是否产生借位
		if (*it > buffer or (last_borrow == 1 and *it == buffer)) {
			borrow = 1; // 使下次减法额外减1（若还有下次减法）
		}
		// borrow <- 0 (当不产生借位时)
		// borrow <- 1 (当产生借位时)
		++iterator_of_right;
	}
	// 后置条件: value <- value - number_of_states (当value >= number_of_states时) 或者 value <- value + (U - number_of_states) (当value < number_of_states时)
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())
// 后置条件 Q: *this <- *this + right
void numerical_cell::operator+=(const numerical_cell& right) noexcept
{
	// 前置条件: not this->content.empty() and not right.content.empty()
	runtime_assert(not this->content.empty() and not right.content.empty(), "数胞的+=函数的前置条件不被满足");
	span<natmax> current_value = this->value();
	span<natmax> right_value = right.value();
	right_value = right_value.subspan(0, find_if(right_value.rbegin(), --right_value.rend(), [](const natmax v) { return v != 0; }).base() - right_value.begin());
	// 当 right 的值大于等于自身的状态数时，需要将 right 的值限制在自身的状态数中，才能正确相加
	if (is_less_or_equal(this->number_of_states(), span<natmax>(right_value))) {
		limit_right_value_then_increase(*this, right);
		return;
	}
	// 如果 this->number_of_states() <= right_value，则 *this <- *this + right，返回

	// 主循环：满足 this->number_of_states() > right_value
	// 循环不变式：
	//   设 i = it - current_value.begin(), B 为 max(natmax) + 1
	//   *this_{new} = *this_{old} + Low_{i}(right_value) - carry * B^i 并且 i <= current_value.size()
	//   其中 Low_k(X) 表示 X 的低 k 位组成的自然数
	auto iterator_of_right = right_value.begin();
	nat8 carry = 0; // 进位
	for (auto it = current_value.begin(); it != current_value.end(); ++it) {
		sizevalue i = it - current_value.begin();

		// 如果 right 的迭代器结束了，将可能为1的进位加到自身迭代器的值上，退出循环
		if (iterator_of_right == right_value.end()) {
			propagate_carry_in_increase(span<natmax>(current_value.data() + (it - current_value.begin()), current_value.size() - (it - current_value.begin())), carry);
			break;
		}
		natmax buffer = *it; // 临时存储加法前的值，稍后用于检查此次加法是否产生进位
		// buffer = current_value_i
		*it = *it + *iterator_of_right + carry;
		// current_value_i <- (current_value_i + right_value_i + carry) mod B
		nat8 last_carry = carry;
		carry = 0;
		// 检查此次加法是否产生进位
		if (*it < buffer or (last_carry == 1 and *it == buffer)) {
			carry = 1; // 使下次加法额外加1 (若还有下次加法)
		}
		// carry <- 0 (当不产生进位时)
		// carry <- 1 (当产生进位时)
		++iterator_of_right;
	}
	// 计算完成后有两种情况
	// 1. 最后一步产生进位(carry == 1)或没有产生进位，但是自身的值溢出(产生进位时一定不会溢出)，此时需要将自身值减去自身的状态数，方能得到正确结果
	// 2. 没有产生进位，自身的值也没有溢出，此时不需要进行处理
	if (carry == 1 or bad()) {
		limit_value_after_increase(this->number_of_states(), this->value());
	}
	// 后置条件: *this <- *this + right
}

// 在运行 -= 函数时，当 right 的值大于自身的状态数时，应调用此函数进行后续处理
// 逻辑规范：
// 前置条件 P: left, right 皆为有效的数胞 (not left.content.empty() and not right.content.empty())
// 后置条件 Q: left <- left - right
void numerical_cell::limit_right_value_then_decrease(numerical_cell& left, const numerical_cell& right) const noexcept
{
	// 前置条件: not left.content.empty() and not right.content.empty()
	runtime_assert(not left.content.empty() and not right.content.empty(), "limit_right_value_then_decrease 的前置条件不被满足");
	vector<natmax> copy_right_value(right.value().begin(), right.value().end());
	// copy_right_value = right.value()
	vector<natmax> remainder = mod_value_by_value(span<natmax>(copy_right_value.data(), copy_right_value.size()), left.number_of_states());
	// remainder = copy_right_value mod left.number_of_states() = right.value() mod left.number_of_states()
	numerical_cell limited_right(right.number_of_states(), span<natmax>(remainder.data(), remainder.size()));
	// limited_right = numerical_cell(right.number_of_states(), remainder)
	left -= limited_right;
	// 后置条件: left <- left - limited_right = left - right
}

// 在运行 -= 函数时，当 right 的长度短于自身时，应调用此函数进行借位的传播
// 逻辑规范：
// 前置条件 P: parts 为有效的数胞的局部 (not parts.empty()) 并且 (borrow = 0 或者 borrow = 1)
// 后置条件 Q: 设 B 为 max(natmax) + 1, parts 以 natmax 为单位的数字向上对齐的结果为 U (U = (max(natmax) + 1)^{parts.size()})
//   (parts <- parts - borrow, borrow <- 0) 或者 (parts <- parts - borrow + U, borrow <- 1)
static void propagate_borrow_in_decrease(span<natmax>&& parts, nat8& borrow) noexcept
{
	// 前置条件: not parts.empty()
	runtime_assert(not parts.empty() and (borrow == 1 or borrow == 1), "propagate_borrow_in_decrease 的前置条件不被满足");
	if (borrow == 0) {
		return;
	}
	// 主循环：满足 borrow = 1
	// 循环不变式：
	//   ∑_{k=0}^{i-1}(parts[k] * B^k) = ∑_{k=0}^{i-1}(parts_{old}[k] * B^k) - borrow_{old} + borrow_{current} * B^i
	for (sizevalue i = 0; i < parts.size(); ++i) {
		parts[i] -= borrow;
		if (parts[i] != natmax_max) {
			borrow = 0;
			break;
		}
	}
	// 后置条件: (parts <- parts - borrow, borrow <- 0) 或者 (parts <- parts - borrow + U, borrow <- 1)
}

// 在调用 -= 函数后，当需要对溢出值进行限制时，应调用此函数
// 逻辑规范：
// 前置条件 P: number_of_states, value 皆有效 (not number_of_states.empty() and not value.empty())，且满足 number_of_states.size() = value.size()
// 后置条件 Q: 设 number_of_states 以 natmax 为单位的数字向上对齐的结果为 U (U = (max(natmax) + 1)^{number_of_states.size()})
//   value <- value + number_of_states (当value < number_of_states时)
//   value <- value - (U - number_of_states) (当value >= number_of_states时)
static void limit_value_after_decrease(span<natmax>&& number_of_states, span<natmax>&& value) noexcept
{
	// 前置条件: not number_of_states.empty() and not value.empty()
	runtime_assert(not number_of_states.empty() and not value.empty() and number_of_states.size() == value.size(), "limit_value_after_decrease 的前置条件不被满足");
	// 当 number_of_states 的大小为1时，说明 value 的大小理应也为1，此时只需一次计算即可
	if (number_of_states.size() == 1) {
		value.front() += (number_of_states.front());
		return;
	}
	// 如果value < number_of_states: value <- value + number_of_states，返回
	// 如果value >= number_of_states: value <- value + number_of_states - U (因为value + number_of_states >= U) = value - (U - number_of_states), 返回

	// 主循环：
	// 循环不变式：
	//   设 i = it - value.begin(), B 为 max(natmax) + 1
	//   value_{new} = value_{old} + Low_{i}(number_of_states) - carry * B^i 并且 i <= value.size()
	//   其中 Low_k(X) 表示 X 的低 k 位组成的自然数
	auto iterator_of_right = number_of_states.begin();
	nat8 carry = 0; // 借位
	for (auto it = value.begin(); it != value.end(); ++it) {
		sizevalue i = it - value.begin();
		
		natmax buffer = *it; // 临时存储加法前的值，稍后用于检查此次加法是否产生进位
		// buffer = value_i
		*it = *it + *iterator_of_right + carry;
		// value_i <- value_i + number_of_states_i + carry (当value_i + number_of_states_i + carry < B时)
		// value_i <- value_i - B + number_of_states_i + carry (当value_i + number_of_states_i + carry >= B时)
		nat8 last_carry = carry;
		carry = 0;
		// 检查此次加法是否产生进位
		if (*it < buffer or (last_carry == 1 and *it == buffer)) {
			carry = 1; // 使下次加法额外加1（若还有下次加法）
		}
		// carry <- 0 (当不产生进位时)
		// carry <- 1 (当产生进位时)
		++iterator_of_right;
	}
	// 后置条件: value <- value + number_of_states (当value < number_of_states时) 或者 value <- value - (U - number_of_states) (当value >= number_of_states时)
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())
// 后置条件 Q: *this <- *this - right
void numerical_cell::operator-=(const numerical_cell& right) noexcept
{
	// 前置条件: not this->content.empty() and not right.content.empty()
	runtime_assert(not this->content.empty() and not right.content.empty(), "数胞的-=函数的前置条件不被满足");
	span<natmax> current_value = this->value();
	span<natmax> right_value = right.value();
	right_value = right_value.subspan(0, find_if(right_value.rbegin(), --right_value.rend(), [](const natmax v) { return v != 0; }).base() - right_value.begin());
	// 当 right 的值大于自身的状态数限制时，需要将 right 的值限制在自身的状态数中，才能正确相减
	if (is_less_or_equal(this->number_of_states(), span<natmax>(right_value))) {
		limit_right_value_then_decrease(*this, right);
		return;
	}
	// 如果 this->number_of_states() <= right_value，则 *this <- *this - right，返回

	// 主循环：满足 this->number_of_states() > right_value
	// 循环不变式：
	//   设 i = it - value.begin(), B 为 max(natmax) + 1
	//   *this_{new} = *this_{old} - Low_{i}(right_value) + borrow * B^i 并且 i <= current_value.size()
	//   其中 Low_k(X) 表示 X 的低 k 位组成的自然数
	auto iterator_of_right = right_value.begin();
	nat8 borrow = 0; // 借位
	for (auto it = current_value.begin(); it != current_value.end(); ++it) {
		sizevalue i = it - current_value.begin();
		
		// 如果 right 的迭代器结束了，将可能为1的借位减到自身迭代器的值上，退出循环
		if (iterator_of_right == right_value.end()) {
			propagate_borrow_in_decrease(span<natmax>(current_value.data() + (it - current_value.begin()), current_value.size() - (it - current_value.begin())), borrow);
			break;
		}
		natmax buffer = *it; // 临时存储减法前的值，稍后用于检查此次减法是否产生借位
		// buffer = current_value_i
		*it = *it - *iterator_of_right - borrow;
		// current_value_i <- (current_value_i - right_value_i - borrow) mod B
		nat8 last_borrow = borrow;
		borrow = 0;
		// 检查此次减法是否产生借位
		if (*it > buffer or (last_borrow == 1 and *it == buffer)) {
			borrow = 1; // 使下次减法额外减1（若还有下次减法）
		}
		// borrow <- 0 (当不产生借位时)
		// borrow <- 1 (当产生借位时)
		++iterator_of_right;
	}
	// 计算完成后有两种情况
	// 1. 自身的值溢出(value >= number_of_states，溢出时一定产生借位)或自身的值没有溢出，但是最后一步产生借位，此时需要将自身值加上自身的状态数，方能得到正确结果
	// 2. 自身的值没有溢出，也没有产生借位，此时不需要进行处理
	if (borrow == 1 or bad()) {
		limit_value_after_decrease(this->number_of_states(), this->value());
	}
	// 后置条件: *this <- *this - right
}

// 在运行 *= 函数时，当 right 的值大于自身的状态数时，应调用此函数进行后续处理
// 逻辑规范：
// 前置条件 P: left, right 皆为有效的数胞 (not left.content.empty() and not right.content.empty())
// 后置条件 Q: left <- left * right
void numerical_cell::limit_right_value_then_multiply(numerical_cell& left, const numerical_cell& right) noexcept
{
	// 前置条件: not left.content.empty() and not right.content.empty()
	runtime_assert(not left.content.empty() and not right.content.empty(), "limit_right_value_then_multiply 的前置条件不被满足");
	vector<natmax> copy_right_value(right.value().begin(), right.value().end());
	// copy_right_value = right.value()
	vector<natmax> remainder = mod_value_by_value(span<natmax>(copy_right_value.data(), copy_right_value.size()), left.number_of_states());
	// remainder = copy_right_value mod left.number_of_states() = right.value() mod left.number_of_states()
	numerical_cell limited_right(right.number_of_states(), span<natmax>(remainder.data(), remainder.size()));
	// limited_right = numerical_cell(right.number_of_states(), remainder)
	left *= limited_right;
	// 后置条件: left <- left * limited_right = left * right
}

// 在运行 *= 函数时，当处理中间数据时，应调用此函数进行进位的传播
// 逻辑规范：
// 前置条件 P: parts 为有效的数胞的局部 (not parts.empty()) 并且 parts 足够容纳进位的结果 ((parts + carry).size() <= parts.size())
// 后置条件 Q: 设 B 为 max(nathalf) + 1
//   parts <- parts + carry, carry <- 0
static void propagate_carry_in_multiply(span<nathalf>&& parts, nathalf& carry) noexcept
{
	// 前置条件: not parts.empty()
	if (carry == 0) {
		return;
	}
	// 主循环：满足 carry = 1
	// 循环不变式：
	//   ∑_{k=0}^{i-1}(parts[k] * B^k) = ∑_{k=0}^{i-1}(parts_{old}[k] * B^k) + carry_{old} - carry_{current} * B^i
	for (sizevalue i = 0; i < parts.size(); ++i) {
		nathalf buffer = parts[i];
		parts[i] += carry;
		if (parts[i] >= buffer) {
			carry = 0;
			break;
		}
		else {
			carry = 1;
		}
	}
	// 后置条件: parts <- parts + carry, carry <- 0
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())
// 后置条件 Q: *this <- *this * right
void numerical_cell::operator*=(const numerical_cell& right) noexcept
{
	// 前置条件: not this->content.empty() and not right.content.empty()
	runtime_assert(not this->content.empty() and not right.content.empty(), "数胞的*=函数的前置条件不被满足");
	span<natmax> current_value = this->value();
	span<natmax> current_number_of_states = this->number_of_states();
	span<natmax> right_value = right.value();
	right_value = right_value.subspan(0, find_if(right_value.rbegin(), --right_value.rend(), [](const natmax v) { return v != 0; }).base() - right_value.begin());
	// 当 right 的值大于自身的状态数限制时，需要将 right 的值限制在自身的状态数中，才能正确相乘
	if (is_less_or_equal(span<natmax>(current_number_of_states), span<natmax>(right_value))) {
		limit_right_value_then_multiply(*this, right);
		return;
	}
	// 如果 this->number_of_states() <= right_value，则 *this <- *this * right，返回

	// 如果满足以下条件，则 current_value.front() * right_value.front() <= NATMAX_MAX
	if (current_value.size() == 1 and right_value.size() == 1 and current_value.front() <= nat32_max and right_value.front() <= nat32_max) {
		current_value.front() *= right_value.front();
		// 如果相乘后自身的值大于等于自身的状态数限制，需要进行限制
		if (is_greater_or_equal(span<natmax>(current_value), span<natmax>(current_number_of_states))) {
			mod_value_by_value(current_value, current_number_of_states);
		}
		return;
	}
	// 当满足以上条件时，则 *this <- *this * right，返回

	span<nathalf> half_form_current_value((nathalf*)current_value.data(), current_value.size() * 2);
	span<nathalf> half_form_right_value((nathalf*)right_value.data(), right_value.size() * 2);
	half_form_current_value = half_form_current_value.subspan(0, find_if(half_form_current_value.rbegin(), --half_form_current_value.rend(), [](const nathalf v) { return v != 0; }).base() - half_form_current_value.begin());
	half_form_right_value = half_form_right_value.subspan(0, find_if(half_form_right_value.rbegin(), --half_form_right_value.rend(), [](const nathalf v) { return v != 0; }).base() - half_form_right_value.begin());
	// 在所代表的值上，满足 half_form_current_value = current_value, half_form_right_value = right_value
	vector<nathalf> intermediate_data(half_form_current_value.size() + half_form_right_value.size() + 1, 0);

	nathalf carry = 0; // 进位
	// 外层循环，结束时代表 right 的每一位都已与自身的每一位相乘
	// 循环不变式：
	//   设 B = NAT32_MAX + 1, 当 n >= half_form_current_value.size() 时 half_form_current_value[n] = 0, 当 m >= half_form_right_value.size() 时 half_form_right_value[m] = 0
	//   intermediate_data = ∑_{m=0}^{i-1}(∑_{n=0}^{half_form_current_value.size()-1}(half_form_right_value[m] * half_form_current_value[n] * B^n) * B^m)
	for (sizevalue i = 0; i < half_form_right_value.size(); ++i) {
		nathalf right_digital = half_form_right_value[i]; // half_form_right_value 的第i位，将与自身的每一位进行一次乘法
		// 内层循环，结束时代表 right 的第i位都已与自身的每一位相乘
		// 循环不变式：
		//   设 B = NAT32_MAX + 1, last_intermediate_data 为循环开始前的 intermediate_data, 当 k >= half_form_current_value.size() 时 half_form_current_value[k] = 0
		//   intermediate_data = last_intermediate_data + (∑_{k=0}^{j-1}(right_digital * half_form_current_value[k] * B^k) - carry * B^{j-1}) * B^i
		for (sizevalue j = 0; j < half_form_current_value.size(); ++j) {
			natmax left_digital = half_form_current_value[j];
			left_digital *= right_digital;
			// left_digital = half_form_current_value[j] * half_form_right_value[i]
			nathalf last_carry = carry;
			carry = left_digital >> (sizeof(nathalf) * WORD_SIZE); // 取相乘结果的高半部分作为下次乘法的进位
			nathalf low_half_of_left_ditital = (nathalf)left_digital; // 低半部分
			// 此时设 intermediate_data_old <- intermediate_data
			nathalf anchor_value = intermediate_data[i + j];
			intermediate_data[i + j] += (nathalf)low_half_of_left_ditital;
			sizevalue k = 0;
			while (intermediate_data[i + j + k] < anchor_value) {
				anchor_value = intermediate_data[i + j + k + 1];
				intermediate_data[i + j + k + 1] += 1;
				k += 1;
			}
			// intermediate_data[i + j] = (low_half_of_left_ditital + last_carry) mod (NAT32_MAX + 1)
			propagate_carry_in_multiply(span<nathalf>(intermediate_data.data() + i + j, intermediate_data.size() - (i + j) - 1), last_carry);
			// intermediate_data = intermediate_data_old + last_carry * (NAT32_MAX + 1)^(i + j)
			// 如果相乘结果加上进位导致再次进位，修正进位(+1)
			if (low_half_of_left_ditital + last_carry < low_half_of_left_ditital) {
				++carry;
			}
			// carry = (half_form_current_value[j] * half_form_right_value[i]) 整除 (NAT32_MAX + 1) + (low_half_of_left_ditital + last_carry) mod (NAT32_MAX + 1)
		}

		if (carry > 0) {
			// 如果最后一次乘法依然产生进位，将其附加在专门为进位预留的最后一位上
			propagate_carry_in_multiply(span<nathalf>(intermediate_data.data() + i + half_form_current_value.size(), 1), carry);
		}
		// intermediate_data = ∑_{m=0}^{i-1}(∑_{n=0}^{j-1}(right_digital * half_form_current_value[n] * B^n) * B^m)
	}

	sizevalue new_size = find_if(intermediate_data.rbegin(), intermediate_data.rend(), [](const nathalf v) { return v != 0; }).base() - intermediate_data.begin();
	if (new_size == 0) {
		new_size = 1;
	}
	intermediate_data.resize(new_size % 2 == 0 ? new_size : new_size + 1);
	// intermediate_data.size() mod 2 = 0
	span<natmax> final_intermediate_data((natmax*)intermediate_data.data(), intermediate_data.size() / 2);
	// 在数值上，final_intermediate_data = intermediate_data
	if (is_greater_or_equal(span<natmax>(final_intermediate_data).subspan(0, find_if(final_intermediate_data.rbegin(), --final_intermediate_data.rend(), [](const natmax v) { return v != 0; }).base() - final_intermediate_data.begin()), span<natmax>(current_number_of_states))) {
		mod_value_by_value(final_intermediate_data, current_number_of_states);
	}
	// final_intermediate_data <- final_intermediate_data mod current_number_of_states
	memset(current_value.data(), 0, current_value.size());
	memcpy(current_value.data(), final_intermediate_data.data(), final_intermediate_data.size() * sizeof(natmax));
	// 后置条件: *this <- *this * right
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())，且 right 的值不为 0
// 后置条件 Q: *this <- *this / right
void numerical_cell::operator/=(const numerical_cell& right)
{
	// 前置条件: not this->content.empty() and not right.content.empty()
	runtime_assert(not this->content.empty() and not right.content.empty(), "数胞的/=函数的前置条件不被满足");

	span<natmax> current_value = this->value();
	span<natmax> right_value = right.value();
	current_value = current_value.subspan(0, find_if(current_value.rbegin(), --current_value.rend(), [](const natmax v) { return v != 0; }).base() - current_value.begin());
	right_value = right_value.subspan(0, find_if(right_value.rbegin(), --right_value.rend(), [](const natmax v) { return v != 0; }).base() - right_value.begin());

	// 如果满足以下条件，可以直接进行单次相除得到结果
	if (current_value.size() == 1 and right_value.size() == 1) {
		current_value.front() /= right_value.front();
		return;
	}
	// 如果被除数小于除数，则结果一定为 0
	if (is_less(span<natmax>(current_value), span<natmax>(right_value))) {
		memset(current_value.data(), 0, current_value.size() * sizeof(natmax));
		return;
	}
	// 满足 current_value >= right_value
	vector<natmax> result = div_value_by_value(current_value, right_value);
	memset(current_value.data(), 0, current_value.size() * sizeof(natmax));
	memcpy(current_value.data(), result.data(), result.size() * sizeof(natmax));
	// 后置条件: *this <- *this / right
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())，且 right 的值不为 0
// 后置条件 Q: *this <- *this / right
void numerical_cell::operator%=(const numerical_cell& right)
{
	// 前置条件: not this->content.empty() and not right.content.empty()
	runtime_assert(not this->content.empty() and not right.content.empty(), "数胞的%=函数的前置条件不被满足");

	span<natmax> current_value = this->value();
	span<natmax> right_value = right.value();
	current_value = current_value.subspan(0, find_if(current_value.rbegin(), --current_value.rend(), [](const natmax v) { return v != 0; }).base() - current_value.begin());
	right_value = right_value.subspan(0, find_if(right_value.rbegin(), --right_value.rend(), [](const natmax v) { return v != 0; }).base() - right_value.begin());

	// 如果满足以下条件，可以直接进行单次相除得到结果
	if (current_value.size() == 1 and right_value.size() == 1) {
		current_value.front() %= right_value.front();
		return;
	}
	// 如果被除数小于除数，则结果为被除数
	if (is_less(span<natmax>(current_value), span<natmax>(right_value))) {
		return;
	}
	// 满足 current_value >= right_value
	mod_value_by_value(current_value, right_value);
	// 后置条件: *this <- *this / right
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())，且 *this 与 right 的状态数相同
// 后置条件 Q: 输出 *this + right
numerical_cell numerical_cell::operator+(const numerical_cell& right) const noexcept
{
	runtime_assert(not this->content.empty() and not right.content.empty() and is_equal(this->number_of_states(), right.number_of_states()), "数胞的+函数的前置条件不被满足，自身的状态数为" + generate_information_of_linear_table(number_of_states()) + "，自身的值为" + generate_information_of_linear_table(this->value()) + "，操作数的值为" + generate_information_of_linear_table(right.value()));
	numerical_cell result = *this;
	result += right;
	return std::move(result);
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())，且 *this 与 right 的状态数相同
// 后置条件 Q: 输出 *this - right
numerical_cell numerical_cell::operator-(const numerical_cell& right) const noexcept
{
	runtime_assert(not this->content.empty() and not right.content.empty() and is_equal(this->number_of_states(), right.number_of_states()), "数胞的-函数的前置条件不被满足，自身的状态数为" + generate_information_of_linear_table(number_of_states()) + "，自身的值为" + generate_information_of_linear_table(this->value()) + "，操作数的值为" + generate_information_of_linear_table(right.value()));
	numerical_cell result = *this;
	result -= right;
	return std::move(result);
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())，且 *this 与 right 的状态数相同
// 后置条件 Q: 输出 *this * right
numerical_cell numerical_cell::operator*(const numerical_cell& right) const noexcept
{
	runtime_assert(not this->content.empty() and not right.content.empty() and is_equal(this->number_of_states(), right.number_of_states()), "数胞的*函数的前置条件不被满足，自身的状态数为" + generate_information_of_linear_table(number_of_states()) + "，自身的值为" + generate_information_of_linear_table(this->value()) + "，操作数的值为" + generate_information_of_linear_table(right.value()));
	numerical_cell result = *this;
	result *= right;
	return std::move(result);
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())，且 *this 与 right 的状态数相同，且 right 的值不为 0
// 后置条件 Q: 输出 *this / right
numerical_cell numerical_cell::operator/(const numerical_cell& right) const
{
	span<natmax> right_value = right.value();
	runtime_assert(not this->content.empty() and not right.content.empty() and is_equal(this->number_of_states(), right.number_of_states()) and not all_of(right_value.begin(), right_value.end(), [](natmax v) { return v == 0; }), "数胞的/函数的前置条件不被满足，自身的状态数为" + generate_information_of_linear_table(number_of_states()) + "，自身的值为" + generate_information_of_linear_table(this->value()) + "，操作数的值为" + generate_information_of_linear_table(right.value()));
	numerical_cell result = *this;
	result /= right;
	return std::move(result);
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())，且 *this 与 right 的状态数相同，且 right 的值不为 0
// 后置条件 Q: 输出 *this % right
numerical_cell numerical_cell::operator%(const numerical_cell& right) const
{
	span<natmax> right_value = right.value();
	runtime_assert(not this->content.empty() and not right.content.empty() and is_equal(this->number_of_states(), right.number_of_states()) and not all_of(right_value.begin(), right_value.end(), [](natmax v) { return v == 0; }), "数胞的%函数的前置条件不被满足，自身的状态数为" + generate_information_of_linear_table(number_of_states()) + "，自身的值为" + generate_information_of_linear_table(this->value()) + "，操作数的值为" + generate_information_of_linear_table(right.value()));
	numerical_cell result = *this;
	result %= right;
	return std::move(result);
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())
// 后置条件 Q: 输出 *this == right
bool numerical_cell::operator==(const numerical_cell& right) const noexcept
{
	span<natmax> current_value = this->value();
	span<natmax> right_value = right.value();
	runtime_assert(not current_value.empty() and not right_value.empty(), "数胞的==函数的前置条件不被满足");
	current_value = current_value.subspan(0, find_if(current_value.rbegin(), --current_value.rend(), [](const natmax v) { return v != 0; }).base() - current_value.begin());
	right_value = right_value.subspan(0, find_if(right_value.rbegin(), --right_value.rend(), [](const natmax v) { return v != 0; }).base() - right_value.begin());
	sizevalue min_size = min(current_value.size(), right_value.size());
	if (current_value.size() != right_value.size()) {
		return false;
	}
	for (sizevalue i = 0; i < min_size; ++i) {
		if (current_value[i] != right_value[i]) {
			return false;
		}
	}
	return true;
}

// 逻辑规范：
// 前置条件 P: *this, right 皆有效 (not this->content.empty() and not right.content.empty())
// 后置条件 Q: 输出 *this <=> right
weak_ordering numerical_cell::operator<=>(const numerical_cell& right) const noexcept
{
	span<natmax> current_value = this->value();
	span<natmax> right_value = right.value();
	runtime_assert(not current_value.empty() and not right_value.empty(), "数胞的<=>函数的前置条件不被满足");
	current_value = current_value.subspan(0, find_if(current_value.rbegin(), --current_value.rend(), [](const natmax v) { return v != 0; }).base() - current_value.begin());
	right_value = right_value.subspan(0, find_if(right_value.rbegin(), --right_value.rend(), [](const natmax v) { return v != 0; }).base() - right_value.begin());
	sizevalue min_size = min(current_value.size(), right_value.size());
	if (current_value.size() < right_value.size()) {
		return weak_ordering::less;
	}
	if (current_value.size() > right_value.size()) {
		return weak_ordering::greater;
	}
	for (sizevalue i = min_size - 1; i < min_size; --i) {
		if (current_value[i] < right_value[i]) {
			return weak_ordering::less;
		}
		if (current_value[i] > right_value[i]) {
			return weak_ordering::greater;
		}
	}
	return weak_ordering::equivalent;
}