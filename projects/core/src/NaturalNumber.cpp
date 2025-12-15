#include "NaturalNumber"
#include "Basic"
#include "BitSpan"
#include "vector"
#include "span"

using std::vector;
using std::span;
using std::memcpy;
using std::min;
using std::max;
using std::runtime_error;

static vector<natmax> mod_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept;
static vector<natmax> div_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept;
static void decrease_between_bit_spans(bit_span& minuend, const bit_span& subtrahend) noexcept;
template <typename T> bool is_less(T&& l, T&& r) noexcept;
template <typename T> bool is_less_or_equal(T&& l, T&& r) noexcept;
template <typename T> bool is_greater_or_equal(T&& l, T&& r) noexcept;

using nathalf = nat32;
static void propagate_carry_in_increase(span<natmax>&& parts, nat8& carry) noexcept;
static void propagate_borrow_in_decrease(span<natmax>&& parts, nat8& borrow) noexcept;
static void propagate_carry_in_multiply(span<nathalf>&& parts, nathalf& carry) noexcept;

natural_number::natural_number(const vector<natmax>& value) noexcept
{
	span<natmax> value_span(const_cast<natmax*>(value.data()), find_if(value.rbegin(), value.rend(), [](natmax x) { return x != 0; }).base() - value.begin());
	content.resize(value_span.size(), 0);
	memcpy(content.data(), value_span.data(), value_span.size() * sizeof(natmax));
}

natural_number::natural_number(vector<natmax>&& value) noexcept
{
	span<natmax> value_span(const_cast<natmax*>(value.data()), find_if(value.rbegin(), value.rend(), [](natmax x) { return x != 0; }).base() - value.begin());
	content.resize(value_span.size(), 0);
	memcpy(content.data(), value_span.data(), value_span.size() * sizeof(natmax));
}

natural_number::natural_number(span<natmax> value) noexcept
{
	value = value.subspan(0, find_if(value.rbegin(), value.rend(), [](natmax x) { return x != 0; }).base() - value.begin());
	content.resize(value.size(), 0);
	memcpy(content.data(), value.data(), value.size() * sizeof(natmax));
}

bool natural_number::bad() const noexcept
{
	if (this->content.empty()) {
		return false;
	}
	return this->content.back() == 0;
}

natural_number::natural_number(const natural_number& right) noexcept
{
	this->content = right.content;
}

natural_number::natural_number(natural_number&& right) noexcept
{
	this->content = right.content;
}

void natural_number::operator=(span<natmax> value) noexcept
{
	value = value.subspan(0, find_if(value.rbegin(), value.rend(), [](natmax x) { return x != 0; }).base() - value.begin());
	this->content.resize(value.size());
	memcpy(this->content.data(), value.data(), value.size() * sizeof(natmax));
}

void natural_number::operator=(const natural_number& right) noexcept
{
	content = right.content;
}

void natural_number::operator=(natural_number&& right) noexcept
{
	content = right.content;
}

// 霍尔逻辑规范：
// 前置条件 P: dividend 和 divisor 皆有效 (作为无符号数解释)，且 divisor != 0
// 后置条件 Q: 返回 dividend mod divisor (余数)
// 注意: dividend 在调用此函数之后可能会被改变
static vector<natmax> mod_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept
{
	// 将输入转换为位跨度
	bit_span dividend_bit_span = bit_span(reinterpret_cast<::byte*>(dividend.data()), 0, dividend.size() * sizeof(natmax) * WORD_SIZE);
	bit_span divisor_bit_span = bit_span(reinterpret_cast<::byte*>(divisor.data()), 0, divisor.size() * sizeof(natmax) * WORD_SIZE);
	dividend_bit_span = dividend_bit_span.subspan(0, find_if(dividend_bit_span.rbegin(), dividend_bit_span.rend(), [](::byte b) { return b != 0; }).base() - dividend_bit_span.begin());
	divisor_bit_span = divisor_bit_span.subspan(0, find_if(divisor_bit_span.rbegin(), divisor_bit_span.rend(), [](::byte b) { return b != 0; }).base() - divisor_bit_span.begin());

	// 前置条件检查：除数不能为0
	if (divisor_bit_span.size() == 0) {
		return vector<natmax>(); // 除数为0，返回空向量
	}

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
		sub_dividend = sub_dividend.subspan(0, find_if(sub_dividend.rbegin(), sub_dividend.rend(), [](::byte b) { return b != 0; }).base() - sub_dividend.begin());

		// 循环不变式: 
		//   sub_dividend 表示当前被处理的位段
		//   该位段的值 >= divisor 或需要继续扩展

		// 比较当前子跨度与除数
		if (!is_less(sub_dividend, divisor_bit_span)) { // 即 sub_dividend >= divisor
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
	remainder.erase(find_if(remainder.rbegin(), remainder.rend(), [](natmax value) { return value != 0; }).base(), remainder.end());
	if (remainder.empty()) {
		remainder.push_back(0);
	}
	return std::move(remainder);
}

static vector<natmax> div_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept
{
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
	for (sizevalue i = 0; i < dividend_bit_span.size(); ++i) {
		// 取当前子跨度：从最高位到当前位
		sizevalue start_index = dividend_bit_span.size() - 1 - i;
		sizevalue length = i + 1;
		auto sub_dividend = dividend_bit_span.subspan(start_index, length);
		sub_dividend = sub_dividend.subspan(0, find_if(sub_dividend.rbegin(), sub_dividend.rend(), [](::byte b) { return b != 0; }).base() - sub_dividend.begin());
		// 如果目前循环取到的被除数部分小于除数，则不能进行相减计算，即不能在此位相除
		if (is_less(sub_dividend, divisor_bit_span)) {
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
	result.erase(find_if(result.rbegin(), result.rend(), [](natmax value) { return value != 0; }).base(), result.end());
	if (result.empty()) {
		result.push_back(0);
	}
	return std::move(result);
}

// 霍尔逻辑规范：
// 前置条件 P: minuend >= subtrahend (作为无符号整数解释)，且两者均为有效位跨度
// 后置条件 Q: minuend := minuend - subtrahend
static void decrease_between_bit_spans(bit_span& minuend, const bit_span& subtrahend) noexcept
{
	// 前置条件: minuend >= subtrahend
	sizevalue culculate_length = min(minuend.size(), subtrahend.size());
	// culculate_length := min(minuend.size(), subtrahend.size())
	bool borrow = false;

	// 主循环：处理公共位段 (0 到 culculate_length-1)
	// 循环不变式: 
	//   设 A = old(minuend), B = subtrahend, L = min(size)
	//   对于当前处理的位索引 i (0 ≤ i ≤ culculate_length):
	//     Low_i(minuend) = Low_i(A) - Low_i(B) - 2^i * borrow
	//   其中 Low_k(X) = X mod 2^k，表示 X 的低 k 位组成的自然数

	// 证明：
	// minuend mod 2^i = (A mod 2^i) - (B mod 2^i) - 2^i * borrow
	// minuend[i] = (minuend / 2^i) mod 2
	// (minuend / 2^i) mod 2 := ((minuend // 2^i) mod 2 - (subtrahend // 2^i) mod 2 - borrow) mod 2 = ((minuend // 2^i) - (subtrahend // 2^i) - borrow) mod 2
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

// 霍尔逻辑规范：
// 前置条件 P: l,r 皆为有效的非空线性表 (两者均作为自然数解释, l.size() > 0, r.size() > 0)，且l,r均不存在高位无效0 (l.size() > 1 => l.back() != 0, r.size() > 1 => r.back() != 0)
// 后置条件 Q: 返回 l < r
template <typename T>
bool is_less(T&& l, T&& r) noexcept
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
	//     High_{L-i-1}(l) = High_{L-i-1}(r) 并且 (i = SIZEVALUE_MAX 或者 i < L)
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

// 霍尔逻辑规范：
// 前置条件 P: l,r 皆为有效的非空线性表 (两者均作为自然数解释, l.size() > 0, r.size() > 0)，且l,r均不存在高位无效0 (l.size() > 1 => l.back() != 0, r.size() > 1 => r.back() != 0)
// 后置条件 Q: 返回 l <= r
template <typename T>
bool is_less_or_equal(T&& l, T&& r) noexcept
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
	//     High_{L-i-1}(l) = High_{L-i-1}(r) 并且 (i = SIZEVALUE_MAX 或者 i < L)
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
	// l = r => 返回 true
	return true;
}

// 霍尔逻辑规范：
// 前置条件 P: l,r 皆为有效的非空线性表 (两者均作为自然数解释, l.size() > 0, r.size() > 0)，且l,r均不存在高位无效0 (l.size() > 1 => l.back() != 0, r.size() > 1 => r.back() != 0)
// 后置条件 Q: 返回 l >= r
template <typename T>
bool is_greater_or_equal(T&& l, T&& r) noexcept
{
	// 前置条件: l.size() > 0, r.size() > 0, l.back() != 0, r.back() != 0
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
	//     High_{L-i-1}(l) = High_{L-i-1}(r) 并且 (i = SIZEVALUE_MAX 或者 i < L)
	//   其中 High_k(X) 表示 X 的高 k (k >= 0) 位组成的自然数 (当 k=0 时定义为空，恒成立)
	for (sizevalue i = l.size() - 1; i < l.size(); --i) {
		if (l[i] < r[i]) {
			return false;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] < r[i] => l < r => 返回 false) 或者 (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] >= r[i])
		if (l[i] > r[i]) {
			return true;
		}
		// (High_{L-i-1}(l) = High_{L-i-1}(r) 并且 l[i] > r[i] => l > r => 返回 true) 或者 High_{L-i}(l) = High_{L-i}(r)
	}
	// l = r => 返回 true
	return true;
}

// 在运行 += 函数时，当 right 的长度短于自身时，应调用此函数进行进位的传播
// 霍尔逻辑规范：
// 前置条件 P: parts 为有效的数的局部 (not parts.empty()) 并且 (carry = 0 或者 carry = 1)
// 后置条件 Q: 设 B 为 max(natmax) + 1, parts 以 natmax 为单位的数字向上对齐的结果为 U (U mod (max(natmax) + 1) = 0)
//   (parts <- parts + carry, carry <- 0) 或者 (parts <- parts + carry - U, carry <- 1)
static void propagate_carry_in_increase(span<natmax>&& parts, nat8& carry) noexcept
{
	// 前置条件: not parts.empty()
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

void natural_number::operator+=(const natural_number& right) noexcept
{
	auto iterator_of_right = right.content.begin();
	nat8 carry = 0; // 进位
	sizevalue max_length = max(content.size(), right.content.size());
	content.resize(max_length);
	for (auto it = content.begin(); it != content.end(); ++it) {
		// 如果 right 的迭代器结束了，将可能为1的进位加到自身迭代器的值上，退出循环
		if (iterator_of_right == right.content.end()) {
			propagate_carry_in_increase(span<natmax>(content.data() + (it - content.begin()), content.size() - (it - content.begin())), carry);
			break;
		}
		natmax buffer = *it; // 临时存储加法前的值，稍后用于检查此次加法是否产生进位
		*it = *it + *iterator_of_right + carry;
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
	if (carry == 1) {
		content.push_back(1);
	}
	content.erase(find_if(content.rbegin(), content.rend(), [](natmax value) { return value != 0; }).base(), content.end());
	if (content.empty()) {
		content.push_back(0);
	}
}

// 在运行 -= 函数时，当 right 的长度短于自身时，应调用此函数进行借位的传播
// 霍尔逻辑规范：
// 前置条件 P: parts 为有效的数的局部 (not parts.empty()) 并且 (borrow = 0 或者 borrow = 1)
// 后置条件 Q: 设 B 为 max(natmax) + 1, parts 以 natmax 为单位的数字向上对齐的结果为 U (U mod (max(natmax) + 1) = 0)
//   (parts <- parts - borrow, borrow <- 0) 或者 (parts <- parts - borrow + U, borrow <- 1)
static void propagate_borrow_in_decrease(span<natmax>&& parts, nat8& borrow) noexcept
{
	// 前置条件: not parts.empty()
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

void natural_number::operator-=(const natural_number& right)
{
	if (is_less(vector<natmax>(content), vector<natmax>(right.content))) {
		throw runtime_error("被减数小于减数");
	}
	auto iterator_of_right = right.content.begin();
	nat8 borrow = 0; // 借位
	for (auto it = content.begin(); it != content.end(); ++it) {
		// 如果 right 的迭代器结束了，将可能为1的借位减到自身迭代器的值上，退出循环
		if (iterator_of_right == right.content.end()) {
			propagate_borrow_in_decrease(span<natmax>(content.data() + (it - content.begin()), content.size() - (it - content.begin())), borrow);
			break;
		}
		natmax buffer = *it; // 临时存储减法前的值，稍后用于检查此次减法是否产生借位
		*it = *it - *iterator_of_right - borrow;
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
	if (borrow == 1) {
		throw runtime_error("被减数小于减数");
	}
	content.erase(find_if(content.rbegin(), content.rend(), [](natmax value) { return value != 0; }).base(), content.end());
	if (content.empty()) {
		content.push_back(0);
	}
}

// 在运行 *= 函数时，当处理中间数据时，应调用此函数进行进位的传播
// 霍尔逻辑规范：
// 前置条件 P: parts 为有效的数的局部 (not parts.empty()) 并且 parts 足够容纳进位的结果 ((parts + carry).size() <= parts.size())
// 后置条件 Q: 设 B 为 max(nathalf) + 1, parts 以 nathalf 为单位的数字向上对齐的结果为 U (U mod (max(nathalf) + 1) = 0)
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

void natural_number::operator*=(const natural_number& right) noexcept
{
	if (content.size() == 1 and right.content.size() == 1 and content.front() <= nat32_max and right.content.front() <= nat32_max) {
		content.front() *= right.content.front();
		return;
	}

	span<nathalf> half_form_current_value((nathalf*)content.data(), content.size() * 2);
	span<nathalf> half_form_right_value((nathalf*)right.content.data(), right.content.size() * 2);
	half_form_current_value = half_form_current_value.subspan(0, find_if(half_form_current_value.rbegin(), half_form_current_value.rend(), [](const nathalf v) { return v != 0; }).base() - half_form_current_value.begin());
	half_form_right_value = half_form_right_value.subspan(0, find_if(half_form_right_value.rbegin(), half_form_right_value.rend(), [](const nathalf v) { return v != 0; }).base() - half_form_right_value.begin());
	// 在所代表的值上，满足 half_form_current_value = current_value, half_form_right_value = right_value
	vector<nathalf> intermediate_data(half_form_current_value.size() + half_form_right_value.size(), 0);

	nathalf carry = 0; // 进位
	for (sizevalue i = 0; i < half_form_right_value.size(); ++i) {
		nathalf right_digital = half_form_right_value[i]; // half_form_right_value 的第i位，将与自身的每一位进行一次乘法
		for (sizevalue j = 0; j < half_form_current_value.size(); ++j) {
			natmax left_digital = half_form_current_value[j];
			left_digital *= right_digital;
			nathalf last_carry = carry;
			carry = left_digital >> (sizeof(nathalf) * WORD_SIZE); // 取相乘结果的高半部分作为下次乘法的进位
			nathalf low_half_of_left_ditital = (nathalf)left_digital; // 低半部分
			nathalf anchor_value = intermediate_data[i + j];
			intermediate_data[i + j] += (nathalf)low_half_of_left_ditital;
			sizevalue k = 0;
			while (intermediate_data[i + j + k] < anchor_value) {
				anchor_value = intermediate_data[i + j + k + 1];
				intermediate_data[i + j + k + 1] += 1;
				k += 1;
			}
			propagate_carry_in_multiply(span<nathalf>(intermediate_data.data() + i + j, intermediate_data.size() - (i + j)), last_carry);
			// 如果相乘结果加上进位导致再次进位，修正进位(+1)
			if (low_half_of_left_ditital + last_carry < low_half_of_left_ditital) {
				++carry;
			}
		}
		if (carry > 0) {
			// 如果最后一次乘法依然产生进位，将其附加在专门为进位预留的最后一位上
			propagate_carry_in_multiply(span<nathalf>(intermediate_data.data() + i + half_form_current_value.size(), 1), carry);
		}
	}
	sizevalue new_size = find_if(intermediate_data.rbegin(), intermediate_data.rend(), [](const nathalf v) { return v != 0; }).base() - intermediate_data.begin();
	if (new_size == 0) {
		new_size = 1;
	}
	intermediate_data.resize(new_size % 2 == 0 ? new_size : new_size + 1);
	span<natmax> final_intermediate_data((natmax*)intermediate_data.data(), intermediate_data.size() / 2);
	content.resize(final_intermediate_data.size());
	memcpy(content.data(), final_intermediate_data.data(), final_intermediate_data.size() * sizeof(natmax));
	content.erase(find_if(content.rbegin(), content.rend(), [](natmax value) { return value != 0; }).base(), content.end());
	if (content.empty()) {
		content.push_back(0);
	}
}

void natural_number::operator/=(const natural_number& right)
{
	// 如果 right 的值为0，则因为任何数除0在数学中都是未定义的，抛出异常
	if (all_of(right.content.begin(), right.content.end(), [](natmax n) { return n == 0; })) {
		throw runtime_error("不能除0");
	}
	// 当确定此对象的值与参数对象的值的长度都为1时，只需进行1次计算即可
	if (content.size() == 1 and right.content.size() == 1) {
		content.front() /= right.content.front();
		return;
	}
	// 否则以二进制的形式相除
	content = div_value_by_value(span<natmax>(content.data(), content.size()), span<natmax>((natmax*)right.content.data(), right.content.size()));
}

void natural_number::operator%=(const natural_number& right)
{
	// 如果 right 的值为0，则因为任何数除0在数学中都是未定义的（求余数需要相除），抛出异常
	if (all_of(right.content.begin(), right.content.end(), [](natmax n) { return n == 0; })) {
		throw runtime_error("不能除0");
	}
	// 当确定此对象的值与参数对象的值的长度都为1时，只需进行1次计算即可
	if (content.size() == 1 and right.content.size() == 1) {
		content.front() %= right.content.front();
		return;
	}
	// 否则以二进制的形式相除，取相除时得到的余数
	content = mod_value_by_value(span<natmax>(content.data(), content.size()), span<natmax>((natmax*)right.content.data(), right.content.size()));
}

natural_number natural_number::operator+(const natural_number& right) const noexcept
{
	natural_number result = *this;
	result += right;
	return std::move(result);
}

natural_number natural_number::operator-(const natural_number& right) const
{
	natural_number result = *this;
	result -= right;
	return std::move(result);
}

natural_number natural_number::operator*(const natural_number& right) const noexcept
{
	natural_number result = *this;
	result *= right;
	return std::move(result);
}

natural_number natural_number::operator/(const natural_number& right) const
{
	natural_number result = *this;
	result /= right;
	return std::move(result);
}

natural_number natural_number::operator%(const natural_number& right) const
{
	natural_number result = *this;
	result %= right;
	return std::move(result);
}

bool natural_number::operator==(const natural_number& right) const noexcept
{
	sizevalue min_size = min(content.size(), right.content.size());
	if (content.size() < right.content.size()) {
		if (any_of(right.content.rbegin(), right.content.rbegin() + (right.content.size() - content.size()), [](natmax n) { return n != 0; })) {
			return false;
		}
	}
	else if (content.size() > right.content.size()) {
		if (any_of(content.rbegin(), content.rbegin() + (content.size() - right.content.size()), [](natmax n) { return n != 0; })) {
			return false;
		}
	}
	for (nat64 i = 0; i < min_size; ++i) {
		if (content[i] < right.content[i]) {
			return false;
		}
		if (content[i] > right.content[i]) {
			return false;
		}
	}
	return true;
}

bool natural_number::operator<(const natural_number& right) const noexcept
{
	sizevalue min_size = min(content.size(), right.content.size());
	if (content.size() < right.content.size()) {
		return true;
	}
	else if (content.size() > right.content.size()) {
		return false;
	}
	for (nat64 i = min_size - 1; i < min_size; --i) {
		if (content[i] < right.content[i]) {
			return true;
		}
		if (content[i] > right.content[i]) {
			return false;
		}
	}
	return false;
}

bool natural_number::operator>(const natural_number& right) const noexcept
{
	sizevalue min_size = min(content.size(), right.content.size());
	if (content.size() < right.content.size()) {
		return false;
	}
	else if (content.size() > right.content.size()) {
		return true;
	}
	for (nat64 i = min_size - 1; i < min_size; --i) {
		if (content[i] < right.content[i]) {
			return false;
		}
		if (content[i] > right.content[i]) {
			return true;
		}
	}
	return false;
}

bool natural_number::operator<=(const natural_number& right) const noexcept
{
	sizevalue min_size = min(content.size(), right.content.size());
	if (content.size() < right.content.size()) {
		return true;
	}
	else if (content.size() > right.content.size()) {
		return false;
	}
	for (nat64 i = min_size - 1; i < min_size; --i) {
		if (content[i] < right.content[i]) {
			return true;
		}
		if (content[i] > right.content[i]) {
			return false;
		}
	}
	return true;
}

bool natural_number::operator>=(const natural_number& right) const noexcept
{
	sizevalue min_size = min(content.size(), right.content.size());
	if (content.size() < right.content.size()) {
		return false;
	}
	else if (content.size() > right.content.size()) {
		return true;
	}
	for (nat64 i = min_size - 1; i < min_size; --i) {
		if (content[i] < right.content[i]) {
			return false;
		}
		if (content[i] > right.content[i]) {
			return true;
		}
	}
	return true;
}