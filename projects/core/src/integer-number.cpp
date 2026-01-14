#include <integer-number>
#include <basic>
#include <bit-span>
#include <vector>
#include <span>

using std::vector;
using std::span;
using std::copy;
using std::min;
using std::max;
using std::runtime_error;

void clear_invalid_bits(vector<natmax>& content) noexcept;

static vector<natmax> mod_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept;
static vector<natmax> div_value_by_value(const span<natmax>& dividend, const span<natmax> divisor) noexcept;
static void decrease_between_bit_spans(bit_span& minuend, const bit_span& subtrahend) noexcept;

using nathalf = nat32;
static void propagate_carry_in_increase(span<natmax>&& parts, nat8& carry) noexcept;
static void propagate_borrow_in_decrease(span<natmax>&& parts, nat8& borrow) noexcept;
static void propagate_carry_in_multiply(span<nathalf>&& parts, nathalf& carry) noexcept;

integer_number::integer_number(const vector<natmax>& value) noexcept
{
	content.resize(value.size(), 0);
	copy(value.data(), value.data() + value.size(), content.data());
	clear_invalid_bits(content);
}

integer_number::integer_number(vector<natmax>&& value) noexcept
{
	content.resize(value.size(), 0);
	copy(value.data(), value.data() + value.size(), content.data());
	clear_invalid_bits(content);
}

integer_number::integer_number(span<natmax> value) noexcept
{
	content.resize(value.size(), 0);
	copy(value.data(), value.data() + value.size(), content.data());
	clear_invalid_bits(content);
}

bool integer_number::bad() const noexcept
{
	if (this->content.empty()) {
		return false;
	}
	if (this->content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1 && this->content.size() > 1) {
		return this->content[this->content.size() - 2] >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
	}
	else if (this->content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0 && this->content.size() > 1) {
		return this->content[this->content.size() - 2] >> (sizeof(natmax) * WORD_SIZE - 1) == 0;
	}
	return false;
}

integer_number::integer_number(const integer_number& right) noexcept
{
	this->content = right.content;
}

integer_number::integer_number(integer_number&& right) noexcept
{
	this->content = right.content;
}

void integer_number::operator=(span<natmax> value) noexcept
{
	if (value.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
		value = value.subspan(0, find_if(value.rbegin(), value.rend(), [](natmax x) { return x != 0; }).base() - value.begin());
	}
	else if (value.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1 && value.size() > 1) {
		value = value.subspan(0, find_if(value.rbegin() + 1, value.rend(), [](natmax x) { return x != natmax_max; }).base() - value.begin());
	}
	this->content.resize(value.size());
    copy(value.data(), value.data() + value.size(), this->content.data());
}

void integer_number::operator=(const integer_number& right) noexcept
{
	content = right.content;
}

void integer_number::operator=(integer_number&& right) noexcept
{
	content = right.content;
}

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
	// 满足 l.size() = r.size()
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

	// 长除法求余数
	for (sizevalue i = 0; i < dividend_bit_span.size(); ++i) {
		// 取当前子跨度：从最高位到当前位
		sizevalue start_index = dividend_bit_span.size() - 1 - i;
		sizevalue length = i + 1;
		auto sub_dividend = dividend_bit_span.subspan(start_index, length);
		sub_dividend = sub_dividend.subspan(0, find_if(sub_dividend.rbegin(), sub_dividend.rend(), [](::byte b) { return b != 0; }).base() - sub_dividend.begin());

		// 比较当前子跨度与除数
		if (!bit_is_less(sub_dividend, divisor_bit_span)) { // 即 sub_dividend >= divisor
			// 执行减法：sub_dividend <- sub_dividend - divisor
			decrease_between_bit_spans(sub_dividend, divisor_bit_span);
		}
	}

	// 计算余数的位数 (不超过除数的位数)
	vector<natmax> remainder(dividend.size());

	// 复制余数部分 (dividend 的低位)
	copy(dividend.data(), dividend.data() + remainder.size(), remainder.data());

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
	result.erase(find_if(result.rbegin(), result.rend(), [](natmax value) { return value != 0; }).base(), result.end());
	if (result.empty()) {
		result.push_back(0);
	}
	return std::move(result);
}

static void decrease_between_bit_spans(bit_span& minuend, const bit_span& subtrahend) noexcept
{
	// 前置条件: minuend >= subtrahend
	sizevalue culculate_length = min(minuend.size(), subtrahend.size());
	bool borrow = false;

	// 处理公共位段 (0 到 culculate_length-1)
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
	if (borrow) {
		sizevalue offset = 0;
		// 借位传播：从 culculate_length 开始向高位传播
		// 终止条件：当遇到一个位翻转后为 false (即原为 true)
		do {
			// 翻转当前高位位 (借位传播)
			minuend[culculate_length + offset] = !minuend[culculate_length + offset];
			++offset;
		} while (minuend[culculate_length + offset - 1] == true);
	}
	// 后置条件: minuend = old(minuend) - subtrahend
}

void clear_invalid_bits(vector<natmax>& content) noexcept
{
	if (content.empty()) {
		return;
	}
	if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
		content.erase(find_if(content.rbegin(), content.rend(), [](natmax value) { return value != 0; }).base(), content.end());
		if (content.empty()) {
			content.push_back(0);
		}
		if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
			content.push_back(0);
		}
	}
	else {
		content.erase(find_if(content.rbegin() + 1, content.rend(), [](natmax value) { return value != natmax_max; }).base(), content.end() - 1);
		if (content.size() > 1) {
			if (content[content.size() - 2] >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
				content.pop_back();
			}
		}
	}
}

// 在运行 += 函数时，当 right 的长度短于自身时，应调用此函数进行进位的传播
static void propagate_carry_in_increase(span<natmax>&& parts, nat8& carry) noexcept
{
	// 前置条件: !parts.empty()
	if (carry == 0) {
		return;
	}
	// 满足 carry = 1
	for (sizevalue i = 0; i < parts.size(); ++i) {
		parts[i] += carry;
		if (parts[i] != 0) {
			carry = 0;
			break;
		}
	}
	// 后置条件: (parts <- parts + carry, carry <- 0) 或者 (parts <- parts + carry - U, carry <- 1)
}

void integer_number::operator+=(const integer_number& right) noexcept
{
	if (content.empty() || right.content.empty()) {
		return;
	}
	auto iterator_of_right = right.content.begin();
	nat8 carry = 0; // 进位
	sizevalue max_length = max(content.size(), right.content.size());
	content.resize(max_length, content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0 ? 0 : natmax_max);
	bool sign_is_different = content.back() >> (sizeof(natmax) * WORD_SIZE - 1) != right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1);
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
		if (*it < buffer || (last_carry == 1 && *it == buffer)) {
			carry = 1; // 使下次加法额外加1 (若还有下次加法)
		}
		// carry <- 0 (当不产生进位时)
		// carry <- 1 (当产生进位时)
		++iterator_of_right;
	}
	// 处理符号相同时计算导致符号变号的情况
	if (!sign_is_different) {
		if (right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0 && content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
			content.push_back(0);
		}
		else if (right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1 && content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
			content.push_back(natmax_max);
		}
	}
	clear_invalid_bits(content);
}

// 在运行 -= 函数时，当 right 的长度短于自身时，应调用此函数进行借位的传播
static void propagate_borrow_in_decrease(span<natmax>&& parts, nat8& borrow) noexcept
{
	// 前置条件: !parts.empty()
	if (borrow == 0) {
		return;
	}
	// 满足 borrow = 1
	for (sizevalue i = 0; i < parts.size(); ++i) {
		parts[i] -= borrow;
		if (parts[i] != natmax_max) {
			borrow = 0;
			break;
		}
	}
	// 后置条件: (parts <- parts - borrow, borrow <- 0) 或者 (parts <- parts - borrow + U, borrow <- 1)
}

void integer_number::operator-=(const integer_number& right) noexcept
{
	if (content.empty() || right.content.empty()) {
		return;
	}
	auto iterator_of_right = right.content.begin();
	nat8 borrow = 0; // 借位
	sizevalue max_length = max(content.size(), right.content.size());
	content.resize(max_length, content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0 ? 0 : natmax_max);
	bool sign_is_different = content.back() >> (sizeof(natmax) * WORD_SIZE - 1) != right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1);
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
		if (*it > buffer || (last_borrow == 1 && *it == buffer)) {
			borrow = 1; // 使下次减法额外减1（若还有下次减法）
		}
		// borrow <- 0 (当不产生借位时)
		// borrow <- 1 (当产生借位时)
		++iterator_of_right;
	}
	// 处理符号相异时计算导致符号变号的情况
	if (sign_is_different) {
		if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
			content.push_back(0);
		}
		else if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
			content.push_back(natmax_max);
		}
	}
	clear_invalid_bits(content);
}

// 在运行 *= 函数时，当处理中间数据时，应调用此函数进行进位的传播
static void propagate_carry_in_multiply(span<nathalf>&& parts, nathalf& carry) noexcept
{
	// 前置条件: !parts.empty()
	if (carry == 0) {
		return;
	}
	// 满足 carry = 1
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

void integer_number::operator*=(const integer_number& right) noexcept
{
	if (content.empty() || right.content.empty()) {
		return;
	}
	if (content.size() == 1 && right.content.size() == 1 && content.front() <= nat32_max && right.content.front() <= nat32_max) {
		content.front() *= right.content.front();
		return;
	}

	bool sign_is_different = content.back() >> (sizeof(natmax) * WORD_SIZE - 1) != right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1);
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
	copy(final_intermediate_data.data(), final_intermediate_data.data() + final_intermediate_data.size(), content.data());
	if (!sign_is_different && content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		content.push_back(0);
	}
	else if (sign_is_different && content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
		content.push_back(natmax_max);
	}
	clear_invalid_bits(content);
}

void integer_number::operator/=(const integer_number& right)
{
	// 如果 right 的值为0，则因为任何数除0在数学中都是未定义的，抛出异常
	if (all_of(right.content.begin(), right.content.end(), [](natmax n) { return n == 0; })) {
		throw runtime_error("不能除0");
	}
	if (content.empty() || right.content.empty()) {
		return;
	}
	// 当确定此对象的值与参数对象的值的长度都为1时，只需进行1次计算即可
	if (content.size() == 1 && right.content.size() == 1) {
		intmax temp = (intmax)content.front();
		temp /= (intmax)right.content.front();
		content.front() = (natmax)temp;
		return;
	}
	bool sign_is_different = content.back() >> (sizeof(natmax) * WORD_SIZE - 1) != right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1);
	if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		for (sizevalue i = 0; i < content.size(); ++i) {
			content[i] = ~content[i];
		}
		nat8 carry = 1;
		propagate_carry_in_increase(span<natmax>(content.data(), content.size()), carry);
	}
	span<natmax> right_content_span((natmax*)(right.content.data()), right.content.size());
	vector<natmax> temporary_content{};
	if (right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		temporary_content = right.content;
		for (sizevalue i = 0; i < temporary_content.size(); ++i) {
			temporary_content[i] = ~temporary_content[i];
		}
		nat8 carry = 1;
		propagate_carry_in_increase(span<natmax>(temporary_content.data(), temporary_content.size()), carry);
		right_content_span = span<natmax>(temporary_content.data(), temporary_content.size());
	}
	// 否则以二进制的形式相除
	content = div_value_by_value(span<natmax>(content.data(), content.size()), right_content_span);
	if (!sign_is_different && content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		content.push_back(0);
	}
	else if (sign_is_different) {
		nat8 borrow = 1;
		propagate_borrow_in_decrease(span<natmax>(content.data(), content.size()), borrow);
		for (sizevalue i = 0; i < content.size(); ++i) {
			content[i] = ~content[i];
		}
		if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
			content.push_back(natmax_max);
		}
	}
}

void integer_number::operator%=(const integer_number& right)
{
	// 如果 right 的值为0，则因为任何数除0在数学中都是未定义的（求余数需要相除），抛出异常
	if (all_of(right.content.begin(), right.content.end(), [](natmax n) { return n == 0; })) {
		throw runtime_error("不能除0");
	}
	if (content.empty() || right.content.empty()) {
		return;
	}
	// 当确定此对象的值与参数对象的值的长度都为1时，只需进行1次计算即可
	if (content.size() == 1 && right.content.size() == 1) {
		intmax temp = (intmax)content.front();
		temp %= (intmax)right.content.front();
		content.front() = (natmax)temp;
		return;
	}
	bool sign_is_negative = content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
	if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		for (sizevalue i = 0; i < content.size(); ++i) {
			content[i] = ~content[i];
		}
		nat8 carry = 1;
		propagate_carry_in_increase(span<natmax>(content.data(), content.size()), carry);
	}
	span<natmax> right_content_span((natmax*)(right.content.data()), right.content.size());
	vector<natmax> temporary_content{};
	if (right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		temporary_content = right.content;
		for (sizevalue i = 0; i < temporary_content.size(); ++i) {
			temporary_content[i] = ~temporary_content[i];
		}
		nat8 carry = 1;
		propagate_carry_in_increase(span<natmax>(temporary_content.data(), temporary_content.size()), carry);
		right_content_span = span<natmax>(temporary_content.data(), temporary_content.size());
	}
	// 否则以二进制的形式相除，取相除时得到的余数
	content = mod_value_by_value(span<natmax>(content.data(), content.size()), right_content_span);
	if (sign_is_negative && !(content.size() == 1 && content.back() == 0)) {
		*this -= right;
	}
}

integer_number integer_number::operator+(const integer_number& right) const noexcept
{
	integer_number result = *this;
	result += right;
	return std::move(result);
}

integer_number integer_number::operator-(const integer_number& right) const noexcept
{
	integer_number result = *this;
	result -= right;
	return std::move(result);
}

integer_number integer_number::operator*(const integer_number& right) const noexcept
{
	integer_number result = *this;
	result *= right;
	return std::move(result);
}

integer_number integer_number::operator/(const integer_number& right) const
{
	integer_number result = *this;
	result /= right;
	return std::move(result);
}

integer_number integer_number::operator%(const integer_number& right) const
{
	integer_number result = *this;
	result %= right;
	return std::move(result);
}

bool integer_number::operator==(const integer_number& right) const noexcept
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

bool integer_number::operator<(const integer_number& right) const noexcept
{
	if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		return false;
	}
	else if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
		return true;
	}
	sizevalue min_size = min(content.size(), right.content.size());
	if (content.size() < right.content.size()) {
		return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0;
	}
	else if (content.size() > right.content.size()) {
		return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
	}
	for (nat64 i = min_size - 1; i < min_size; --i) {
		if (content[i] < right.content[i]) {
			return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0;
		}
		if (content[i] > right.content[i]) {
			return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
		}
	}
	return false;
}

bool integer_number::operator>(const integer_number& right) const noexcept
{
	if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		return true;
	}
	else if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
		return false;
	}
	sizevalue min_size = min(content.size(), right.content.size());
	if (content.size() < right.content.size()) {
		return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
	}
	else if (content.size() > right.content.size()) {
		return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0;
	}
	for (nat64 i = min_size - 1; i < min_size; --i) {
		if (content[i] < right.content[i]) {
			return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
		}
		if (content[i] > right.content[i]) {
			return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0;
		}
	}
	return false;
}

bool integer_number::operator<=(const integer_number& right) const noexcept
{
	if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		return false;
	}
	else if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
		return true;
	}
	sizevalue min_size = min(content.size(), right.content.size());
	if (content.size() < right.content.size()) {
		return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0;
	}
	else if (content.size() > right.content.size()) {
		return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
	}
	for (nat64 i = min_size - 1; i < min_size; --i) {
		if (content[i] < right.content[i]) {
			return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0;
		}
		if (content[i] > right.content[i]) {
			return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
		}
	}
	return true;
}

bool integer_number::operator>=(const integer_number& right) const noexcept
{
	if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		return true;
	}
	else if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1 && right.content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0) {
		return false;
	}
	sizevalue min_size = min(content.size(), right.content.size());
	if (content.size() < right.content.size()) {
		return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
	}
	else if (content.size() > right.content.size()) {
		return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0;
	}
	for (nat64 i = min_size - 1; i < min_size; --i) {
		if (content[i] < right.content[i]) {
			return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1;
		}
		if (content[i] > right.content[i]) {
			return content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 0;
		}
	}
	return true;
}

integer_number natural_to_integer(span<natmax> content) noexcept
{
	if (content.empty()) {
		return integer_number{};
	}
	vector<natmax> result{ content.begin(), content.end() };
	if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		result.push_back(0);
	}
	return std::move(integer_number(result));
}

integer_number natural_to_integer(vector<natmax> content) noexcept
{
	if (content.empty()) {
		return integer_number{};
	}
	vector<natmax> result{ content.begin(), content.end() };
	if (content.back() >> (sizeof(natmax) * WORD_SIZE - 1) == 1) {
		result.push_back(0);
	}
	return std::move(integer_number(result));
}