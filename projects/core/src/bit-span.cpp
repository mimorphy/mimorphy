#include <bit-span>
#include <cstddef>
#include <stdexcept>

// 构造函数
bit_span::bit_span() noexcept : data_(nullptr), bit_offset_(0), size_in_bits_(0) {}
bit_span::bit_span(pointer data, size_type bit_offset, size_type size_in_bits)
    : data_(data), bit_offset_(bit_offset), size_in_bits_(size_in_bits) {
    if (bit_offset_ >= 8) {
        throw std::out_of_range("构造 bit_span 时参数 bit_offset 必须在范围 [0, 7] 中");
    }
}
bit_span::bit_span(const bit_span& right) : data_(right.data_), bit_offset_(right.bit_offset_), size_in_bits_(right.size_in_bits_) {}
bit_span::bit_span(bit_span&& right) : data_(right.data_), bit_offset_(right.bit_offset_), size_in_bits_(right.size_in_bits_) {}

bit_span::bit_span(iterator first, iterator last) {
    if (first == last) {
        // 空范围
        data_ = nullptr;
        bit_offset_ = 0;
        size_in_bits_ = 0;
        return;
    }

    // 获取起始位置
    data_ = first.byte_ptr();
    bit_offset_ = first.bit_offset();

    // 计算范围大小
    size_in_bits_ = static_cast<size_type>(last - first);

    // 验证范围有效性
    if (last.byte_ptr() < data_) {
        throw std::invalid_argument("Invalid iterator range: last before first");
    }

    // 检查结束位置是否超出范围
    const size_type end_byte = last.byte_ptr() - data_;
    const size_type end_bit_offset = last.bit_offset();
    const size_type max_bits = (end_byte * 8) + end_bit_offset - bit_offset_;

    if (size_in_bits_ > max_bits) {
        throw std::out_of_range("Iterator range exceeds valid bit range");
    }
}

bit_span::bit_span(const_iterator first, const_iterator last) {
    if (first == last) {
        // 空范围
        data_ = nullptr;
        bit_offset_ = 0;
        size_in_bits_ = 0;
        return;
    }

    // 获取起始位置
    data_ = const_cast<pointer>(first.byte_ptr()); // 移除const限定
    bit_offset_ = first.bit_offset();

    // 计算范围大小
    size_in_bits_ = static_cast<size_type>(last - first);

    // 验证范围有效性
    if (last.byte_ptr() < data_) {
        throw std::invalid_argument("Invalid iterator range: last before first");
    }

    // 检查结束位置是否超出范围
    const size_type end_byte = last.byte_ptr() - data_;
    const size_type end_bit_offset = last.bit_offset();
    const size_type max_bits = (end_byte * 8) + end_bit_offset - bit_offset_;

    if (size_in_bits_ > max_bits) {
        throw std::out_of_range("Iterator range exceeds valid bit range");
    }
}

void bit_span::operator=(const bit_span& right) {
    data_ = right.data_;
    bit_offset_ = right.bit_offset_;
    size_in_bits_ = right.size_in_bits_;
}

void bit_span::operator=(bit_span&& right) {
    data_ = right.data_;
    bit_offset_ = right.bit_offset_;
    size_in_bits_ = right.size_in_bits_;
}

// 迭代器接口
bit_span::iterator bit_span::begin() noexcept {
    return iterator(data_, bit_offset_);
}
bit_span::const_iterator bit_span::begin() const noexcept {
    return const_iterator(data_, bit_offset_);
}
bit_span::const_iterator bit_span::cbegin() const noexcept {
    return begin();
}

bit_span::iterator bit_span::end() noexcept {
    return begin() + size_in_bits_;
}
bit_span::const_iterator bit_span::end() const noexcept {
    return begin() + size_in_bits_;
}
bit_span::const_iterator bit_span::cend() const noexcept {
    return end();
}

// 反向迭代器
bit_span::reverse_iterator bit_span::rbegin() noexcept {
    return reverse_iterator(end());
}
bit_span::const_reverse_iterator bit_span::rbegin() const noexcept {
    return const_reverse_iterator(end());
}
bit_span::const_reverse_iterator bit_span::crbegin() const noexcept {
    return rbegin();
}

bit_span::reverse_iterator bit_span::rend() noexcept {
    return reverse_iterator(begin());
}
bit_span::const_reverse_iterator bit_span::rend() const noexcept {
    return const_reverse_iterator(begin());
}
bit_span::const_reverse_iterator bit_span::crend() const noexcept {
    return rend();
}

// 元素访问
bit_span::reference bit_span::front() {
    return *begin();
}
bit_span::const_reference bit_span::bit_span::front() const {
    return *begin();
}

bit_span::reference bit_span::back() {
    return *(begin() + (size_in_bits_ - 1));
}
bit_span::const_reference bit_span::back() const {
    return *(begin() + (size_in_bits_ - 1));
}

bit_span::reference bit_span::operator[](size_type idx) {
    return *(begin() + idx);
}
bit_span::const_reference bit_span::operator[](size_type idx) const {
    return *(begin() + idx);
}

bit_span::reference bit_span::at(size_type idx) {
    if (idx >= size_in_bits_) {
        throw std::out_of_range("bit_span index out of range");
    }
    return (*this)[idx];
}
bit_span::const_reference bit_span::at(size_type idx) const {
    if (idx >= size_in_bits_) {
        throw std::out_of_range("bit_span index out of range");
    }
    return (*this)[idx];
}

// 容量相关
bit_span::pointer bit_span::data() const noexcept {
    return data_;
}

bit_span::size_type bit_span::size() const noexcept {
    return size_in_bits_;
}

bit_span::size_type bit_span::size_bytes() const noexcept {
    return (size_in_bits_ + bit_offset_ + 7) / 8;
}

bool bit_span::empty() const noexcept {
    return size_in_bits_ == 0;
}

// 子视图
bit_span bit_span::first(size_type n) const {
    if (n > size_in_bits_) {
        throw std::out_of_range("bit_span::first: n exceeds size");
    }
    return bit_span(data_, bit_offset_, n);
}

bit_span bit_span::last(size_type n) const {
    if (n > size_in_bits_) {
        throw std::out_of_range("bit_span::last: n exceeds size");
    }
    // 计算新起始位置
    size_type total_bits = bit_offset_ + (size_in_bits_ - n);
    size_type new_byte_offset = total_bits / 8;
    size_type new_bit_offset = total_bits % 8;
    return bit_span(data_ + new_byte_offset, new_bit_offset, n);
}

bit_span bit_span::subspan(size_type offset, size_type count) const {
    if (offset > size_in_bits_) {
        throw std::out_of_range("bit_span::subspan: offset exceeds size");
    }
    size_type actual_count = (count == dynamic_extent) ? (size_in_bits_ - offset) : count;
    if (offset + actual_count > size_in_bits_) {
        throw std::out_of_range("bit_span::subspan: offset+count exceeds size");
    }

    // 计算新起始位置
    size_type total_bits = bit_offset_ + offset;
    size_type new_byte_offset = total_bits / 8;
    size_type new_bit_offset = total_bits % 8;
    return bit_span(data_ + new_byte_offset, new_bit_offset, actual_count);
}

// bit_reference 实现
bit_reference::bit_reference(unsigned char* byte_ptr, size_t bit_pos) noexcept : byte_ptr_(byte_ptr), bit_pos_(bit_pos) {}

// 转换为 bool (读取比特值)
bit_reference::operator bool() const noexcept {
    return (*byte_ptr_ >> bit_pos_) & 1;
}

// 赋值操作 (设置比特值)
bit_reference& bit_reference::operator=(bool value) noexcept {
    if (value) {
        *byte_ptr_ |= (1 << bit_pos_); // 置1
    }
    else {
        *byte_ptr_ &= ~(1 << bit_pos_); // 置0
    }
    return *this;
}

// 从另一个比特引用赋值
bit_reference& bit_reference::operator=(const bit_reference& other) noexcept {
*this = static_cast<bool>(other);
return *this;
}

// 翻转比特
void bit_reference::flip() noexcept {
*byte_ptr_ ^= (1 << bit_pos_);
}

// bit_iterator 实现
bit_iterator::bit_iterator(unsigned char* ptr, size_t bit_pos) noexcept
: byte_ptr_(ptr), bit_pos_(bit_pos) {}

// 解引用
bit_iterator::reference bit_iterator::operator*() const {
return bit_reference(byte_ptr_, bit_pos_);
}

// 前置递增
bit_iterator& bit_iterator::operator++() {
if (++bit_pos_ == 8) {
    bit_pos_ = 0;
    ++byte_ptr_;
}
return *this;
}

// 后置递增
bit_iterator bit_iterator::operator++(int) {
auto tmp = *this;
++(*this);
return tmp;
}

// 前置递减
bit_iterator& bit_iterator::operator--() {
if (bit_pos_ == 0) {
    bit_pos_ = 7;
    --byte_ptr_;
}
else {
    --bit_pos_;
}
return *this;
}

// 后置递减
bit_iterator bit_iterator::operator--(int) {
auto tmp = *this;
--(*this);
return tmp;
}

// 随机访问：迭代器 + n
bit_iterator bit_iterator::operator+(difference_type n) const {
if (n == 0) return *this;
difference_type total_bits = static_cast<difference_type>(bit_pos_) + n;
difference_type byte_advance = total_bits / 8;
bit_span::size_type new_bit_pos = total_bits % 8;
if (new_bit_pos < 0) {
    new_bit_pos += 8;
    --byte_advance;
}
return bit_iterator(byte_ptr_ + byte_advance, new_bit_pos);
}

// 随机访问：n + 迭代器
bit_iterator operator+(bit_iterator::difference_type n, const bit_iterator& it) {
    return it + n;
}

// 随机访问：迭代器 - n
bit_iterator bit_iterator::operator-(difference_type n) const {
    return *this + (-n);
}

// 迭代器差值
bit_iterator::difference_type bit_iterator::operator-(const bit_iterator& other) const {
    difference_type byte_diff = (byte_ptr_ - other.byte_ptr_) * 8;
    return byte_diff + static_cast<difference_type>(bit_pos_) - static_cast<difference_type>(other.bit_pos_);
}

// 复合赋值 +=
bit_iterator& bit_iterator::operator+=(difference_type n) {
    *this = *this + n;
    return *this;
}

// 复合赋值 -=
bit_iterator& bit_iterator::operator-=(difference_type n) {
    *this = *this - n;
    return *this;
}

// 下标访问
bit_iterator::reference bit_iterator::operator[](difference_type n) const {
    return *(*this + n);
}

// 比较运算符
bool bit_iterator::operator==(const bit_iterator& other) const noexcept {
    return byte_ptr_ == other.byte_ptr_ && bit_pos_ == other.bit_pos_;
}

bool bit_iterator::operator!=(const bit_iterator& other) const noexcept {
    return !(*this == other);
}

bool bit_iterator::operator<(const bit_iterator& other) const noexcept {
    if (byte_ptr_ < other.byte_ptr_) return true;
    if (byte_ptr_ == other.byte_ptr_) return bit_pos_ < other.bit_pos_;
    return false;
}

bool bit_iterator::operator<=(const bit_iterator& other) const noexcept {
    return !(other < *this);
}

bool bit_iterator::operator>(const bit_iterator& other) const noexcept {
    return other < *this;
}

bool bit_iterator::operator>=(const bit_iterator& other) const noexcept {
    return !(*this < other);
}

// const_bit_iterator 实现
const_bit_iterator::const_bit_iterator(const unsigned char* ptr, size_t bit_pos) noexcept
    : byte_ptr_(ptr), bit_pos_(bit_pos) {}

// 从可变迭代器构造
const_bit_iterator::const_bit_iterator(const bit_iterator& other) noexcept
    : byte_ptr_(other.byte_ptr_), bit_pos_(other.bit_pos_) {}

// 解引用
const_bit_iterator::reference const_bit_iterator::operator*() const {
    return (*byte_ptr_ >> bit_pos_) & 1;
}

// 前置递增
const_bit_iterator& const_bit_iterator::operator++() {
    if (++bit_pos_ == 8) {
        bit_pos_ = 0;
        ++byte_ptr_;
    }
    return *this;
}

// 后置递增
const_bit_iterator const_bit_iterator::operator++(int) {
    auto tmp = *this;
    ++(*this);
    return tmp;
}

// 前置递减
const_bit_iterator& const_bit_iterator::operator--() {
    if (bit_pos_ == 0) {
        bit_pos_ = 7;
        --byte_ptr_;
    }
    else {
        --bit_pos_;
    }
    return *this;
}

// 后置递减
const_bit_iterator const_bit_iterator::operator--(int) {
    auto tmp = *this;
    --(*this);
    return tmp;
}

// 随机访问：迭代器 + n
const_bit_iterator const_bit_iterator::operator+(difference_type n) const {
    if (n == 0) return *this;
    difference_type total_bits = static_cast<difference_type>(bit_pos_) + n;
    difference_type byte_advance = total_bits / 8;
    bit_span::size_type new_bit_pos = total_bits % 8;
    if (new_bit_pos < 0) {
        new_bit_pos += 8;
        --byte_advance;
    }
    return const_bit_iterator(byte_ptr_ + byte_advance, new_bit_pos);
}

// 随机访问：n + 迭代器
const_bit_iterator operator+(const_bit_iterator::difference_type n, const const_bit_iterator& it) {
    return it + n;
}

// 随机访问：迭代器 - n
const_bit_iterator const_bit_iterator::operator-(difference_type n) const {
    return *this + (-n);
}

// 迭代器差值
const_bit_iterator::difference_type const_bit_iterator::operator-(const const_bit_iterator& other) const {
    difference_type byte_diff = (byte_ptr_ - other.byte_ptr_) * 8;
    return byte_diff + static_cast<difference_type>(bit_pos_) - static_cast<difference_type>(other.bit_pos_);
}

// 复合赋值 +=
const_bit_iterator& const_bit_iterator::operator+=(difference_type n) {
    *this = *this + n;
    return *this;
}

// 复合赋值 -=
const_bit_iterator& const_bit_iterator::operator-=(difference_type n) {
    *this = *this - n;
    return *this;
}

// 下标访问
const_bit_iterator::reference const_bit_iterator::operator[](difference_type n) const {
    return *(*this + n);
}

// 比较运算符
bool const_bit_iterator::operator==(const const_bit_iterator& other) const noexcept {
    return byte_ptr_ == other.byte_ptr_ && bit_pos_ == other.bit_pos_;
}

bool const_bit_iterator::operator!=(const const_bit_iterator& other) const noexcept {
    return !(*this == other);
}

bool const_bit_iterator::operator<(const const_bit_iterator& other) const noexcept {
    if (byte_ptr_ < other.byte_ptr_) return true;
    if (byte_ptr_ == other.byte_ptr_) return bit_pos_ < other.bit_pos_;
    return false;
}

bool const_bit_iterator::operator<=(const const_bit_iterator& other) const noexcept {
    return !(other < *this);
}

bool const_bit_iterator::operator>(const const_bit_iterator& other) const noexcept {
    return other < *this;
}

bool const_bit_iterator::operator>=(const const_bit_iterator& other) const noexcept {
    return !(*this < other);
}