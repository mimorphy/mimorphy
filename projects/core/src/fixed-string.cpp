#include <fixed-string>

// 重载版本：接受 byte_array 参数
str fixed_length(const byte_array& bstr)
{
	str result;

	sizevalue i = 0;
	sizevalue len = bstr.length();

	while (i < len) {
		unsigned char c = static_cast<unsigned char>(bstr[i]);
		char32_t cp = 0;

		if (c < 0x80) {
			cp = c;
			i += 1;
		}
		else if ((c & 0xE0) == 0xC0 && i + 1 < len) {
			unsigned char c2 = static_cast<unsigned char>(bstr[i + 1]);
			cp = ((c & 0x1F) << 6) | (c2 & 0x3F);
			i += 2;
		}
		else if ((c & 0xF0) == 0xE0 && i + 2 < len) {
			unsigned char c2 = static_cast<unsigned char>(bstr[i + 1]);
			unsigned char c3 = static_cast<unsigned char>(bstr[i + 2]);
			cp = ((c & 0x0F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
			i += 3;
		}
		else if ((c & 0xF8) == 0xF0 && i + 3 < len) {
			unsigned char c2 = static_cast<unsigned char>(bstr[i + 1]);
			unsigned char c3 = static_cast<unsigned char>(bstr[i + 2]);
			unsigned char c4 = static_cast<unsigned char>(bstr[i + 3]);
			cp = ((c & 0x07) << 18) | ((c2 & 0x3F) << 12) |
				((c3 & 0x3F) << 6) | (c4 & 0x3F);
			i += 4;
		}
		else {
			cp = 0xFFFD;
			i += 1;
		}

		result.push_back(cp);
	}

	return result;
}

// 重载版本：接受 C 风格字符串指针
str fixed_length(const char* cstr)
{
	if (!cstr) return str();
	return fixed_length(byte_array(cstr));
}

// 重载版本：接受指针和长度
str fixed_length(const char* cstr, sizevalue len)
{
	if (!cstr) return str();
	return fixed_length(byte_array(cstr, len));
}

// 将定长字符串转换成字节串
byte_array variable_length(const str& u32str)
{
	// 先计算需要的字节数
	sizevalue byte_count = 0;
	for (char32_t cp : u32str) {
		if (cp <= 0x7F) byte_count += 1;
		else if (cp <= 0x7FF) byte_count += 2;
		else if (cp <= 0xFFFF) {
			if (cp >= 0xD800 && cp <= 0xDFFF) {
				byte_count += 3; // 替换字符的长度
			}
			else {
				byte_count += 3;
			}
		}
		else byte_count += 4;
	}

	byte_array result;
	result.resize(byte_count);

	sizevalue pos = 0;
	for (char32_t cp : u32str) {
		if (cp <= 0x7F) {
			result[pos++] = static_cast<char>(cp);
		}
		else if (cp <= 0x7FF) {
			result[pos++] = static_cast<char>(0xC0 | ((cp >> 6) & 0x1F));
			result[pos++] = static_cast<char>(0x80 | (cp & 0x3F));
		}
		else if (cp <= 0xFFFF) {
			if (cp >= 0xD800 && cp <= 0xDFFF) {
				// 替换字符
				result[pos++] = (char)0xEF;
				result[pos++] = (char)0xBF;
				result[pos++] = (char)0xBD;
			}
			else {
				result[pos++] = static_cast<char>(0xE0 | ((cp >> 12) & 0x0F));
				result[pos++] = static_cast<char>(0x80 | ((cp >> 6) & 0x3F));
				result[pos++] = static_cast<char>(0x80 | (cp & 0x3F));
			}
		}
		else {
			result[pos++] = static_cast<char>(0xF0 | ((cp >> 18) & 0x07));
			result[pos++] = static_cast<char>(0x80 | ((cp >> 12) & 0x3F));
			result[pos++] = static_cast<char>(0x80 | ((cp >> 6) & 0x3F));
			result[pos++] = static_cast<char>(0x80 | (cp & 0x3F));
		}
	}

	return result;
}