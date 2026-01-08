#include <basic>
#include <exception>
#include <runtime-exception>
#include <context>
#include <fstream>
#include <filesystem>
#include <iostream>
#include <regex>
#include <utility>

using std::vector;
using std::pair;
namespace fs = std::filesystem;

bool save_as_lean(const byte_array& filepath, const fs::path& output_path, const byte_array& content, vector<byte_array>& saved_file_names);
void exectute(byte_array& content);
byte_array replace_content(byte_array content, commmand_value& cmd);

// 读取传入参数中的文件路径，并尝试打开文件获取内容，若成功获取，尝试进行处理
int32 main(int32 argc, char* argv[])
{
    if (argc < 2) {
        std::cerr << "用法: " << argv[0] << " <文件1> [文件2 ...]" << std::endl;
        return 1;
    }

    fs::path output_path = "./Lean";
    // 尝试寻找"-o"选项并更改输出目录
    for (int i = 1; i < argc; ++i) {
        if (byte_array(argv[i]) == "-o") {
            ++i;
            if (i >= argc) {
                std::cerr << "错误：\"-o\" 参数不存在后继参数" << std::endl;
                return 1;
            }
            output_path = argv[i];
            if (!fs::is_directory(output_path)) {
                std::cerr << "警告：\"-o\" 参数的后继参数必须是目录，而不能是文件——将使用默认目录\"./Lean\"输出" << std::endl;
                output_path = "./Lean";
            }
        }
    }
    
    // 提取文件并处理
    vector<byte_array> saved_file_names{};
    for (int i = 1; i < argc; ++i) {
        if (byte_array(argv[i]) == "-o") {
            ++i;
            continue;
        }

        byte_array filepath = argv[i];
        std::ifstream file(filepath, std::ios::binary);
        
        if (!file.is_open()) {
            std::cerr << "警告：无法打开文件 " << filepath << std::endl;
            continue;
        }
        
        // 读取文件
        file.seekg(0, std::ios::end);
        sizevalue size = file.tellg();
        file.seekg(0, std::ios::beg);
        
        byte_array content;
        content.resize(size);
        file.read(&content[0], size);
        file.close();
        
        exectute(content);

        if (save_as_lean(filepath, output_path, content, saved_file_names)) {
            std::cout << "文件转换成功！" << std::endl;
        } else {
            std::cerr << "文件转换失败！" << std::endl;
            return 1;
        }
    }
}

// 创建Lean文件夹（如果不存在）
bool create_output_directory(const fs::path& output_path)
{
    try {
        if (!fs::exists(output_path)) {
            if (fs::create_directory(output_path)) {
                std::cout << "创建输出文件夹" << std::endl;
            } else {
                std::cerr << "警告：无法创建输出文件夹" << std::endl;
                return false;
            }
        }
        return true;
    } catch (const std::exception& e) {
        std::cerr << "创建文件夹时出错: " << e.what() << std::endl;
        return false;
    }
}

// 修改文件后缀为.lean并保存到Lean文件夹
bool save_as_lean(const byte_array& filepath, const fs::path& output_path, const byte_array& content, vector<byte_array>& saved_file_names)
{
    try {
        // 创建Lean文件夹
        if (!create_output_directory(output_path)) {
            return false;
        }
        
        // 获取原始文件名（不含路径）
        fs::path original_path(filepath);
        byte_array original_name = original_path.filename().string();
        std::replace(original_name.begin(), original_name.end(), '-', '_'); // 将文件名中的 '-' 替换为 '_'
        
        // 替换后缀为.lean
        fs::path lean_path = output_path / original_name;
        lean_path.replace_extension(".lean");
        
        // 保存文件
        byte_array stem = lean_path.stem().string();
        // 根据是否已经保存过同名(省略后缀)文件来选择追加或覆盖模式
        std::ofstream out_file(lean_path, std::find_if(saved_file_names.begin(), saved_file_names.end(), [&stem](byte_array& s) { return s == stem; }) != saved_file_names.end() ? std::ios::binary | std::ios::app : std::ios::binary);
        if (!out_file) {
            std::cerr << "错误：无法创建文件 " << lean_path << std::endl;
            return false;
        }
        
        out_file.write(content.c_str(), content.size());
        out_file.close();

        saved_file_names.push_back(stem);
        
        std::cout << "已保存为: " << lean_path << std::endl;
        return true;
        
    } catch (const std::exception& e) {
        std::cerr << "保存文件时出错: " << e.what() << std::endl;
        return false;
    }
}

// 根据读入的文件内容，以及 context 中的 executable_list 执行命令
void exectute(byte_array& content)
{
    for (auto& cmdv : executable_list) {
        switch (cmdv.type) {
        case command_type::REPLACE_COMMAND:
            content = replace_content(content, cmdv);
            break;
        case command_type::DEFINE_COMMAND:
            break;
        }
    }
}

byte_array set_capture_of(byte_array s, pair<sizevalue, sizevalue>& position);
byte_array expand_target(byte_array& content, vector<pair<sizevalue, sizevalue>>& captures, byte_array& target);
byte_array expand_number_of_target(byte_array& content, vector<pair<sizevalue, sizevalue>>& captures, byte_array& target);
byte_array disable_all_captures(const byte_array& pattern);
byte_array expand_symbol_of_target(byte_array& target);
byte_array expand_symbol_once_of_target(byte_array& target);

// 进行匹配过程，结果反映在 matches 和 captures 中
void process_match(vector<pair<sizevalue, sizevalue>>& matches, vector<vector<pair<sizevalue, sizevalue>>>& captures, std::sregex_iterator begin, std::sregex_iterator end)
{
    for (auto it = begin; it != end; ++it) {
        const std::smatch& match = *it;
        
        // 主匹配
        sizevalue pos = match.position();
        sizevalue length = match.length();
        matches.emplace_back(pos, length);
        
        // 处理捕获组
        vector<pair<sizevalue, sizevalue>> match_captures;
        for (sizevalue i = 1; i < match.size(); ++i) {  // i=0是整个匹配
            if (match[i].matched) {
                match_captures.emplace_back(match.position(i), match.length(i));
            } else {
                match_captures.emplace_back(byte_array::npos, 0);  // 未匹配的捕获组
            }
        }
        captures.push_back(std::move(match_captures));
    }
}

// 替换命令的执行
byte_array replace_content(byte_array content, commmand_value& cmdv)
{ 
    // 查找所有匹配
    byte_array pattern = expand_symbol_of_target(cmdv.ptr->pattern);
    std::regex re(pattern);
    
    vector<pair<sizevalue, sizevalue>> matches;  // 位置和长度
    vector<vector<pair<sizevalue, sizevalue>>> captures;  // 每个匹配的捕获组
    
    auto begin = std::sregex_iterator(content.begin(), content.end(), re);
    auto end = std::sregex_iterator();
    
    process_match(matches, captures, begin, end);
    
    // 进行逐层子替换
    byte_array sub_content = disable_all_captures(expand_symbol_once_of_target(cmdv.ptr->pattern));
    re = R"(@([a-zA-Z_][a-zA-Z0-9_]*)#)";
    begin = std::sregex_iterator(sub_content.begin(), sub_content.end(), re);
    end = std::sregex_iterator();

    auto old_matches = std::move(matches);
    auto old_captures = std::move(captures);

    matches.clear();
    captures.clear();
    process_match(matches, captures, begin, end);

    // 最外层循环，遍历单层展开的 pattern 中的变量
    for (sizevalue i = captures.size() - 1; i != sizevalue_max; --i) {
        str name = fixed_length(sub_content.substr(captures[i][0].first, captures[i][0].second));
        runtime_assert(buffer.contains(name), "在展开\"" + sub_content + "\"的\"" + sub_content.substr(captures[i][0].first, captures[i][0].second) + "\"时，未发现存在对应的定义！");
        byte_array temp_pattern = set_capture_of(sub_content, captures[i][0]);
        std::regex temp_re(expand_symbol_of_target(temp_pattern));
        // 内层循环，遍历 content 中的每个匹配的子字符串
        for (sizevalue j = old_matches.size() - 1; j != sizevalue_max; --j) {
            vector<pair<sizevalue, sizevalue>> temp_matches;  // 位置和长度
            vector<vector<pair<sizevalue, sizevalue>>> temp_captures;  // 每个匹配的捕获组
            byte_array temp_content = content.substr(old_matches[j].first, old_matches[j].second); // 子字符串
            auto temp_begin = std::sregex_iterator(temp_content.begin(), temp_content.end(), temp_re);
            auto temp_end = std::sregex_iterator();
            process_match(temp_matches, temp_captures, temp_begin, temp_end);
            // 进行子替换
            auto replacement = replace_content(content.substr(old_matches[j].first + temp_captures[0][0].first, temp_captures[0][0].second), buffer[name]);
            content.replace(old_matches[j].first + temp_captures[0][0].first, temp_captures[0][0].second, replacement);
            // 更新索引
            old_matches[j].second += replacement.size() - temp_captures[0][0].second;
            old_captures[j][i].second += replacement.size() - temp_captures[0][0].second;
            for (sizevalue k = i + 1; k < old_captures[j].size(); ++k) {
                old_captures[j][k].first += replacement.size() - temp_captures[0][0].second;
            }
            for (sizevalue k = j + 1; k < old_matches.size(); ++k) {
                old_matches[k].first += replacement.size() - temp_captures[0][0].second;
                for (auto& old_capture : old_captures[k]) {
                    old_capture.first += replacement.size() - temp_captures[0][0].second;
                }
            }
        }
    }

    // 如果是替换指令，进行替换
    if (cmdv.type == command_type::REPLACE_COMMAND) {
        replace_command& cmd = *static_cast<replace_command*>(cmdv.ptr.get());
        // 进行替换
        for (sizevalue i = old_matches.size() - 1; i != sizevalue_max; --i) {
            auto& match = old_matches[i];
            byte_array expanded_target = expand_target(content, old_captures[i], cmd.target);
            content.replace(match.first, match.second, expanded_target);
        }
    }

    return std::move(content);
}

// 为 s 中名称位于 position 处的变量添加捕获修饰 (若之前没有)
byte_array set_capture_of(byte_array s, pair<sizevalue, sizevalue>& position)
{
    byte_array result = s;
    result.insert(position.first + position.second + 2, ")");
    result.insert(position.first - 1, "(");
    return std::move(result);
}

// 展开 replace_command::target 中的 "@...#" 内容
byte_array expand_target(byte_array& content, vector<pair<sizevalue, sizevalue>>& captures, byte_array& target)
{
    byte_array expanded_target = expand_number_of_target(content, captures, target);
    expanded_target = expand_symbol_of_target(expanded_target);
    return std::move(expanded_target);
}

// 展开 replace_command::target 中的 "@\d+#" 内容
byte_array expand_number_of_target(byte_array& content, vector<pair<sizevalue, sizevalue>>& captures, byte_array& target)
{
    byte_array expanded_target = target;
    std::regex re(R"(@(\d+)#)");
    vector<pair<sizevalue, sizevalue>> matches;  // 位置和长度
    vector<vector<pair<sizevalue, sizevalue>>> number_captures;  // 每个匹配的捕获组
    
    auto begin = std::sregex_iterator(expanded_target.begin(), expanded_target.end(), re);
    auto end = std::sregex_iterator();
    
    process_match(matches, number_captures, begin, end);

    for (sizevalue i = matches.size() - 1; i != sizevalue_max; --i) {
        auto& match = matches[i];
        sizevalue number = 0;
        try {
            number = std::stoll(expanded_target.substr(number_captures[i][0].first, number_captures[i][0].second));
        }
        catch (std::exception& e) {
            link_error(e, "在展开\"" + target + "\"的\"" + expanded_target.substr(match.first, match.second) + "\"时，其中的数字过大！(大于sizevalue_max)");
        }
        runtime_assert(number - 1 < captures.size(), "在展开\"" + target + "\"的\"" + expanded_target.substr(match.first, match.second) + "\"时，未发现存在对应的捕获组！");
        expanded_target.replace(match.first, match.second, content.substr(captures[number - 1].first, captures[number - 1].second));
    }

    return std::move(expanded_target);
}

// 将 pattern 中的所有捕获组改成非捕获组
byte_array disable_all_captures(const byte_array& pattern)
{
    byte_array result;
    result.reserve(pattern.length() + 20); // 预分配空间
    
    for (size_t i = 0; i < pattern.length(); ++i) {
        if (pattern[i] == '(') {
            // 检查前一个字符是否是反斜杠（转义情况）
            if (i > 0 && pattern[i-1] == '\\') {
                result += pattern[i];
                continue;
            }
            
            // 检查是否已经是特殊语法
            if (i + 1 < pattern.length()) {
                if (pattern[i+1] == '?') {
                    // 已经是 (?:, (?=, (?!, (?<=, (?<! 等
                    result += pattern[i];
                    result += pattern[i+1];
                    i++;
                    if (i + 1 < pattern.length() && pattern[i+1] == ':') {
                        result += pattern[++i]; // 非捕获组，保留
                    } else {
                        // 其他 (? 语法，保持原样
                        continue;
                    }
                } else {
                    // 普通捕获组，转换为非捕获组
                    result += "(?:";
                }
            } else {
                result += "(?:";
            }
        } else {
            result += pattern[i];
        }
    }
    
    return result;
}

// 展开 target 中的 "@{var}#" 内容直到无法展开，其中 var 指代任意定义名标识符
byte_array expand_symbol_of_target(byte_array& target)
{
    byte_array expanded_target = target;
    std::regex re(R"(@([a-zA-Z_][a-zA-Z0-9_]*)#)");
    vector<pair<sizevalue, sizevalue>> matches;  // 位置和长度
    vector<vector<pair<sizevalue, sizevalue>>> symbol_captures;  // 每个匹配的捕获组

    auto begin = std::sregex_iterator(expanded_target.begin(), expanded_target.end(), re);
    auto end = std::sregex_iterator();
    
    process_match(matches, symbol_captures, begin, end);

    // 展开内容
    for (sizevalue i = matches.size() - 1; i != sizevalue_max; --i) {
        auto& match = matches[i];
        str name = fixed_length(expanded_target.substr(symbol_captures[i][0].first, symbol_captures[i][0].second));
        runtime_assert(buffer.contains(name), "在展开\"" + target + "\"的\"" + expanded_target.substr(match.first, match.second) + "\"时，未发现存在对应的定义！");
        auto& cmdv = buffer[name];
        // 如果是定义指令或者替换指令，直接全部展开
        if (cmdv.type == command_type::DEFINE_COMMAND || cmdv.type == command_type::REPLACE_COMMAND) {
            expanded_target.replace(match.first, match.second, disable_all_captures(expand_symbol_of_target(static_cast<define_command*>(cmdv.ptr.get())->pattern)));
        }
    }

    return std::move(expanded_target);
}

// 展开 target 中的 "@{var}#" 内容中的顶层，其中 var 指代任意定义名标识符
byte_array expand_symbol_once_of_target(byte_array& target)
{
    byte_array expanded_target = target;
    std::regex re(R"(@([a-zA-Z_][a-zA-Z0-9_]*)#)");
    vector<pair<sizevalue, sizevalue>> matches;  // 位置和长度
    vector<vector<pair<sizevalue, sizevalue>>> symbol_captures;  // 每个匹配的捕获组

    auto begin = std::sregex_iterator(expanded_target.begin(), expanded_target.end(), re);
    auto end = std::sregex_iterator();
    
    process_match(matches, symbol_captures, begin, end);

    // 展开内容
    for (sizevalue i = matches.size() - 1; i != sizevalue_max; --i) {
        auto& match = matches[i];
        str name = fixed_length(expanded_target.substr(symbol_captures[i][0].first, symbol_captures[i][0].second));
        runtime_assert(buffer.contains(name), "在展开\"" + target + "\"的\"" + expanded_target.substr(match.first, match.second) + "\"时，未发现存在对应的定义！");
        auto& cmdv = buffer[name];
        // 如果是定义指令或者替换指令，展开一层
        if (cmdv.type == command_type::DEFINE_COMMAND || cmdv.type == command_type::REPLACE_COMMAND) {
            expanded_target.replace(match.first, match.second, disable_all_captures(static_cast<define_command*>(cmdv.ptr.get())->pattern));
        }
    }

    return std::move(expanded_target);
}