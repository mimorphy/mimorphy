#include <basic>
#include <exception>
#include <runtime-exception>
#include <context>
#include <fstream>
#include <filesystem>
#include <iostream>
#include <regex>

namespace fs = std::filesystem;

bool save_as_lean(const byte_array& filepath, const fs::path& output_path, const byte_array& content);
void exectute(byte_array& content);
void replace_content(byte_array& content, replace_command& cmd);

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

        if (save_as_lean(filepath, output_path, content)) {
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
bool save_as_lean(const byte_array& filepath, const fs::path& output_path, const byte_array& content)
{
    try {
        // 创建Lean文件夹
        if (!create_output_directory(output_path)) {
            return false;
        }
        
        // 获取原始文件名（不含路径）
        fs::path original_path(filepath);
        byte_array original_name = original_path.filename().string();
        
        // 替换后缀为.lean
        fs::path lean_path = output_path / original_name;
        lean_path.replace_extension(".lean");
        
        // 保存文件
        std::ofstream out_file(lean_path, std::ios::binary);
        if (!out_file) {
            std::cerr << "错误：无法创建文件 " << lean_path << std::endl;
            return false;
        }
        
        out_file.write(content.c_str(), content.size());
        out_file.close();
        
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
            replace_content(content, *static_cast<replace_command*>(cmdv.ptr.get()));
            break;
        }
    }
}

byte_array expand_target(byte_array& content, std::vector<std::pair<sizevalue, sizevalue>>& captures, byte_array& target);

// 替换命令的执行
void replace_content(byte_array& content, replace_command& cmd)
{   
    // 查找所有匹配
    std::regex re(cmd.pattern);
    std::vector<std::pair<sizevalue, sizevalue>> matches;  // 位置和长度
    std::vector<std::vector<std::pair<sizevalue, sizevalue>>> captures;  // 每个匹配的捕获组
    
    auto begin = std::sregex_iterator(content.begin(), content.end(), re);
    auto end = std::sregex_iterator();
    
    for (auto it = begin; it != end; ++it) {
        const std::smatch& match = *it;
        
        // 主匹配
        sizevalue pos = match.position();
        sizevalue length = match.length();
        matches.emplace_back(pos, length);
        
        // 处理捕获组
        std::vector<std::pair<sizevalue, sizevalue>> match_captures;
        for (sizevalue i = 1; i < match.size(); ++i) {  // i=0是整个匹配
            if (match[i].matched) {
                match_captures.emplace_back(match.position(i), match.length(i));
            } else {
                match_captures.emplace_back(byte_array::npos, 0);  // 未匹配的捕获组
            }
        }
        captures.push_back(std::move(match_captures));
    }

    for (sizevalue i = matches.size() - 1; i != sizevalue_max; --i) {
        auto& match = matches[i];
        byte_array expanded_target = expand_target(content, captures[i], cmd.target);
        content.replace(match.first, match.second, expanded_target);
    }
}

// 展开 replace_command::target 中的 "#...#" 内容
byte_array expand_target(byte_array& content, std::vector<std::pair<sizevalue, sizevalue>>& captures, byte_array& target)
{
    byte_array expanded_target = target;
    std::regex re(R"(#(\d+)#)");
    std::vector<std::pair<sizevalue, sizevalue>> matches;  // 位置和长度
    std::vector<std::vector<std::pair<sizevalue, sizevalue>>> number_captures;  // 每个匹配的捕获组
    
    auto begin = std::sregex_iterator(expanded_target.begin(), expanded_target.end(), re);
    auto end = std::sregex_iterator();
    
    for (auto it = begin; it != end; ++it) {
        const std::smatch& match = *it;
        
        // 主匹配
        sizevalue pos = match.position();
        sizevalue length = match.length();
        matches.emplace_back(pos, length);
        
        // 处理捕获组
        std::vector<std::pair<sizevalue, sizevalue>> match_captures;
        for (sizevalue i = 1; i < match.size(); ++i) {  // i=0是整个匹配
            if (match[i].matched) {
                match_captures.emplace_back(match.position(i), match.length(i));
            } else {
                match_captures.emplace_back(byte_array::npos, 0);  // 未匹配的捕获组
            }
        }
        number_captures.push_back(std::move(match_captures));
    }

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