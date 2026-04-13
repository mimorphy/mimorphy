#include <basic>
#include <fixed-length-string>
#include <runtime-exception>
#include <state-transition>
#include <build-regular-table>
#include <test-building-cases>
#include <test-length-cases>
#include <iostream>
#include <chrono>

int32 main()
{
    auto start = std::chrono::steady_clock::now();
    std::cout << variable_length(test_building_cases()) << std::endl;
    auto end = std::chrono::steady_clock::now();
    std::cout << "构建正则表测试用时：" << end - start << std::endl;
    start = std::chrono::steady_clock::now();
    std::cout << variable_length(test_length_cases()) << std::endl;
    end = std::chrono::steady_clock::now();
    std::cout << "计算长度测试用时：" << end - start << std::endl;
    start = std::chrono::steady_clock::now();
    expression_information r = build_expression_information(fixed_length(R"(\~\(abc\))"), functional_operations, INDEX_OF_MAIN_EXCEPTIONS);
    if (length_of_exception_pool(INDEX_OF_MAIN_EXCEPTIONS) != 0) {
        std::cout << information_of_exception_pool_by_index(INDEX_OF_MAIN_EXCEPTIONS, 0) << std::endl;
    }
    end = std::chrono::steady_clock::now();
    std::cout << "临时测试用时：" << end - start << std::endl;
    return 0;
}