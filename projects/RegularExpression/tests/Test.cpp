#include "Basic"
#include "FixedLengthString"
#include "TestCases"
#include "iostream"
#include "chrono"

int32 main()
{
    auto start = std::chrono::steady_clock::now();
    std::cout << variable_length(test_cases()) << std::endl;
    auto end = std::chrono::steady_clock::now();
    std::cout << "耗时: " << std::chrono::duration_cast<std::chrono::microseconds>(end - start) << std::endl;
	return 0;
}