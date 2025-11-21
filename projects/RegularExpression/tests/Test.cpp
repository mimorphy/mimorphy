#include "Basic"
#include "BuildNFA"
#include "FixedLengthString"
// #include "iostream"
// #include "string"

int32 main()
{
    NFA nfa = build_nfa(STR("xyz(123|456)(甲乙|丙丁)😊").data());
    // std::cout << std::to_string(stt.transition_condition) << std::endl;
	return 0;
}