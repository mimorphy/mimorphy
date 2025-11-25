#include "Basic"
#include "BuildNFA"
#include "FixedLengthString"
// #include "iostream"
// #include "string"

int32 main()
{
    NFA nfa = build_nfa(STR("A(123|(xyz)*)B").data());
    // std::cout << std::to_string(stt.transition_condition) << std::endl;
	return 0;
}