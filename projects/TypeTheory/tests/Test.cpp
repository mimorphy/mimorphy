#include "Basic"
#include "FixedLengthString"
#include "LambdaCalculus"
#include "map"
#include "iostream"

using std::map;

int32 main()
{
	map<str, lambda_expression> defintions{};
	defintions[STR("TRUE").data()] = lambda_expression(STR("λx. λy. x").data());
	defintions[STR("FALSE").data()] = lambda_expression(STR("λx. λy. y").data());
	defintions[STR("AND").data()] = lambda_expression(STR("λp. λq. p q FALSE").data());
	bool is_equal = defintions[STR("TRUE").data()] == defintions[STR("FALSE").data()];
	auto lambda0 = lambda_expression(STR("AND FALSE q").data());
	lambda0.applicate(defintions);
	str result = lambda0.get();
	std::cout << variable_length(result) << std::endl;
	return 0;
}