#include <basic>
#include <numerical-cell>
#include <vector>
#include <iostream>

using std::vector;

int32 main()
{
    NC c1 = NC(vector<natmax>{0, 1}, vector<natmax>{3});
    NC c2 = NC(vector<natmax>{0, 1}, vector<natmax>{natmax_max});
    NC c3 = c1 + c2;
    NC c4 = c1 - c2;
    NC c5 = c1 * c2;
    NC c6 = c1 / c2;
    NC c7 = c1 % c2;
    std::cout << c3.content[0] << std::endl;
    std::cout << c4.content[0] << std::endl;
    std::cout << c5.content[0] << std::endl;
    std::cout << c6.content[0] << std::endl;
    std::cout << c7.content[0] << std::endl;
    return 0;
}