#include "Basic"
#include "Cell"
#include "vector"
#include "iostream"

using std::vector;

int32 main()
{
    cell c1 = cell(vector<natmax>{0, 1}, vector<natmax>{3});
    cell c2 = cell(vector<natmax>{0, 1}, vector<natmax>{natmax_max});
    cell c3 = c1 + c2;
    cell c4 = c1 - c2;
    cell c5 = c1 * c2;
    cell c6 = c1 / c2;
    cell c7 = c1 % c2;
    std::cout << c5.content[0] << std::endl;
    return 0;
}