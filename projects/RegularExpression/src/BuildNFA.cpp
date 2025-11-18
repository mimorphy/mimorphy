#include "BuildNFA"
#include "Basic"
#include "FixedLengthString"
#include "RuntimeException"
#include "StateTransition"

static state_transition build_state_transition(character c, bool required_escape);
static character escape_character(character c);
static bool check_validity(str_view& expression, NFA& nfa);

// 逻辑规范：
// 前置条件：expression 是一个合法的表达式
// 后置条件：输出 expression 对应的 NFA
NFA build_nfa(str_view expression)
{
    NFA nfa = { state_transition(0, state_transition_type::VIRTUAL_TRANSFER, 0) };
    sizevalue i = 0;
    bool required_escape = false;
    for (i = 0; i < expression.size(); ++i) {
        if (expression[i] == STR("\\")[0] && !required_escape) {
            required_escape = true;
            continue;
        }
        else if (expression[i] == STR("ε")[0] && !required_escape) {
            continue;
        }
        else if (expression[i] == STR("·")[0] && !required_escape) {
            state_transition st = { expression[i], state_transition_type::ANY, nfa.size() + 1 };
            nfa.push_back(st);
            continue;
        }
        state_transition st = build_state_transition(expression[i], required_escape);
        required_escape = false;
        st.index_of_default_target = nfa.size() + 1;
        nfa.push_back(st);
    }
    nfa.back().index_of_default_target = sizevalue_max;
    runtime_assert(check_validity(expression, nfa), "正则表达式\"" + variable_length(expression.data()) + "\"构建出了不等价的NFA");
    return std::move(nfa);
}

// 逻辑规范：
// 前置条件：无
// 后置条件：输出一个 transition_condition 为 process(c, required_escape)，type 为 state_transition_type::DEFAULT 的状态节点
//     process(c: character, required_escape: bool) -> character 定义为
//     c, 当 required_escape == false 时
//     '\0', 当 required_escape == true 且 c == '0' 时
//     '\a', 当 required_escape == true 且 c == 'a' 时
//     '\b', 当 required_escape == true 且 c == 'b' 时
//     '\t', 当 required_escape == true 且 c == 't' 时
//     '\n', 当 required_escape == true 且 c == 'n' 时
//     '\v', 当 required_escape == true 且 c == 'v' 时
//     '\f', 当 required_escape == true 且 c == 'f' 时
//     '\e', 当 required_escape == true 且 c == 'e' 时
//     c, 当以上条件均不被满足时
static state_transition build_state_transition(character c, bool required_escape)
{
    state_transition st{};
    if (required_escape) {
        escape_character(c);
    }
    st.transition_condition = c;
    st.type = state_transition_type::DEFAULT;
    return std::move(st);
}

static character escape_character(character c)
{
    switch (c) {
    case STR("0")[0]:
        c = STR("\0")[0];
        break;
    case STR("a")[0]:
        c = STR("\a")[0];
        break;
    case STR("b")[0]:
        c = STR("\b")[0];
        break;
    case STR("t")[0]:
        c = STR("\t")[0];
        break;
    case STR("n")[0]:
        c = STR("\n")[0];
        break;
    case STR("v")[0]:
        c = STR("\v")[0];
        break;
    case STR("f")[0]:
        c = STR("\f")[0];
        break;
    case STR("e")[0]:
        c = STR("\e")[0];
        break;
    }
    return c;
}

// 输入正则表达式字面量和NFA，判断此NFA是否对应输入的表达式，如果对应成功输出真值，反之输出假值
static bool check_validity(str_view& expression, NFA& nfa)
{
    sizevalue count_of_transition = 1; // 目前推理到的状态节点的索引
    bool required_escape = false;
    for (sizevalue i = 0; i < expression.size(); ++i) {
        if (expression[i] == STR("\\")[0] && !required_escape) {
            required_escape = true;
            continue;
        }
        else if (expression[i] == STR("ε")[0] && !required_escape) {
            continue;
        }
        else if (expression[i] == STR("·")[0] && !required_escape) {
            // 判断字面量中的任意字符是否在NFA中也为任意字符的转移条件
            if (nfa[count_of_transition].type != state_transition_type::ANY) {
                return false;
            }
            count_of_transition += 1;
            continue;
        }
        // 判断字面量中相邻的字面字符是否在NFA中也相邻
        if (nfa[count_of_transition].transition_condition != required_escape ? escape_character(expression[i]) : expression[i]) {
            return false;
        }
        required_escape = false;
        count_of_transition += 1;
    }
    return true;
}