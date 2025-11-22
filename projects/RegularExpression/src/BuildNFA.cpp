#include "BuildNFA"
#include "Basic"
#include "FixedLengthString"
#include "RuntimeException"
#include "StateTransition"
#include "map"
#include "functional"
#include "algorithm"

using std::map;
using std::function;
using std::for_each;

struct building_context
{
    NFA nfa{};
    vector<vector<state_transition>> virtual_transitions_table{};
    vector<vector<sizevalue>> index_of_predecessors_virtual_transitions{};
    vector<vector<sizevalue>> index_of_successors_state_transitions{};
    sizevalue number_of_nested_of_or_operation{};
};

static state_transition build_state_transition(character c, bool required_escape);
static character escape_character(character c);
static bool check_validity(str_view& expression, NFA& nfa);
static void left_bracket(str_view expression, sizevalue& current_index, building_context& context);
static void right_bracket(str_view expression, sizevalue& current_index, building_context& context);
static void expression_or(str_view expression, sizevalue& current_index, building_context& context);
static bool is_last(str_view expression, sizevalue index, character c);
static void connect_predecessors_and_successors(building_context& context);
static void expand_virtual_transition(building_context& context);

map<character, function<void(str_view, sizevalue&, building_context&)>> functional_characters {
    { STR("(")[0], left_bracket },
    { STR(")")[0], right_bracket },
    { STR("|")[0], expression_or },
};

// 逻辑规范：
// 前置条件：expression 是一个合法的表达式
// 后置条件：输出 expression 对应的 NFA
NFA build_nfa(str_view expression)
{
    building_context context{};
    context.nfa = { state_transition(0, state_transition_type::VIRTUAL_TRANSFER, 0) };
    context.virtual_transitions_table.push_back({});
    context.index_of_predecessors_virtual_transitions.push_back({ 0 }); // 前驱队列初始化时默认有两个元素
    context.index_of_predecessors_virtual_transitions.push_back({});
    context.index_of_successors_state_transitions.push_back({ 0 }); // 后继队列初始化时默认有一个元素
    context.number_of_nested_of_or_operation = 0;
    sizevalue i = 0;
    bool required_escape = false;
    for (i = 0; i < expression.size(); ++i) {
        // 这个分支保证了：对于所有为"\c"的结构，以最高优先级处理
        if (expression[i] == STR("\\")[0] && !required_escape) {
            required_escape = true;
            continue;
        }
        // 这个分支保证了：对于所有未被转义的"ε"，当作空内容处理
        else if (expression[i] == STR("ε")[0] && !required_escape) {
            continue;
        }
        // 这个分支保证了：对于所有未被转义的"·"，当作任意字符处理
        else if (expression[i] == STR("·")[0] && !required_escape) {
            state_transition st = { expression[i], state_transition_type::ANY, context.nfa.size() + 1 };
            context.nfa.push_back(st);
            continue;
        }
        // 这个分支保证了：对于所有未被转义的功能字符，以其语义进行特殊处理
        else if (functional_characters.contains(expression[i]) && !required_escape) {
            functional_characters[expression[i]](expression, i, context);
            continue;
        }
        // 如果是转义字符，或者不是转义字符但也不是上述提及的字符，当作普通字符处理
        state_transition st = build_state_transition(expression[i], required_escape);
        required_escape = false;
        st.index_of_default_target = context.nfa.size() + 1; // 所有默认字符节点默认指向自身相对于NFA中的下一个节点
        context.nfa.push_back(st);
    }
    runtime_assert(!required_escape, "禁止在表达式的末尾使用无后继字符的'\\'");
    context.nfa.back().index_of_default_target = sizevalue_max;
    // 为 NFA 开头的虚转移节点添加到第一个实义状态的转移路径
    auto first_meaningful_node = std::find_if(context.nfa.begin(), context.nfa.end(), [](const state_transition& transition) { return transition.type != state_transition_type::VIRTUAL_TRANSFER; });
    context.virtual_transitions_table[0].insert(context.virtual_transitions_table[0].begin(), state_transition(0, state_transition_type::TRANSFER, first_meaningful_node - context.nfa.begin()));
    // 后续处理
    connect_predecessors_and_successors(context);
    expand_virtual_transition(context);
    // runtime_assert(check_validity(expression, context.nfa), "正则表达式\"" + variable_length(expression.data()) + "\"构建出了不等价的NFA");
    return std::move(context.nfa);
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

// 逻辑规范：
// 前置条件：无
// 后置条件：输出 escape(c)
//     escape(c: character) -> character 定义为
//     '\0', 且 c == '0' 时
//     '\a', 且 c == 'a' 时
//     '\b', 且 c == 'b' 时
//     '\t', 且 c == 't' 时
//     '\n', 且 c == 'n' 时
//     '\v', 且 c == 'v' 时
//     '\f', 且 c == 'f' 时
//     '\e', 且 c == 'e' 时
//     c, 当以上条件均不被满足时
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

static void left_bracket(str_view expression, sizevalue& current_index, building_context& context)
{
    // 尝试寻找上一个实义节点
    auto it = context.nfa.end() - 1;
    while (it->type == state_transition_type::VIRTUAL_TRANSFER && it != context.nfa.begin()) {
        it -= 1;
    }
    // 当找到上一个实义节点且满足不指向结束状态时
    if (it->type != state_transition_type::VIRTUAL_TRANSFER && it->index_of_default_target != sizevalue_max) {
        context.nfa.back().index_of_default_target += 1; // 因为被左括号分割的节点之间需要有一个虚转移节点，所以把原本指向下一个节点的索引+1，否则将错误地指向虚转移节点
    }
    for (sizevalue i = 0; i < context.index_of_predecessors_virtual_transitions.back().size(); ++i) {
        // 同理，因为虚转移节点，前驱的转移目标的索引也要+1
        auto& virtual_transition = context.virtual_transitions_table[context.index_of_predecessors_virtual_transitions.back()[i]];
        if (!virtual_transition.empty()) {
            virtual_transition.back().index_of_default_target += 1;
        }
    }
    // 同理，当左括号的直接前驱是或运算时，将或运算添加的后继的索引+1
    if (*(context.index_of_successors_state_transitions.back().end() - 2) == context.nfa.size()) {
        *(context.index_of_successors_state_transitions.back().end() - 2) += 1;
    }
    // 前驱就是末尾，以上代码保证了所有末尾(包括记录的前驱和上一个实义节点)跳过虚转移节点，指向虚转移节点后的下一个节点

    context.index_of_predecessors_virtual_transitions.back().push_back(context.virtual_transitions_table.size());
    context.index_of_predecessors_virtual_transitions.push_back({}); // 前驱队列在末尾添加一个元素
    context.index_of_successors_state_transitions.push_back({ context.nfa.size() }); // 后继队列在末尾添加一个元素
    // 当进入新的括号的作用域时，之前的一组前驱(包括之前所有的前驱和左括号的直接前驱)被暂存，作用域内的前驱被放在新的一组前驱内
    // 当进入新的括号的作用域时，之前的一组后继被暂存，作用域内的后继被放在新的一组后继内
    
    context.nfa.push_back(state_transition(0, state_transition_type::VIRTUAL_TRANSFER, context.virtual_transitions_table.size()));
    context.virtual_transitions_table.push_back({});

    bool required_escape = false;
    bool finish_correctly = false;
    // 在这对括号的作用域结束前，在此函数中遍历表达式并构建状态节点
    for (++current_index; current_index < expression.size(); ++current_index) {
        if (expression[current_index] == STR("\\")[0] && !required_escape) {
            required_escape = true;
            continue;
        }
        else if (expression[current_index] == STR("ε")[0] && !required_escape) {
            continue;
        }
        else if (expression[current_index] == STR("·")[0] && !required_escape) {
            state_transition st = { expression[current_index], state_transition_type::ANY, context.nfa.size() + 1 };
            context.nfa.push_back(st);
            continue;
        }
        else if (functional_characters.contains(expression[current_index])) {
            functional_characters[expression[current_index]](expression, current_index, context);
            // 当满足以下条件时，说明这对括号的作用域结束了，打破循环
            if (expression[current_index] == STR(")")[0]) {
                current_index += 1;
                finish_correctly = true;
                break;
            }
            continue;
        }
        state_transition st = build_state_transition(expression[current_index], required_escape);
        required_escape = false;
        st.index_of_default_target = context.nfa.size() + 1;
        context.nfa.push_back(st);
    }
    // 最外层的括号作用域结束时，调整索引，防止漏掉字符
    if (current_index >= expression.size()) {
        current_index -= 1;
    }
    else if (expression[current_index] != STR(")")[0]) {
        current_index -= 1;
    }
    runtime_assert(finish_correctly, "禁止在表达式中使用不成对的左括号");
}

static void right_bracket(str_view expression, sizevalue& current_index, building_context& context)
{
    runtime_assert(current_index > 0, "禁止在表达式开头使用右括号");
    runtime_assert(!is_last(expression, current_index - 1, STR("(")[0]), "禁止在表达式中出现内容为空的一对括号\"()\"");
    runtime_assert(!is_last(expression, current_index - 1, STR("|")[0]), "禁止在表达式中出现无效的或运算\"...|)\"");
    runtime_assert(!context.index_of_successors_state_transitions.empty(), "禁止在表达式中使用不成对的右括号");

    // 如果满足以下条件，说明或运算及其作用域的末尾之间存在空字符串，那么消除空字符串的影响
    if (context.index_of_successors_state_transitions.back().size() > 1) {
        auto& index_of_successor_state_transitions = context.index_of_successors_state_transitions.back();
        if (index_of_successor_state_transitions.back() == context.nfa.size()) {
            // 删除 expression_or 添加的元素
            context.index_of_predecessors_virtual_transitions.back().pop_back();
            context.index_of_successors_state_transitions.back().pop_back();
        }
    }
    // 结算前驱队列倒数第二个元素和后继队列最后一个元素的连接
    connect_predecessors_and_successors(context);

    // 为所有新前驱预先添加转移路径
    auto& predecessors_virtual_transitions = *(context.index_of_predecessors_virtual_transitions.end() - 1 - context.number_of_nested_of_or_operation);
    for (sizevalue i = 0; i < predecessors_virtual_transitions.size(); ++i) {
        if (context.number_of_nested_of_or_operation > 0) {
            // 如果是连续或运算，则清空之前的转移路径，因为要使用连续或的最后一个或运算为基准
            context.virtual_transitions_table[predecessors_virtual_transitions[i]].clear();
        }
        context.virtual_transitions_table[predecessors_virtual_transitions[i]].push_back(state_transition(0, state_transition_type::TRANSFER, context.nfa.size()));
    }

    context.index_of_predecessors_virtual_transitions.erase(context.index_of_predecessors_virtual_transitions.end() - 2); // 前驱队列移除倒数第二个元素
    context.index_of_successors_state_transitions.pop_back(); // 后继队列在末尾移除一个元素

    // 如果在连续或运算中，减少一个连续层数
    if (context.number_of_nested_of_or_operation > 0) {
        context.number_of_nested_of_or_operation -= 1;
    }
    return;
}

static void expression_or(str_view expression, sizevalue& current_index, building_context& context)
{
    runtime_assert(current_index > 0, "禁止在表达式开头使用或运算");
    runtime_assert(!is_last(expression, current_index - 1, STR("(")[0]), "禁止在表达式中出现无效的或运算\"(|...\"");
    runtime_assert(!is_last(expression, current_index - 1, STR("|")[0]), "禁止在表达式中出现无效的或运算\"...||...\"");
    // 如果满足以下条件，说明进行或操作的左表达式是一个空字符串，那么无视这次或操作
    if (context.index_of_successors_state_transitions.back().size() > 1) {
        auto& index_of_successor_state_transitions = context.index_of_successors_state_transitions.back();
        if (index_of_successor_state_transitions.back() == context.nfa.size()) {
            return;
        }
    }

    // 尝试寻找上一个实义节点
    auto it = context.nfa.end() - 1;
    while (it->type == state_transition_type::VIRTUAL_TRANSFER && it != context.nfa.begin()) {
        it -= 1;
    }
    // 当找到上一个实义节点且满足不指向结束状态时
    if (it->type != state_transition_type::VIRTUAL_TRANSFER && it->index_of_default_target != sizevalue_max) {
        context.nfa.back().index_of_default_target += 1; // 因为被或运算产生一个虚转移节点，所以把原本指向下一个节点的索引+1，否则将错误地指向虚转移节点
    }
    for (sizevalue i = 0; i < context.index_of_predecessors_virtual_transitions.back().size(); ++i) {
        // 同理，因为虚转移节点，前驱的转移目标的索引也要+1
        auto& virtual_transition = context.virtual_transitions_table[context.index_of_predecessors_virtual_transitions.back()[i]];
        if (!virtual_transition.empty()) {
            virtual_transition.back().index_of_default_target += 1;
        }
    }

    // 默认往前驱队列的元素的最后一个元素中写入，如果是连续或运算，则使用最外层作用域的前驱队列
    (context.index_of_predecessors_virtual_transitions.end() - 1 - context.number_of_nested_of_or_operation)->push_back(context.virtual_transitions_table.size());
    context.nfa.back().index_of_default_target = sizevalue_max;
    context.nfa.push_back(state_transition(0, state_transition_type::VIRTUAL_TRANSFER, context.virtual_transitions_table.size()));
    context.virtual_transitions_table.push_back({});
    // 默认往后继队列的元素的最后一个元素中写入，如果是连续或运算，则使用最外层作用域的后继队列
    (context.index_of_successors_state_transitions.end() - 1 - context.number_of_nested_of_or_operation)->back() = context.nfa.size();
    (context.index_of_successors_state_transitions.end() - 1 - context.number_of_nested_of_or_operation)->push_back(0);

    // 如果或运算的后继是左括号且直接前驱不是右括号，那么形成了连续或运算，记录连续的层数
    for (sizevalue i = current_index + 1; i < expression.size(); ++i) {
        if (expression[i] != STR("(")[0]) {
            break;
        }
        context.number_of_nested_of_or_operation += 1;
    }
}

// 逻辑规范：
// 前置条件：index < expression.size()
// 后置条件：输出 expression[index] 是否是未转义的 c
static bool is_last(str_view expression, sizevalue index, character c)
{
    if (expression[index] != c) {
        return false;
    }
    bool is_escape = false;
    for (sizevalue i = index - 1; i != sizevalue_max; --i) {
        if (expression[i] != STR("\\")[0]) {
            break;
        }
        is_escape = !is_escape;
    }
    return !is_escape;
}

// 逻辑规范：
// 前置条件：无
// 后置条件：context.index_of_predecessors_virtual_transitions 倒数第二个元素中指向的所有的虚转移表，其中包含所有指向 context.index_of_successors_state_transitions 最后一个元素处索引的转移节点
static void connect_predecessors_and_successors(building_context& context)
{
    auto& virtual_transitions_table = context.virtual_transitions_table;
    auto& index_of_successor_state_transitions = context.index_of_successors_state_transitions.back();
    auto proc = [&index_of_successor_state_transitions, &virtual_transitions_table](sizevalue index) {
        for (sizevalue i = 0; i < index_of_successor_state_transitions.size() - 1; ++i) {
            virtual_transitions_table[index].push_back(state_transition(0, state_transition_type::TRANSFER, index_of_successor_state_transitions[i]));
        }
    };
    for_each((context.index_of_predecessors_virtual_transitions.end() - 2)->begin(), (context.index_of_predecessors_virtual_transitions.end() - 2)->end(), proc);
}

// 逻辑规范：
// 前置条件：无
// 后置条件：context.nfa 中的所有虚转移节点都展开为转移节点，且NFA整体的转移路径不变
static void expand_virtual_transition(building_context& context)
{
    // 第一遍遍历，建立映射表
    vector<sizevalue> original_index_to_expanded_index(context.nfa.size(), 0); // 索引代表 original_index，值代表 expanded_index
    intmax current_offset = 0;
    for (sizevalue i = 0; i < context.nfa.size(); ++i) {
        // 处理NFA中的虚转移节点
        if (context.nfa[i].type == state_transition_type::VIRTUAL_TRANSFER) {
            auto& transitions = context.virtual_transitions_table[context.nfa[i].index_of_default_target];
            intmax offset_of_this = -1;
            // 如果虚转移节点修饰的节点的默认转移路径指向NFA的结束状态，则将虚转移包含的第一个转移赋给默认转移路径
            auto previous_meaningful_it = context.nfa.begin() + i;
            while (previous_meaningful_it->type == state_transition_type::VIRTUAL_TRANSFER && previous_meaningful_it != context.nfa.begin()) {
                previous_meaningful_it -= 1;
            }
            if (previous_meaningful_it != context.nfa.begin()) {
                if (previous_meaningful_it->index_of_default_target >= context.nfa.size() && transitions.size() > 0) {
                    offset_of_this -= 1;
                }
            }
            // 计算偏移
            offset_of_this += transitions.size();
            current_offset += offset_of_this;
            continue;
        }
        // 如果是普通节点，根据 current_offset 进行索引的映射
        original_index_to_expanded_index[i] = i + current_offset;
    }

    // 第二遍遍历，展开虚转移节点
    vector<state_transition> expanded_nfa{};
    for (sizevalue i = 0; i < context.nfa.size(); ++i) {
        // 如果是虚转移节点，进行展开处理
        if (context.nfa[i].type == state_transition_type::VIRTUAL_TRANSFER) {
            sizevalue index_of_virtual_transition = context.nfa[i].index_of_default_target;
            auto& virtual_transitions = context.virtual_transitions_table[index_of_virtual_transition];
            // 如果虚转移节点修饰的节点的默认转移路径指向NFA的结束状态，则将虚转移包含的第一个转移赋给默认转移路径，剩下的再正常展开。
            auto previous_meaningful_it = context.nfa.begin() + i;
            while (previous_meaningful_it->type == state_transition_type::VIRTUAL_TRANSFER && previous_meaningful_it != context.nfa.begin()) {
                previous_meaningful_it -= 1;
            }
            if (previous_meaningful_it != context.nfa.begin()) {
                if (previous_meaningful_it->index_of_default_target >= context.nfa.size() && virtual_transitions.size() > 0) {
                    expanded_nfa.back().index_of_default_target = virtual_transitions.front().index_of_default_target;
                    expanded_nfa.insert(expanded_nfa.end(), virtual_transitions.begin() + 1, virtual_transitions.end());
                    continue;
                }
            }
            // 否则全部正常展开
            expanded_nfa.insert(expanded_nfa.end(), virtual_transitions.begin(), virtual_transitions.end());
        }
        // 否则正常添加
        else {
            expanded_nfa.push_back(context.nfa[i]);
        }
    }
    context.nfa = std::move(expanded_nfa); // 将展开后的结果载入上下文

    // 第三遍遍历，将所有的转移路径映射到新转移路径
    for (sizevalue i = 0; i < context.nfa.size(); ++i) {
        if (context.nfa[i].index_of_default_target >= original_index_to_expanded_index.size()) {
            context.nfa[i].index_of_default_target = sizevalue_max;
            continue; // 不处理指向结束状态的转移路径
        }
        context.nfa[i].index_of_default_target = original_index_to_expanded_index[context.nfa[i].index_of_default_target];
    }
}

// 输入正则表达式字面量和NFA，判断此NFA是否对应输入的表达式，如果对应成功输出真值，反之输出假值
static bool check_validity(str_view& expression, NFA& nfa)
{
    // sizevalue count_of_transition = 1; // 目前推理到的状态节点的索引
    // bool required_escape = false;
    // for (sizevalue i = 0; i < expression.size(); ++i) {
    //     if (expression[i] == STR("\\")[0] && !required_escape) {
    //         required_escape = true;
    //         continue;
    //     }
    //     else if (expression[i] == STR("ε")[0] && !required_escape) {
    //         continue;
    //     }
    //     else if (expression[i] == STR("·")[0] && !required_escape) {
    //         // 判断字面量中的任意字符是否在NFA中也为任意字符的转移条件
    //         if (nfa[count_of_transition].type != state_transition_type::ANY) {
    //             return false;
    //         }
    //         count_of_transition += 1;
    //         continue;
    //     }
    //     // 判断字面量中相邻的字面字符是否在NFA中也相邻
    //     if (nfa[count_of_transition].transition_condition != required_escape ? escape_character(expression[i]) : expression[i]) {
    //         return false;
    //     }
    //     required_escape = false;
    //     count_of_transition += 1;
    // }
    return true;
}