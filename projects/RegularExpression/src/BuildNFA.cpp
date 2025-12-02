#include "BuildNFA"
#include "Basic"
#include "FixedLengthString"
#include "RuntimeException"
#include "StateTransition"
#include "map"
#include "functional"

using std::map;
using std::function;

struct building_context
{
    NFA nfa{};
    vector<vector<state_transition>> virtual_transitions_table{};
    vector<vector<sizevalue>> index_of_predecessors_state_transitions{};
    vector<vector<sizevalue>> index_of_successors_state_transitions{};
    vector<vector<sizevalue>> temporary_predecessors_buffer{};
    sizevalue last_index_of_predecessors_because_epsilon;
    vector<sizevalue> predecessors_before_kleene_star{};
};

static state_transition build_state_transition(character c, bool required_escape);
static character escape_character(character c);
static void left_bracket(str_view expression, sizevalue& current_index, building_context& context);
static void right_bracket(str_view expression, sizevalue& current_index, building_context& context);
static void expression_or(str_view expression, sizevalue& current_index, building_context& context);
static void kleene_star(str_view expression, sizevalue& current_index, building_context& context);
static void connect_in_kleene_star(building_context& context);
static bool is_last(str_view expression, sizevalue index, character c);
static bool is_local_epsilon(building_context& context);
static void connect_predecessors_and_successors(building_context& context);
static void clear_last_pair_of_predecessors_and_successors(building_context& context);
static void connect_normal_transitions(building_context& context);
static void expand_virtual_transition(building_context& context);

map<character, function<void(str_view, sizevalue&, building_context&)>> functional_characters {
    { STR("(")[0], left_bracket },
    { STR(")")[0], right_bracket },
    { STR("|")[0], expression_or },
    { STR("*")[0], kleene_star },
};

// 逻辑规范：
// 前置条件：expression 是一个合法的表达式
// 后置条件：输出 expression 对应的 NFA
NFA build_nfa(str_view expression)
{
    building_context context{};
    context.nfa = { state_transition(0) };
    context.virtual_transitions_table.push_back({});
    context.index_of_predecessors_state_transitions.push_back({ 0 }); // 前驱队列初始化
    context.temporary_predecessors_buffer.push_back({}); // 前驱缓冲区初始化
    sizevalue i = 0;
    bool required_escape = false;
    // 主循环：正确处理转义，遇到空字符串无效处理；遇到任意字符添加对应节点；遇到功能字符以其语义进行特殊处理；否则前述皆不满足时添加状态节点
    for (i = 0; i < expression.size(); ++i) {
        // 这个分支保证了：对于所有为"\·"的结构，以最高优先级处理
        if (expression[i] == STR("\\")[0] && !required_escape) {
            // 之后的执行路径: required_escape = true -> continue -> build_state_transition -> required_escape = false
            required_escape = true;
            continue;
        }
        // 这个分支保证了：对于所有未被转义的"ε"，当作空内容处理
        else if (expression[i] == STR("ε")[0] && !required_escape) {
            continue;
        }
        // 这个分支保证了：对于所有未被转义的"·"，当作任意字符处理
        else if (expression[i] == STR("·")[0] && !required_escape) {
            state_transition st = { expression[i], state_transition_type::ANY };
            connect_normal_transitions(context);
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
        // st == q_{n+1}, n 为 NFA 中当前的实义状态节点数量
        required_escape = false; // 确保转义字符成为状态节点之后，转义结束
        connect_normal_transitions(context);
        context.nfa.push_back(st);
    }
    runtime_assert(!required_escape, "禁止在表达式的末尾使用无后继字符的'\\'");
    // 为表达式的末尾添加指向结束状态的转移路径
    context.index_of_predecessors_state_transitions.back().insert(context.index_of_predecessors_state_transitions.back().end(), context.temporary_predecessors_buffer.front().begin(), context.temporary_predecessors_buffer.front().end());
    for (auto& element : context.index_of_predecessors_state_transitions.back()) {
        if (context.nfa[element].is_transfer_transition()) {
            context.virtual_transitions_table[context.nfa[element].index()].push_back(state_transition(sizevalue_max));
        }
        else if (element + 1 < context.nfa.size()) {
            if (context.nfa[element + 1].is_transfer_transition()) {
                context.virtual_transitions_table[context.nfa[element + 1].index()].push_back(state_transition(sizevalue_max));
            }
            else {
                goto last;
            }
        }
        else {
            last:
            runtime_assert(element == context.nfa.size() - 1, "禁止为没有特殊转移路径的节点添加新的转移路径");
            context.nfa.push_back(state_transition(sizevalue_max));
        }
    }
    // 判断末尾是否为空的分支子表达式
    if (is_local_epsilon(context)) {
        // 如果为空且在表达式顶层
        if (context.last_index_of_predecessors_because_epsilon != sizevalue_max) {
            // 为起始状态添加到结束状态的转移路径
            context.virtual_transitions_table[0].push_back(state_transition(sizevalue_max));
            context.last_index_of_predecessors_because_epsilon = sizevalue_max;
        }
    }
    // 后续处理
    expand_virtual_transition(context);
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
    // 如果满足以下条件，应为连续的左括号等情况，需要为 index_of_predecessors_state_transitions 添加与之前的前驱索引相同的元素
    if (context.index_of_predecessors_state_transitions.back().empty()) {
        context.index_of_predecessors_state_transitions.back().insert(context.index_of_predecessors_state_transitions.back().end(), (context.index_of_predecessors_state_transitions.end() - 2)->begin(), (context.index_of_predecessors_state_transitions.end() - 2)->end());
    }
    context.index_of_predecessors_state_transitions.push_back({}); // 前驱队列在末尾添加一个元素
    context.index_of_successors_state_transitions.push_back({}); // 后继队列在末尾添加一个元素
    // 当进入新的括号的作用域时，之前的一组前驱(包括之前所有的前驱和左括号的直接前驱)被暂存，作用域内的前驱被放在新的一组前驱内
    // 当进入新的括号的作用域时，之前的一组后继被暂存，作用域内的后继被放在新的一组后继内

    context.temporary_predecessors_buffer.push_back({}); // 前驱缓冲区随着进入新的作用域而增加一层

    // 如果末尾不是虚转移节点
    if (!context.nfa.back().is_transfer_transition()) {
        // 添加新的虚转移节点
        context.nfa.push_back(state_transition(context.virtual_transitions_table.size()));
        context.virtual_transitions_table.push_back({});
    }

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
            state_transition st = { expression[current_index], state_transition_type::ANY };
            connect_normal_transitions(context);
            context.nfa.push_back(st);
            continue;
        }
        else if (functional_characters.contains(expression[current_index])) {
            // 当满足以下条件时，说明这对括号的作用域结束了，打破循环
            if (expression[current_index] == STR(")")[0]) {
                functional_characters[expression[current_index]](expression, current_index, context);
                finish_correctly = true;
                break;
            }
            functional_characters[expression[current_index]](expression, current_index, context);
            continue;
        }
        state_transition st = build_state_transition(expression[current_index], required_escape);
        required_escape = false;
        connect_normal_transitions(context);
        context.nfa.push_back(st);
    }
    runtime_assert(finish_correctly, "禁止在表达式中使用不成对的左括号");
}

static void right_bracket(str_view expression, sizevalue& current_index, building_context& context)
{
    runtime_assert(current_index > 0, "禁止在表达式开头使用右括号");
    runtime_assert(!is_last(expression, current_index - 1, STR("(")[0]), "禁止在表达式中出现内容为空的一对括号\"()\"");
    runtime_assert(!is_last(expression, current_index - 1, STR("|")[0]), "禁止在表达式中出现无效的或运算\"...|)\"");
    runtime_assert(!context.index_of_successors_state_transitions.empty(), "禁止在表达式中使用不成对的右括号");

    // 判断是否存在或运算的子表达式为空
    if (is_local_epsilon(context)) {
        // 如果为空，将或运算的前驱添加到 temporary_predecessors_buffer 中
        auto last_predecessor = (context.index_of_predecessors_state_transitions.end() - 2)->back();
        // 确保没有添加过，以防重复添加
        if (context.last_index_of_predecessors_because_epsilon != last_predecessor) {
            context.temporary_predecessors_buffer.back().insert(context.temporary_predecessors_buffer.back().end(), (context.index_of_predecessors_state_transitions.end() - 2)->begin(), (context.index_of_predecessors_state_transitions.end() - 2)->end());
            context.last_index_of_predecessors_because_epsilon = last_predecessor;
        }
        return;
    }

    // 如果右括号的直接后继是闭包运算
    if (current_index + 1 < expression.size()) {
        if (expression[current_index + 1] == STR("*")[0]) {
            // 将这对括号作用域的前驱继承到下一个作用域，使用 predecessors_before_kleene_star 进行转存
            auto& index_of_predecessor_state_transitions = *(context.index_of_predecessors_state_transitions.end() - 2);
            context.predecessors_before_kleene_star.clear();
            context.predecessors_before_kleene_star.insert(context.predecessors_before_kleene_star.end(), index_of_predecessor_state_transitions.begin(), index_of_predecessor_state_transitions.end());
        }
    }

    connect_predecessors_and_successors(context);
    clear_last_pair_of_predecessors_and_successors(context);

    // 从前驱缓冲区中取走前驱，放置在 index_of_predecessors_state_transitions 的末尾，以让作用域的后继以这些前驱作为直接前驱，同时移除一层缓冲区
    context.index_of_predecessors_state_transitions.back().insert(context.index_of_predecessors_state_transitions.back().end(), context.temporary_predecessors_buffer.back().begin(), context.temporary_predecessors_buffer.back().end());
    context.temporary_predecessors_buffer.pop_back();
}

static void expression_or(str_view expression, sizevalue& current_index, building_context& context)
{
    runtime_assert(current_index > 0, "禁止在表达式开头使用或运算");
    runtime_assert(!is_last(expression, current_index - 1, STR("(")[0]), "禁止在表达式中出现无效的或运算\"(|...\"");
    runtime_assert(!is_last(expression, current_index - 1, STR("|")[0]), "禁止在表达式中出现无效的或运算\"...||...\"");

    // 如果最后一个节点不为虚转移节点，正常处理
    if (!context.nfa.back().is_transfer_transition()) {
        context.nfa.push_back(state_transition(context.virtual_transitions_table.size()));
        context.virtual_transitions_table.push_back({});
    }
    // 否则判断是否存在或运算的子表达式为空
    else if (is_local_epsilon(context)) {
        // 如果为空且在表达式顶层
        if (context.index_of_predecessors_state_transitions.size() < 2 && context.last_index_of_predecessors_because_epsilon != sizevalue_max) {
            // 为起始状态添加到结束状态的转移路径
            context.virtual_transitions_table[0].push_back(state_transition(sizevalue_max));
            context.last_index_of_predecessors_because_epsilon = sizevalue_max;
            return;
        }
        // 如果为空，将或运算的前驱添加到 temporary_predecessors_buffer 中
        auto last_predecessor = (context.index_of_predecessors_state_transitions.end() - 2)->back();
        // 确保没有添加过，以防重复添加
        if (context.last_index_of_predecessors_because_epsilon != last_predecessor) {
            context.temporary_predecessors_buffer.back().insert(context.temporary_predecessors_buffer.back().end(), (context.index_of_predecessors_state_transitions.end() - 2)->begin(), (context.index_of_predecessors_state_transitions.end() - 2)->end());
            context.last_index_of_predecessors_because_epsilon = last_predecessor;
        }
        return;
    }

    // 将或运算左方的子表达式的末尾添加到前驱缓冲区中
    context.temporary_predecessors_buffer.back().insert(context.temporary_predecessors_buffer.back().end(), context.index_of_predecessors_state_transitions.back().begin(), context.index_of_predecessors_state_transitions.back().end());
    // 截断直接前驱，使其无法直接连接到后方的节点
    context.index_of_predecessors_state_transitions.back().clear();
}

static void kleene_star(str_view expression, sizevalue& current_index, building_context& context)
{
    runtime_assert(current_index > 0, "禁止在表达式开头使用闭包运算");
    runtime_assert(!is_last(expression, current_index - 1, STR("(")[0]), "禁止在表达式中出现无效的闭包运算\"(*\"");
    runtime_assert(!is_last(expression, current_index - 1, STR("|")[0]), "禁止在表达式中出现无效的闭包运算\"|*\"");
    runtime_assert(!is_last(expression, current_index - 1, STR("*")[0]), "禁止在表达式中出现无效的闭包运算\"**\"");

    // 当最后一个字符不是未转义的右括号时，说明这是单个字符的闭包
    if (!is_last(expression, current_index - 1, STR(")")[0])) {
        // 如果是空字符串的闭包，直接无视
        if (is_last(expression, current_index, STR("ε")[0])) {
            return;
        }
        context.nfa.push_back(state_transition(context.virtual_transitions_table.size()));
        context.virtual_transitions_table.push_back({ state_transition(context.nfa.size() - 2) });
        return;
    }
    // 否则是括号作用域的闭包

    // 如果这个括号作用域内没有任何实义节点，直接无视 (判断NFA的最后一个节点是否是括号作用域的前驱)
    if (context.last_index_of_predecessors_because_epsilon == context.nfa.size() - 1) {
        return;
    }

    // 为NFA的最后一个节点，也就是括号作用域的最后一个末尾，添加虚转移节点
    if (!context.nfa.back().is_transfer_transition()) {
        context.nfa.push_back(state_transition(context.virtual_transitions_table.size()));
        context.virtual_transitions_table.push_back({});
    }

    // 让作用域内的所有末尾状态拥有指向所有开头状态的转移路径
    connect_in_kleene_star(context);

    // 将转存的前驱继承到下一个作用域
    context.index_of_predecessors_state_transitions.back().insert(context.index_of_predecessors_state_transitions.back().end(), context.predecessors_before_kleene_star.begin(), context.predecessors_before_kleene_star.end());

    context.predecessors_before_kleene_star.clear();
}

// 逻辑规范：
// 前置条件：context 中NFA末尾为虚转移节点，闭包运算作用的作用域不为空
// 后置条件：context 中前驱队列末尾的所有前驱和NFA末尾的实义节点，拥有指向以 direct_predecessors_before_kleene_star 末尾找到的所有开头和第一个开头的转移路径
static void connect_in_kleene_star(building_context& context)
{
    sizevalue index_of_previous_predecessor = 0; // 闭包运算作用的作用域之前的直接前驱在NFA中的索引
    // 推理计算 index_of_previous_predecessor
    for (sizevalue i = context.temporary_predecessors_buffer.size() - 1; i != sizevalue_max; --i) {
        if (!context.temporary_predecessors_buffer[i].empty()) {
            index_of_previous_predecessor = context.temporary_predecessors_buffer[i].back();
            break;
        }
    }
    index_of_previous_predecessor = std::max(index_of_previous_predecessor, context.predecessors_before_kleene_star.back());
    // 外层循环，遍历前驱队列末尾的所有前驱
    for (auto& index_of_predecessor : context.index_of_predecessors_state_transitions.back()) {
        auto& predecessor_state_transition = context.nfa[index_of_predecessor + 1];
        auto& transitions_of_predecessor = context.virtual_transitions_table[predecessor_state_transition.index()];
        // 中间层循环，遍历作用域的直接前驱往后的虚转移节点
        for (sizevalue i = index_of_previous_predecessor + 1; i < context.nfa.size(); ++i) {
            if (!context.nfa[i].is_transfer_transition()) {
                break;
            }
            auto& transitions = context.virtual_transitions_table[context.nfa[i].index()];
            // 内层循环，遍历虚转移节点代表的所有转移节点
            for (auto& transition : transitions) {
                // 使前驱队列末尾的所有前驱拥有指向/作用域的直接前驱往后的虚转移节点/代表的所有转移节点/的转移路径
                transitions_of_predecessor.push_back(transition);
            }
        }
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
// 后置条件：判断左方是否存在作用域内的整块子表达式为空
static bool is_local_epsilon(building_context& context)
{
    // 如果 context.temporary_predecessors_buffer.back().empty() 成立，例如是 "(ε|" 第一个或运算，当第一个块是 ε 时，上一个作用域的前驱指向的索引+1(即指向虚转移节点)+1(即NFA的大小)，因为中间没有任何节点
    if (context.temporary_predecessors_buffer.back().empty()) {
        // 当满足 context.index_of_predecessors_state_transitions.size() < 2 时说明在表达式的顶层
        if (context.index_of_predecessors_state_transitions.size() < 2) {
            // 此时若NFA只有初始的一个节点，那么说明表达式开头到第一个或运算之间为空
            return context.nfa.size() == 1;
        }
        return ((context.index_of_predecessors_state_transitions.end() - 2)->back() + 1) + 1 == context.nfa.size();
    }
    // 否则，例如是 "|ε|" 第n个或运算，左方的子表达式为空，temporary_predecessors_buffer.back().back() 指向上个有实际内容的子表达式的末尾，+1(即指向虚转移节点)+1(即NFA的大小)，因为中间没有任何节点
    return (context.temporary_predecessors_buffer.back().back() + 1) + 1 == context.nfa.size();
}

// 逻辑规范：
// 前置条件：无
// 后置条件：context.index_of_predecessors_state_transitions 倒数第二个元素中指向的所有的虚转移表，其中包含所有指向 context.index_of_successors_state_transitions 最后一个元素处索引的转移节点
static void connect_predecessors_and_successors(building_context& context)
{
    auto& nfa = context.nfa;
    auto& virtual_transitions_table = context.virtual_transitions_table;
    auto& index_of_successor_state_transitions = context.index_of_successors_state_transitions.back();
    for (auto it = (context.index_of_predecessors_state_transitions.end() - 2)->begin(); it != (context.index_of_predecessors_state_transitions.end() - 2)->end(); ++it) {
        for (sizevalue i = 0; i < index_of_successor_state_transitions.size(); ++i) {
            if (nfa[*it].is_transfer_transition()) {
                virtual_transitions_table[nfa[*it].index()].push_back(state_transition(index_of_successor_state_transitions[i]));
            }
            else if (*it + 1 < nfa.size()) {
                if (nfa[*it + 1].is_transfer_transition()) {
                    virtual_transitions_table[nfa[*it + 1].index()].push_back(state_transition(index_of_successor_state_transitions[i]));
                }
                else {
                    goto last;
                }
            }
            else {
                last:
                // *it + 1 == index_of_successor_state_transitions[i] 成立时即连接的两个节点直接相邻，此时省略转移
                runtime_assert(*it + 1 == index_of_successor_state_transitions[i], "禁止为没有特殊转移路径的节点添加新的转移路径");
            }
        }
    }
}

static void clear_last_pair_of_predecessors_and_successors(building_context& context)
{
    context.index_of_predecessors_state_transitions.erase(context.index_of_predecessors_state_transitions.end() - 2);
    context.index_of_successors_state_transitions.pop_back();
}

static void connect_normal_transitions(building_context& context)
{
    // 当前驱队列中没有元素，即可能被截断时
    if (context.index_of_predecessors_state_transitions.back().empty()) {
        // 为之前的前驱添加后继，并使前驱队列中出现元素
        if (!context.index_of_successors_state_transitions.empty()) {
            // 如果不在顶层，index_of_successors_state_transitions 不为空，正常连接
            context.index_of_successors_state_transitions.back().push_back(context.nfa.size());
            connect_predecessors_and_successors(context);
            context.index_of_successors_state_transitions.back().pop_back();
        }
        else {
            // 在顶层，index_of_predecessors_state_transitions 为空，直接使起始状态连接到这个状态
            context.virtual_transitions_table[0].push_back(state_transition(context.nfa.size()));
        }
        context.index_of_predecessors_state_transitions.back().push_back(context.nfa.size());
        return;
    }
    // 否则正常连接
    context.index_of_predecessors_state_transitions.push_back({});
    context.index_of_successors_state_transitions.push_back({});
    context.index_of_successors_state_transitions.back().push_back(context.nfa.size()); // 添加这个节点作为上一个直接前驱的后继
    connect_predecessors_and_successors(context);
    clear_last_pair_of_predecessors_and_successors(context);
    context.index_of_predecessors_state_transitions.back().push_back(context.nfa.size()); // 添加这个节点作为下一个直接后继的前驱
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
        if (context.nfa[i].is_transfer_transition() && context.nfa[i].index() != sizevalue_max) {
            auto& transitions = context.virtual_transitions_table[context.nfa[i].index()];
            intmax offset_of_this = -1;
            // 如果虚转移节点修饰的节点的默认转移路径指向NFA的结束状态，则将虚转移包含的第一个转移赋给默认转移路径
            auto previous_meaningful_it = context.nfa.begin() + i;
            while (previous_meaningful_it->is_transfer_transition() && previous_meaningful_it != context.nfa.begin()) {
                previous_meaningful_it -= 1;
            }
            if (previous_meaningful_it != context.nfa.begin()) {
                if (previous_meaningful_it->index() == 0 && transitions.size() > 0) {
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
        if (context.nfa[i].is_transfer_transition() && context.nfa[i].index() != sizevalue_max) {
            sizevalue index_of_virtual_transition = context.nfa[i].index();
            auto& virtual_transitions = context.virtual_transitions_table[index_of_virtual_transition];
            // 如果虚转移节点修饰的节点的只有到下一个直接相邻节点的转移路径，则跳过处理，采用默认连接的模式。
            auto previous_meaningful_it = context.nfa.begin() + i;
            while (previous_meaningful_it->is_transfer_transition() && previous_meaningful_it != context.nfa.begin()) {
                previous_meaningful_it -= 1;
            }
            if (previous_meaningful_it != context.nfa.begin()) {
                if (previous_meaningful_it - context.nfa.begin() + 1 + 1 == virtual_transitions.front().index() && virtual_transitions.size() == 1) {
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
        if (context.nfa[i].is_transfer_transition() && context.nfa[i].index() >= original_index_to_expanded_index.size()) {
            context.nfa[i] = state_transition(sizevalue_max);
            continue; // 不处理指向结束状态的转移路径
        }
        else if (context.nfa[i].is_transfer_transition()) {
            context.nfa[i] = state_transition(original_index_to_expanded_index[context.nfa[i].index()]);
        }
    }
}