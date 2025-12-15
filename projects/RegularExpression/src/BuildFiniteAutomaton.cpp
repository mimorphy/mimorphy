#include "BuildFiniteAutomaton"
#include "Basic"
#include "FixedLengthString"
#include "RuntimeException"
#include "StateTransition"
#include "ConcatenateFiniteAutomaton"
#include "map"
#include "functional"

using std::map;
using std::function;

// 自动机上下文：用于表示一个虚转移节点未展开的自动机
struct finite_automaton_context
{
    finite_automaton finite_automaton{};
    vector<vector<state_transition>> virtual_transitions_table{};
};

// character_symbol 结构：
// 当 c != character_max 时，character_symbol 实例代表字面字符 c
// 当 c == character_max 时，character_symbol 实例代表特殊字符 functional
struct character_symbol
{
    character c = 0;
    character functional = 0;
    bool is_functional_symbol() const { return c == character_max; }
};

static character escape_character(character c);
static character_symbol next_symbol_of_expression(str_view expression, sizevalue& index);
static expression_information epsilon(str_view expression, sizevalue& index);
static expression_information center_dot(str_view expression, sizevalue& index);
static expression_information left_bracket(str_view expression, sizevalue& index);
static expression_information right_bracket(str_view expression, sizevalue& index);
static expression_information alternation(str_view expression, sizevalue& index);
static expression_information kleene_star(str_view expression, sizevalue& index);
static void literal_character_with_kleene_star(expression_information& information, state_transition transition);
static bool is_last(str_view expression, sizevalue index, character c);
static void connect_predecessors_and_successors(finite_automaton& finite_automaton, vector<vector<state_transition>>& virtual_transitions_table, vector<sizevalue>& index_of_predecessors, vector<sizevalue> index_of_successors);
static finite_automaton_context information_to_finite_automaton_context(expression_information& information);
static void expand_virtual_transition(finite_automaton_context& context);

map<character, function<expression_information(str_view, sizevalue&)>> functional_characters {
    { STR("ε")[0], epsilon },
    { STR("·")[0], center_dot },
    { STR("(")[0], left_bracket },
    { STR(")")[0], right_bracket },
    { STR("|")[0], alternation },
    { STR("*")[0], kleene_star },
};

// 逻辑规范：
// 前置条件：expression 是一个合法的表达式
// 后置条件：输出 expression 对应的自动机
finite_automaton build_finite_automaton(str_view expression)
{
    expression_information information{};
    information.content.reserve(expression.size());
    information.content.push_back(state_transition(0));
    information.virtual_transitions_table.push_back({});
    information.index_of_tails = { 0 };
    sizevalue i = 0;
    bool required_escape = false;
    // 主循环：
    while (i < expression.size()) {
        character_symbol symbol = next_symbol_of_expression(expression, i);
        // 如果是特殊字符标记，进行特殊处理
        if (symbol.is_functional_symbol()) {
            // 如果在最外层的表达式中出现了右括号，显然是无效的表达式，因为没有对应的左括号
            runtime_assert(symbol.functional != STR(")")[0], "禁止在表达式中使用不成对的右括号");
            // 进行特殊的函数调用
            expression_information sub_information = functional_characters[symbol.functional](expression, i);
            // 如果是或运算，以取并集的方式连接，否则以正常的首尾相接的方式连接
            symbol.functional == STR("|")[0] ? join_expression_information(information, sub_information) : concatenate_expression_information(information, sub_information);
            continue;
        }
        // 否则是字面字符标记
        if (symbol.functional == STR("*")[0]) {
            // 如果是被闭包修饰的字面字符，进行特殊处理
            literal_character_with_kleene_star(information, state_transition(symbol.c, state_transition_type::DEFAULT));
            i += 1;
            continue;
        }
        vector<sizevalue> temporary_index_of_successors = { information.content.size() };
        connect_predecessors_and_successors(information.content, information.virtual_transitions_table, information.index_of_tails, temporary_index_of_successors);
        information.index_of_tails = { information.content.size() };
        if (information.index_of_heads.empty()) {
            information.index_of_heads = { information.content.size() };
        }
        information.content.push_back(state_transition(symbol.c, state_transition_type::DEFAULT));
    }
    // 后续处理
    finite_automaton_context context = information_to_finite_automaton_context(information);
    expand_virtual_transition(context);
    return std::move(context.finite_automaton);
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

// 逻辑规范：
// 前置条件：index < expression.size()
// 后置条件：输出 expression 中以 index 为起始，往后的第一个字面字符标记或特殊字符标记，同时 index 被更新为在代表这个字符标记之后的第一个字符的索引 (一种特殊情况：一个字面字符后紧接闭包运算，此时输出的标记中不仅含有字面字符，也含有特殊字符闭包)
static character_symbol next_symbol_of_expression(str_view expression, sizevalue& index)
{
    runtime_assert(index < expression.size(), "next_symbol_of_expression 的前置条件不被满足");
    character_symbol symbol{};
    // 当满足以下条件时，说明这是转义字符，要求 index + 1 < expression.size()
    if (expression[index] == STR("\\")[0]) {
        runtime_assert(index + 1 < expression.size(), "next_symbol_of_expression 在识别到转义字符后的条件不被满足");
        index += 2;
        symbol = { escape_character(expression[index - 1]) };
        if (index < expression.size()) {
            if (expression[index] == STR("*")[0]) {
                symbol.functional = STR("*")[0];
            }
        }
        return std::move(symbol);
    }
    // expression[index] != STR("\\")[0]，只能是非转义字面字符或者特殊字符
    if (functional_characters.contains(expression[index])) {
        index += 1;
        symbol = { character_max, expression[index - 1] };
        return std::move(symbol);
    }
    // expression[index] != STR("\\")[0] 且 !functional_characters.contains(expression[index])，只能是非转义字面字符
    index += 1;
    symbol = { expression[index - 1] };
    if (index < expression.size()) {
        if (expression[index] == STR("*")[0]) {
            symbol.functional = STR("*")[0];
        }
    }
    return std::move(symbol);
}

// 逻辑规范：
// 前置条件：无
// 后置条件：输出 'ε' 对应的 expression_information (如果直接后继的字符是'*'，那么使 index 跳过)
static expression_information epsilon(str_view expression, sizevalue& index)
{
    if (index < expression.size()) {
        if (expression[index] == STR("*")[0]) {
            index += 1;
        }
    }
    return expression_information{ {}, {}, {}, {}, true };
}

// 逻辑规范：
// 前置条件：无
// 后置条件：输出 '·' 对应的 expression_information (如果直接后继的字符是'*'，那么使 index 跳过，并输出被闭包修饰的 '·' 的 expression_information)
static expression_information center_dot(str_view expression, sizevalue& index)
{
    if (index < expression.size()) {
        if (expression[index] == STR("*")[0]) {
            index += 1;
            return expression_information{ { state_transition(0, state_transition_type::ANY), state_transition(0) }, { 0 }, { 0 }, { { state_transition(0) } }, true };
        }
    }
    return expression_information{ { state_transition(0, state_transition_type::ANY) }, { 0 }, { 0 }, {}, false };
}

// 逻辑规范：
// 前置条件：expression 中存在与这个左括号对应的右括号
// 后置条件：输出 "(expr)" 中 expr 的 expression_information
static expression_information left_bracket(str_view expression, sizevalue& index)
{
    expression_information information{};
    bool required_escape = false;
    bool finish_correctly = false;
    // 主循环：
    while (index < expression.size()) {
        character_symbol symbol = next_symbol_of_expression(expression, index);
        // 如果是特殊字符标记，进行特殊处理
        if (symbol.is_functional_symbol()) {
            // 当满足以下条件时，说明这对括号的作用域结束了，打破循环
            if (symbol.functional == STR(")")[0]) {
                right_bracket(expression, index);
                finish_correctly = true;
                break;
            }
            expression_information sub_information = functional_characters[symbol.functional](expression, index);
            // 如果是或运算，以取并集的方式连接，否则以正常的首尾相接的方式连接
            symbol.functional == STR("|")[0] ? join_expression_information(information, sub_information) : concatenate_expression_information(information, sub_information);
            continue;
        }
        // 否则是字面字符标记
        if (symbol.functional == STR("*")[0]) {
            // 如果是被闭包修饰的字面字符，进行特殊处理
            literal_character_with_kleene_star(information, state_transition(symbol.c, state_transition_type::DEFAULT));
            index += 1;
            continue;
        }
        vector<sizevalue> temporary_index_of_successors = { information.content.size() };
        connect_predecessors_and_successors(information.content, information.virtual_transitions_table, information.index_of_tails, temporary_index_of_successors);
        information.index_of_tails = { information.content.size() };
        if (information.index_of_heads.empty()) {
            information.index_of_heads = { information.content.size() };
        }
        information.content.push_back(state_transition(symbol.c, state_transition_type::DEFAULT));
    }
    runtime_assert(finish_correctly, "禁止在表达式中使用不成对的左括号");
    // 检测作用域是否被闭包修饰
    if (index < expression.size()) {
        if (expression[index] == STR("*")[0] && !information.content.empty()) {
            // 如果被闭包修饰且 information.content 不为空，进行相关处理
            if (!information.content.back().is_transfer_transition()) {
                // 如果 content 的末尾不是虚转移节点，添加虚转移节点以为闭包的首尾连接做准备
                information.content.push_back(state_transition(information.virtual_transitions_table.size()));
                information.virtual_transitions_table.push_back({});
            }
            // 进行 content 的首尾相连
            connect_predecessors_and_successors(information.content, information.virtual_transitions_table, information.index_of_tails, information.index_of_heads);
            // 修改贯穿标志
            information.exists_escape_transition = true;
        }
    }
    return std::move(information);
}

// 逻辑规范：
// 前置条件：右括号不在表达式开头，不与对应的左括号直接相邻，不是或运算的直接后继，不是反运算的直接后继
// 后置条件：无
static expression_information right_bracket(str_view expression, sizevalue& index)
{
    runtime_assert(index - 1 > 0, "禁止在表达式开头使用右括号");
    runtime_assert(!is_last(expression, index - 2, STR("(")[0]), "禁止在表达式中出现内容为空的一对括号\"()\"");
    runtime_assert(!is_last(expression, index - 2, STR("|")[0]), "禁止在表达式中出现无效的或运算\"...|)\"");
    runtime_assert(!is_last(expression, index - 2, STR("~")[0]), "禁止在表达式中出现无效的反运算\"...~)\"");
    return {};
}

// 逻辑规范：
// 前置条件：或运算不在表达式开头，不是左括号、或运算、反运算的直接后继
// 后置条件：输出 "|expr" 中 expr 的 expression_information
static expression_information alternation(str_view expression, sizevalue& index)
{
    runtime_assert(index - 1 > 0, "禁止在表达式开头使用或运算");
    runtime_assert(!is_last(expression, index - 2, STR("(")[0]), "禁止在表达式中出现无效的或运算\"(|...\"");
    runtime_assert(!is_last(expression, index - 2, STR("|")[0]), "禁止在表达式中出现无效的或运算\"...||...\"");
    runtime_assert(!is_last(expression, index - 2, STR("~")[0]), "禁止在表达式中出现无效的或运算\"...~|...\"");
    expression_information information{};
    bool required_escape = false;
    // 主循环：
    while (index < expression.size()) {
        sizevalue old_index = index;
        character_symbol symbol = next_symbol_of_expression(expression, index);
        // 如果是特殊字符标记，进行特殊处理
        if (symbol.is_functional_symbol()) {
            // 当满足以下条件时，说明这些或运算的作用域结束了，打破循环
            if (symbol.functional == STR(")")[0]) {
                right_bracket(expression, index);
                index = old_index;
                break;
            }
            expression_information sub_information = functional_characters[symbol.functional](expression, index);
            // 如果是或运算，以取并集的方式连接，否则以正常的首尾相接的方式连接
            symbol.functional == STR("|")[0] ? join_expression_information(information, sub_information) : concatenate_expression_information(information, sub_information);
            continue;
        }
        // 否则是字面字符标记
        if (symbol.functional == STR("*")[0]) {
            // 如果是被闭包修饰的字面字符，进行特殊处理
            literal_character_with_kleene_star(information, state_transition(symbol.c, state_transition_type::DEFAULT));
            index += 1;
            continue;
        }
        vector<sizevalue> temporary_index_of_successors = { information.content.size() };
        connect_predecessors_and_successors(information.content, information.virtual_transitions_table, information.index_of_tails, temporary_index_of_successors);
        information.index_of_tails = { information.content.size() };
        if (information.index_of_heads.empty()) {
            information.index_of_heads = { information.content.size() };
        }
        information.content.push_back(state_transition(symbol.c, state_transition_type::DEFAULT));
    }
    return std::move(information);
}

// 逻辑规范：
// 前置条件：闭包运算不在表达式开头，不是左括号、或运算、闭包运算、反运算的直接后继
// 后置条件：无
static expression_information kleene_star(str_view expression, sizevalue& index)
{
    runtime_assert(index - 1 > 0, "禁止在表达式开头使用闭包运算");
    runtime_assert(!is_last(expression, index - 2, STR("(")[0]), "禁止在表达式中出现无效的闭包运算\"(*\"");
    runtime_assert(!is_last(expression, index - 2, STR("|")[0]), "禁止在表达式中出现无效的闭包运算\"|*\"");
    runtime_assert(!is_last(expression, index - 2, STR("*")[0]), "禁止在表达式中出现无效的闭包运算\"**\"");
    runtime_assert(!is_last(expression, index - 2, STR("~")[0]), "禁止在表达式中出现无效的闭包运算\"~*\"");
    return {};
}

// 逻辑规范：
// 前置条件：information 有效
// 后置条件：information 连接上被闭包修饰的 transition
static void literal_character_with_kleene_star(expression_information& information, state_transition transition)
{
    if (!information.content.back().is_transfer_transition()) {
        information.content.push_back(information.virtual_transitions_table.size());
        information.virtual_transitions_table.push_back({});
    }
    vector<sizevalue> temporary_index_of_successors = { information.content.size() };
    connect_predecessors_and_successors(information.content, information.virtual_transitions_table, information.index_of_tails, temporary_index_of_successors);
    information.index_of_tails.push_back(information.content.size());
    if (information.index_of_heads.empty()) {
        information.index_of_heads = { information.content.size() };
    }
    information.content.push_back(transition);
    information.content.push_back(information.virtual_transitions_table.size());
    information.virtual_transitions_table.push_back({ state_transition(information.content.size() - 2) });
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
// 前置条件：index_of_predecessors 中不存在自身不为虚转移节点且后继节点也不为虚转移节点，但是需要转移到 index_of_successors 中不直接相邻的节点的节点
// 后置条件：index_of_predecessors 中指向的所有的虚转移表，其中包含所有指向 index_of_successors 中索引的转移节点 (连接的两个节点直接相邻时省略转移)
static void connect_predecessors_and_successors(finite_automaton& finite_automaton, vector<vector<state_transition>>& virtual_transitions_table, vector<sizevalue>& index_of_predecessors, vector<sizevalue> index_of_successors)
{
    for (auto index_of_predecessor : index_of_predecessors) {
        for (auto index_of_successor : index_of_successors) {
            if (finite_automaton[index_of_predecessor].is_transfer_transition()) {
                virtual_transitions_table[finite_automaton[index_of_predecessor].index()].push_back(state_transition(index_of_successor));
            }
            else if (index_of_predecessor + 1 < finite_automaton.size()) {
                if (finite_automaton[index_of_predecessor + 1].is_transfer_transition()) {
                    virtual_transitions_table[finite_automaton[index_of_predecessor + 1].index()].push_back(state_transition(index_of_successor));
                }
                else {
                    goto last;
                }
            }
            else {
                last:
                // index_of_predecessor + 1 == index_of_successor 成立时即连接的两个节点直接相邻，此时省略转移
                runtime_assert(index_of_predecessor + 1 == index_of_successor, "禁止为没有特殊转移路径的节点添加新的转移路径");
            }
        }
    }
}

// 逻辑规范：
// 前置条件：information 有效
// 后置条件：输出 information 对应的 finite_automaton_context
static finite_automaton_context information_to_finite_automaton_context(expression_information& information)
{
    finite_automaton_context context{};
    // 初始化
    context.virtual_transitions_table = std::move(information.virtual_transitions_table);
    // 将 index_of_heads 变为转移节点
    for (sizevalue i = 0; i < information.index_of_heads.size(); ++i) {
        if (std::count(context.virtual_transitions_table.front().begin(), context.virtual_transitions_table.front().end(), state_transition(information.index_of_heads[i])) == 0) {
            context.virtual_transitions_table.front().push_back(state_transition(information.index_of_heads[i]));
        }
    }
    // 进行主要节点的移动
    context.finite_automaton = std::move(information.content);
    // 将尾部节点连接到自动机的结束状态
    if (!context.finite_automaton.back().is_transfer_transition()) {
        // 如果末尾不是虚转移节点，添加虚转移节点用于连接结束状态
        context.finite_automaton.push_back(context.virtual_transitions_table.size());
        context.virtual_transitions_table.push_back({});
    }
    vector<sizevalue> index_of_end_transition = { sizevalue_max };
    if (information.exists_escape_transition) {
        // 如果需要存在贯穿路径，将起始节点视为尾部，使在连接时出现贯穿转移路径
        information.index_of_tails.push_back(0);
    }
    connect_predecessors_and_successors(context.finite_automaton, context.virtual_transitions_table, information.index_of_tails, index_of_end_transition);
    // 输出
    return std::move(context);
}

// 逻辑规范：
// 前置条件：无
// 后置条件：context.finite_automaton 中的所有虚转移节点都展开为转移节点，且自动机整体的转移路径不变
static void expand_virtual_transition(finite_automaton_context& context)
{
    // 第一遍遍历，建立映射表
    vector<sizevalue> original_index_to_expanded_index(context.finite_automaton.size(), 0); // 索引代表 original_index，值代表 expanded_index
    intmax current_offset = 0;
    for (sizevalue i = 0; i < context.finite_automaton.size(); ++i) {
        // 处理自动机中的虚转移节点
        if (context.finite_automaton[i].is_transfer_transition() && context.finite_automaton[i].index() != sizevalue_max) {
            auto& transitions = context.virtual_transitions_table[context.finite_automaton[i].index()];
            intmax offset_of_this = -1;
            // 如果 transitions 为空，则说明这个虚转移节点不指代任何实际的转移节点，进行直接处理
            if (transitions.empty()) {
                current_offset -= 1;
                continue;
            }
            // 如果虚转移节点修饰的节点的只有到下一个直接相邻节点的转移路径，则跳过处理，采用默认连接的模式。
            auto previous_meaningful_it = context.finite_automaton.begin() + i;
            while (previous_meaningful_it->is_transfer_transition() && previous_meaningful_it != context.finite_automaton.begin()) {
                previous_meaningful_it -= 1;
            }
            if (previous_meaningful_it != context.finite_automaton.begin()) {
                if (previous_meaningful_it - context.finite_automaton.begin() + 1 + 1 == transitions.front().index() && transitions.size() == 1 && transitions.front().is_transfer_transition()) {
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
    vector<state_transition> expanded_finite_automaton{};
    for (sizevalue i = 0; i < context.finite_automaton.size(); ++i) {
        // 如果是虚转移节点，进行展开处理
        if (context.finite_automaton[i].is_transfer_transition() && context.finite_automaton[i].index() != sizevalue_max) {
            sizevalue index_of_virtual_transition = context.finite_automaton[i].index();
            auto& virtual_transitions = context.virtual_transitions_table[index_of_virtual_transition];
            // 如果 virtual_transitions 为空，则说明这个虚转移节点不指代任何实际的转移节点，进行跳过处理
            if (virtual_transitions.empty()) {
                continue;
            }
            // 如果虚转移节点修饰的节点的只有到下一个直接相邻节点的转移路径，则跳过处理，采用默认连接的模式。
            auto previous_meaningful_it = context.finite_automaton.begin() + i;
            while (previous_meaningful_it->is_transfer_transition() && previous_meaningful_it != context.finite_automaton.begin()) {
                previous_meaningful_it -= 1;
            }
            if (previous_meaningful_it != context.finite_automaton.begin()) {
                if (previous_meaningful_it - context.finite_automaton.begin() + 1 + 1 == virtual_transitions.front().index() && virtual_transitions.size() == 1 && virtual_transitions.front().is_transfer_transition()) {
                    continue;
                }
            }
            // 否则全部正常展开
            expanded_finite_automaton.insert(expanded_finite_automaton.end(), virtual_transitions.begin(), virtual_transitions.end());
        }
        // 否则正常添加
        else {
            expanded_finite_automaton.push_back(context.finite_automaton[i]);
        }
    }
    context.finite_automaton = std::move(expanded_finite_automaton); // 将展开后的结果载入上下文

    // 第三遍遍历，将所有的转移路径映射到新转移路径
    for (sizevalue i = 0; i < context.finite_automaton.size(); ++i) {
        if (context.finite_automaton[i].is_transfer_transition() && context.finite_automaton[i].index() >= original_index_to_expanded_index.size()) {
            context.finite_automaton[i] = state_transition(sizevalue_max);
            continue; // 不处理指向结束状态的转移路径
        }
        else if (context.finite_automaton[i].is_transfer_transition()) {
            context.finite_automaton[i] = state_transition(original_index_to_expanded_index[context.finite_automaton[i].index()]);
        }
    }
}