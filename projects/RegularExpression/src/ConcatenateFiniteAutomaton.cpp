#include "ConcatenateFiniteAutomaton"
#include "Basic"
#include "StateTransition"
#include "RuntimeException"
#include "algorithm"

static void connect_predecessors_and_successors(finite_automaton& finite_automaton, vector<vector<state_transition>>& virtual_transitions_table, vector<sizevalue>& index_of_predecessors, vector<sizevalue> index_of_successors);

// 逻辑规范：
// 前置条件：target, source 皆有效
// 后置条件：target 连接上 source 作为结果
void concatenate_expression_information(expression_information& target, expression_information& source)
{
    // 如果 target 为空，直接复制返回
    if (target.content.empty()) {
        target = source;
        return;
    }
    // 如果 source 为空，直接返回
    if (source.content.empty()) {
        return;
    }
    // 如果 target 不为空，且最后一个节点不是虚转移节点，添加末尾的虚转移节点
    if (!target.content.back().is_transfer_transition()) {
        target.content.push_back(target.virtual_transitions_table.size());
        target.virtual_transitions_table.push_back({});
    }
    sizevalue offset_of_source = target.content.size();
    sizevalue offset_of_virtual_table = target.virtual_transitions_table.size();
    // 进行节点衔接
    target.content.insert(target.content.end(), source.content.begin(), source.content.end());
    // 进行虚转移表的衔接
    target.virtual_transitions_table.insert(target.virtual_transitions_table.end(), source.virtual_transitions_table.begin(), source.virtual_transitions_table.end());
    // 首尾相连
    vector<sizevalue> new_index_of_heads_of_source = source.index_of_heads;
    std::for_each(new_index_of_heads_of_source.begin(), new_index_of_heads_of_source.end(), [&offset_of_source](sizevalue& index) { index += offset_of_source; });
    connect_predecessors_and_successors(target.content, target.virtual_transitions_table, target.index_of_tails, new_index_of_heads_of_source);
    // 遍历新部分的状态节点
    for (sizevalue i = offset_of_source; i < target.content.size(); ++i) {
        // 如果是虚转移节点，修正索引为其在新虚转移表中的索引
        if (target.content[i].is_transfer_transition()) {
            target.content[i] = state_transition(target.content[i].index() + offset_of_virtual_table);
        }
    }
    // 遍历新部分的虚转移表
    for (sizevalue i = offset_of_virtual_table; i < target.virtual_transitions_table.size(); ++i) {
        // 修正新部分虚转移表中的转移路径的索引
        std::for_each(target.virtual_transitions_table[i].begin(), target.virtual_transitions_table[i].end(), [&offset_of_source](state_transition& st) { st = state_transition(st.index() + offset_of_source); });
    }
    // 如果满足 target.exists_escape_transition == true 或者 target 的头部为空，则将 source 的头部添加到总头部
    if (target.exists_escape_transition || target.index_of_heads.empty()) {
        target.index_of_heads.insert(target.index_of_heads.end(), new_index_of_heads_of_source.begin(), new_index_of_heads_of_source.end());
    }
    // 如果满足 source.exists_escape_transition == true，则将 target 的尾部等价于总尾部，否则清空
    if (!source.exists_escape_transition) {
        target.index_of_tails.clear();
    }
    // 进行尾部的更改
    vector<sizevalue> new_index_of_tails_of_source = source.index_of_tails;
    std::for_each(new_index_of_tails_of_source.begin(), new_index_of_tails_of_source.end(), [&offset_of_source](sizevalue& index) { index += offset_of_source; });
    target.index_of_tails.insert(target.index_of_tails.end(), new_index_of_tails_of_source.begin(), new_index_of_tails_of_source.end());
    // 判断是否仍然存在贯穿的转移路径
    target.exists_escape_transition = target.exists_escape_transition && source.exists_escape_transition;
}

// 逻辑规范：
// 前置条件：target, source 皆有效
// 后置条件：target 和 source 取并集作为结果
void join_expression_information(expression_information& target, expression_information& source)
{
    // 如果 target 为空，直接复制返回
    if (target.content.empty()) {
        bool target_has_escape_transition = target.exists_escape_transition;
        target = source;
        target.exists_escape_transition = target_has_escape_transition || source.exists_escape_transition;
        return;
    }
    // 如果 source 为空，直接返回
    if (source.content.empty()) {
        target.exists_escape_transition = target.exists_escape_transition || source.exists_escape_transition;
        return;
    }
    // 如果 target 不为空，且最后一个节点不是虚转移节点，添加末尾的虚转移节点
    if (!target.content.back().is_transfer_transition()) {
        target.content.push_back(target.virtual_transitions_table.size());
        target.virtual_transitions_table.push_back({});
    }
    sizevalue offset_of_source = target.content.size();
    sizevalue offset_of_virtual_table = target.virtual_transitions_table.size();
    // 进行节点衔接
    target.content.insert(target.content.end(), source.content.begin(), source.content.end());
    // 进行虚转移表的衔接
    target.virtual_transitions_table.insert(target.virtual_transitions_table.end(), source.virtual_transitions_table.begin(), source.virtual_transitions_table.end());
    // 遍历新部分的状态节点
    for (sizevalue i = offset_of_source; i < target.content.size(); ++i) {
        // 如果是虚转移节点，修正索引为其在新虚转移表中的索引
        if (target.content[i].is_transfer_transition()) {
            target.content[i] = state_transition(target.content[i].index() + offset_of_virtual_table);
        }
    }
    // 遍历新部分的虚转移表
    for (sizevalue i = offset_of_virtual_table; i < target.virtual_transitions_table.size(); ++i) {
        // 修正新部分虚转移表中的转移路径的索引
        std::for_each(target.virtual_transitions_table[i].begin(), target.virtual_transitions_table[i].end(), [&offset_of_source](state_transition& st) { st = state_transition(st.index() + offset_of_source); });
    }
    // 进行首尾的叠加
    vector<sizevalue> new_index_of_heads_of_source = source.index_of_heads;
    std::for_each(new_index_of_heads_of_source.begin(), new_index_of_heads_of_source.end(), [&offset_of_source](sizevalue& index) { index += offset_of_source; });
    target.index_of_heads.insert(target.index_of_heads.end(), new_index_of_heads_of_source.begin(), new_index_of_heads_of_source.end());
    vector<sizevalue> new_index_of_tails_of_source = source.index_of_tails;
    std::for_each(new_index_of_tails_of_source.begin(), new_index_of_tails_of_source.end(), [&offset_of_source](sizevalue& index) { index += offset_of_source; });
    target.index_of_tails.insert(target.index_of_tails.end(), new_index_of_tails_of_source.begin(), new_index_of_tails_of_source.end());
    // 判断是否存在贯穿的转移路径
    target.exists_escape_transition = target.exists_escape_transition || source.exists_escape_transition;
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