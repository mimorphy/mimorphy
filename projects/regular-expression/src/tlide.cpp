#include <build-regular-table>
#include <basic>
#include <cstddef>
#include <runtime-exception>
#include <state-transition>
#include <concatenate-regular-table>
#include <compute-length>
#include <algorithm>
#include <execution>
#include <vector>
#include <set>

using std::set;

expression_information to_negative(expression_information& information, sizevalue index_of_exception_pool);
expression_information apply_negative_rules(expression_information& information, sizevalue index_of_exception_pool);
void apply_truncated_rule(expression_information& negative_information, vector<sizevalue>& length_array, sizevalue index_of_exception_pool);
expression_information generate_wildcard_information(expression_information& negative_information, sizevalue index_of_exception_pool);
void combine_negative_and_wildcard(expression_information& negative, expression_information& wildcard, sizevalue index_of_exception_pool);
static void join_expression_information(expression_information& target, expression_information& source);

// 逻辑规范：
// 前置条件：ewp 有效
// 后置条件：输出 ~expr 对应的 expression_information
expression_information tlide(expression_with_operation ewp, span<functional_operation> functional_operations, sizevalue index_of_exception_pool)
{
    expression_information body = build_expression_information(ewp.expression.substr(2), functional_operations, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    return to_negative(body, index_of_exception_pool);
}

// 逻辑规范：
// 前置条件：无
// 后置条件：输出反运算修饰的 information 对应的 expression_information
expression_information to_negative(expression_information& information, sizevalue index_of_exception_pool)
{
    expression_information negative_information = apply_negative_rules(information, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    vector<sizevalue> length_array_of_negative_information = compute_length_of_expression_information(negative_information, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    apply_truncated_rule(negative_information, length_array_of_negative_information, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    expression_information wildcard_information = generate_wildcard_information(negative_information, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    combine_negative_and_wildcard(negative_information, wildcard_information, index_of_exception_pool);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    return std::move(negative_information);
}

// 逻辑规范：
// 前置条件：无
// 后置条件：输出 information 经过反运算修饰后的部分内容，不含通配部分，没有长度截断，没有阻塞节点，转移到通配内容的部分使用一个通配节点指代
expression_information apply_negative_rules(expression_information& information, sizevalue index_of_exception_pool)
{
    expression_information result{};

    // 辅助函数：检查节点是否为阻塞节点
    auto is_dead_end = [](const state_transition& node) -> bool {
        return !node.is_transfer_transition() && node.type == state_transition_type::DEAD_END;
    };
    
    // 辅助函数：获取一个状态节点的所有后继节点索引（考虑虚转移表）
    auto get_successors = [&information, &is_dead_end, &index_of_exception_pool](sizevalue node_index) -> vector<sizevalue> {
        vector<sizevalue> successors;
        const regular_table& content = information.content;
        
        // 如果节点是虚转移节点，它本身不拥有后继
        if (content[node_index].is_transfer_transition()) {
            return successors;
        }
        
        // 检查是否为阻塞节点
        if (is_dead_end(content[node_index])) {
            return successors; // 阻塞节点没有后继
        }
        
        sizevalue next_index = node_index + 1;
        // 如果节点是反交集节点，需要特殊处理 next_index
        if (next_index < content.size() && content[node_index].type == state_transition_type::NEGATION_INTERSECTION) {
            while (content[next_index].type == state_transition_type::NEGATION_INTERSECTION) {
                next_index += 1;
                runtime_assert(next_index < content.size(), "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
            }
            runtime_assert(content[next_index].type == state_transition_type::NEGATION, "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            next_index += 1;
        }
        
        // 情况1：检查直接相邻的后继节点（如果存在且不是虚转移节点）
        if (next_index < content.size()) {
            const state_transition& next_node = content[next_index];
            if (!next_node.is_transfer_transition() && !is_dead_end(next_node)) {
                successors.push_back(next_index);
            }
        }
        
        // 情况2：通过紧随其后的虚转移节点获取转移目标
        if (next_index < content.size() && content[next_index].is_transfer_transition()) {
            sizevalue virtual_transition_index = content[next_index].index();
            if (virtual_transition_index < information.virtual_transitions_table.size()) {
                const auto& virtual_transitions = information.virtual_transitions_table[virtual_transition_index];
                for (const state_transition& transition : virtual_transitions) {
                    sizevalue target_index = transition.index();
                    if (target_index < content.size() && !is_dead_end(content[target_index])) {
                        successors.push_back(target_index);
                    }
                }
            }
        }
        
        return successors;
    };

    // 辅助函数：根据 information 的索引 index 节点，输出这个长度为1的节点的反节点
    auto get_negative_state_transition = [&information, &index_of_exception_pool](sizevalue index) -> expression_information {
        expression_information result{};
        if (information.content[index].type == state_transition_type::DEFAULT) {
            auto& default_node = information.content[index];
            result.content.push_back(state_transition(default_node.transition_condition, state_transition_type::NEGATION));
            result.index_of_heads = { 0 };
            result.index_of_tails = { 0 };
        }
        else if (information.content[index].type == state_transition_type::NEGATION) {
            auto& default_node = information.content[index];
            result.content.push_back(state_transition(default_node.transition_condition, state_transition_type::DEFAULT));
            result.index_of_heads = { 0 };
            result.index_of_tails = { 0 };
        }
        else if (information.content[index].type == state_transition_type::NEGATION_INTERSECTION){
            sizevalue i = 0;
            for (i = index; information.content[i].type != state_transition_type::NEGATION; ++i) {
                runtime_assert(information.content[i].type == state_transition_type::NEGATION_INTERSECTION, "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
                result.content.push_back(state_transition(information.content[i].transition_condition, state_transition_type::DEFAULT));
                result.index_of_heads.push_back(result.content.size() - 1);
                result.index_of_tails.push_back(result.content.size() - 1);
                result.content.push_back(state_transition(result.virtual_transitions_table.size()));
                result.virtual_transitions_table.push_back({});
            }
            result.content.push_back(state_transition(information.content[i].transition_condition, state_transition_type::DEFAULT));
            result.index_of_heads.push_back(result.content.size() - 1);
            result.index_of_tails.push_back(result.content.size() - 1);
        }
        else if (information.content[index].type == state_transition_type::ANY) {
            result = { { state_transition(0, state_transition_type::DEAD_END) } };
        }
        return std::move(result);
    };

    // 辅助函数：根据 information 的索引 index_array 中的所有节点，输出它们取并集后取反的结果
    auto get_negative_state_transitions = [&information, &index_of_exception_pool](vector<sizevalue> index_array) -> expression_information {
        expression_information result{};
        vector<character> marked_characters{};
        bool is_complement = false;
        // 预处理
        for (sizevalue index : index_array) {
            auto node = information.content[index];
            if (node.type == state_transition_type::DEAD_END) {
                return { { state_transition(0, state_transition_type::DEAD_END) } };
            }
            if (node.type == state_transition_type::DEFAULT) {
                if (!is_complement) {
                    if (std::count(marked_characters.begin(), marked_characters.end(), node.transition_condition) == 0) {
                        marked_characters.push_back(node.transition_condition);
                    }
                }
                else {
                    auto it = std::find(marked_characters.begin(), marked_characters.end(), node.transition_condition);
                    if (it != marked_characters.end()) {
                        marked_characters.erase(it);
                    }
                }
            }
            else if (node.type == state_transition_type::NEGATION) {
                if (!is_complement) {
                    if (std::find(marked_characters.begin(), marked_characters.end(), node.transition_condition) != marked_characters.end()) {
                        is_complement = true;
                        marked_characters.clear();
                    }
                    else {
                        is_complement = true;
                        marked_characters = { node.transition_condition };
                    }
                }
                else {
                    if (std::find(marked_characters.begin(), marked_characters.end(), node.transition_condition) != marked_characters.end()) {
                        marked_characters = { node.transition_condition };
                    }
                    else {
                        marked_characters.clear();
                    }
                }
            }
            else if (node.type == state_transition_type::NEGATION_INTERSECTION) {
                vector<character> related_characters{};
                sizevalue i = index;
                while (information.content[i].type == state_transition_type::NEGATION_INTERSECTION) {
                    if (std::count(related_characters.begin(), related_characters.end(), information.content[i].transition_condition) == 0) {
                        related_characters.push_back(information.content[i].transition_condition);
                    }
                }
                runtime_assert(information.content[i].type == state_transition_type::NEGATION, "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
                if (std::count(related_characters.begin(), related_characters.end(), information.content[i].transition_condition) == 0) {
                    related_characters.push_back(information.content[i].transition_condition);
                }
                if (!is_complement) {
                    is_complement = true;
                    marked_characters.clear();
                    for (i = 0; i < related_characters.size(); ++i) {
                        auto it = std::find(marked_characters.begin(), marked_characters.end(), node.transition_condition);
                        if (it == marked_characters.end() && std::count(marked_characters.begin(), marked_characters.end(), related_characters[i]) == 0) {
                            marked_characters.push_back(related_characters[i]);
                        }
                    }
                }
                else {
                    for (i = 0; i < related_characters.size(); ++i) {
                        auto it = std::find(marked_characters.begin(), marked_characters.end(), node.transition_condition);
                        if (it == marked_characters.end()) {
                            marked_characters.erase(it);
                        }
                    }
                }
            }
        }
        // 生成结果
        if (is_complement) {
            for (character marked_character : marked_characters) {
                result.content.push_back(state_transition(marked_character, state_transition_type::DEFAULT));
                result.index_of_heads.push_back(result.content.size() - 1);
                result.index_of_tails.push_back(result.content.size() - 1);
                result.content.push_back(state_transition(result.virtual_transitions_table.size()));
                result.virtual_transitions_table.push_back({});
            }
        }
        else if (!marked_characters.empty()) {
            for (character marked_character : marked_characters) {
                result.content.push_back(state_transition(marked_character, state_transition_type::NEGATION_INTERSECTION));
            }
            result.content.back().type = state_transition_type::NEGATION;
            result.index_of_heads = { 0 };
            result.index_of_tails = { 0 };
        }
        return std::move(result);
    };

    // 辅助函数：如果 information 的 content 的索引 index 节点仅和一个节点线性相邻，应用线性的顺序规则，得到对应的 expression_information (不含后继反运算结构)
    auto apply_linear_rule = [&information, &get_negative_state_transition, &index_of_exception_pool](sizevalue index) -> expression_information {
        auto negative = get_negative_state_transition(index);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        if (!negative.content.empty()) {
            if (negative.content[0].type == state_transition_type::DEAD_END) {
                return { { state_transition(0, state_transition_type::DEAD_END) } };
            }
        }
        negative.content.push_back(state_transition(0, state_transition_type::ANY));
        negative.index_of_heads.push_back(negative.content.size());
        negative.index_of_tails = { negative.content.size() };
        if (information.content[index].type != state_transition_type::NEGATION_INTERSECTION) {
            negative.content.push_back(information.content[index]);
        }
        else {
            sizevalue i = 0;
            for (i = index; information.content[i].type != state_transition_type::NEGATION; ++i) {
                negative.content.push_back(information.content[i]);
            }
            negative.content.push_back(information.content[i]);
        }
        return std::move(negative);
    };

    // 如果 information 的 content 的索引 index_array 这些节点是并关系，应用分支的规则，得到对应的 expression_information
    auto apply_branched_rule = [&information, &get_successors, &get_negative_state_transition, &get_negative_state_transitions, &index_of_exception_pool](vector<sizevalue>& index_array, auto&& apply, auto&& self) -> expression_information {
        expression_information result{}; 
        // 构建长度为1后继通配的分支
        result = get_negative_state_transitions(index_array);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        if (!result.content.empty()) {
            if (result.content[0].type != state_transition_type::DEAD_END) {
                expression_information one_any = {
                    { state_transition(0, state_transition_type::ANY) },
                    { 0 },
                    { 0 },
                    {},
                    false
                };
                concatenate_expression_information(result, one_any);
            }
        }
        vector<expression_information> branches(index_array.size());
        vector<std::pair<sizevalue, sizevalue>> building_information(index_array.size());
        for (sizevalue i = 0; i < building_information.size(); ++i) {
            building_information[i] = { index_array[i], i };
        }
        // 构建其他分支的函数
        auto build_other_branches = [&information, &get_successors, &apply, &self, &branches, &index_of_exception_pool](std::pair<sizevalue, sizevalue> node_index_and_position) {
            sizevalue node_index = node_index_and_position.first;
            sizevalue position = node_index_and_position.second;
            // 加载第一个节点
            if (information.content[node_index].type != state_transition_type::NEGATION_INTERSECTION) {
                branches[position] = { { information.content[node_index] }, { 0 }, { 0 } };
            }
            else {
                sizevalue i = 0;
                for (i = node_index; information.content[i].type != state_transition_type::NEGATION; ++i) {
                    branches[position].content.push_back(information.content[i]);
                }
                branches[position].content.push_back(information.content[i]);
                branches[position].index_of_heads = { 0 };
                branches[position].index_of_tails = { 0 };
            }
            // 获取后继节点
            auto successors = get_successors(node_index);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return;
            }
            if (successors.empty()) {
                branches[position] = {};
                return;
            }
            // 根据后继节点的数量，选择函数进行后续结构的构建，最后进行连接
            expression_information next = successors.size() == 1 ? apply(successors[0], apply) : self(successors, apply, self);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return;
            }
            if (!next.content.empty()) {
                if (next.content[0].type == state_transition_type::DEAD_END) {
                    branches[position] = {};
                    return;
                }
            }
            concatenate_expression_information(branches[position], next);
        };
        std::for_each(std::execution::par, building_information.begin(), building_information.end(), build_other_branches);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        // 进行并运算连接
        for (sizevalue i = 0; i < branches.size(); ++i) {
            join_expression_information(result, branches[i]);
        }
        return std::move(result);
    };

    // 应用规则的主函数
    auto apply = [&information, &get_successors, &apply_linear_rule, &apply_branched_rule, &is_dead_end, &get_negative_state_transition, &index_of_exception_pool](sizevalue current_index, auto&& self) -> expression_information {
        expression_information result{};
        if (is_dead_end(information.content[current_index]) || information.content[current_index].type == state_transition_type::ANY) {
            return { { state_transition(0, state_transition_type::DEAD_END) } };
        }
        auto successors = get_successors(current_index);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        if (successors.empty()) {
            auto st = get_negative_state_transition(current_index);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            return st;
        }
        if (successors.size() == 1) {
            // 应用线性规则
            result = apply_linear_rule(current_index);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            expression_information next = self(successors[0], self);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            // 判断是否遇到阻塞
            if (!next.content.empty()) {
                if (is_dead_end(next.content[0])) {
                    return { { state_transition(0, state_transition_type::DEAD_END) } };
                }
            }
            concatenate_expression_information(result, next);
        }
        else {
            result = apply_branched_rule(successors, self, apply_branched_rule);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
        }
        return std::move(result);
    };

    result = information.index_of_heads.size() == 1 ? apply(information.index_of_heads[0], apply) : apply_branched_rule(information.index_of_heads, apply, apply_branched_rule);
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    return std::move(result);
}

// 逻辑规范：
// 前置条件：negative_information 的每个字面节点后方都有通配符节点或者虚转移节点，且不含阻塞节点
// 后置条件：negative_information 中的所有长度到达 length in length_array 的部分都被截断，记录到 index_of_tails 中
void apply_truncated_rule(expression_information& negative_information, vector<sizevalue>& length_array, sizevalue index_of_exception_pool)
{
    // 辅助函数：获取一个状态节点的所有后继节点索引（考虑虚转移表）
    auto get_successors = [&negative_information, &index_of_exception_pool](sizevalue node_index) -> vector<sizevalue> {
        vector<sizevalue> successors;
        const regular_table& content = negative_information.content;
        
        // 如果节点是虚转移节点，它本身不拥有后继
        if (content[node_index].is_transfer_transition()) {
            return successors;
        }
        
        sizevalue next_index = node_index + 1;
        // 如果节点是反交集节点，需要特殊处理 next_index
        if (next_index < content.size() && content[node_index].type == state_transition_type::NEGATION_INTERSECTION) {
            while (content[next_index].type == state_transition_type::NEGATION_INTERSECTION) {
                next_index += 1;
                runtime_assert(next_index < content.size(), "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
            }
            runtime_assert(content[next_index].type == state_transition_type::NEGATION, "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            next_index += 1;
        }
        
        // 情况1：检查直接相邻的后继节点（如果存在且不是虚转移节点）
        if (next_index < content.size()) {
            const state_transition& next_node = content[next_index];
            if (!next_node.is_transfer_transition()) {
                successors.push_back(next_index);
            }
        }
        
        // 情况2：通过紧随其后的虚转移节点获取转移目标
        if (next_index < content.size() && content[next_index].is_transfer_transition()) {
            sizevalue virtual_transition_index = content[next_index].index();
            if (virtual_transition_index < negative_information.virtual_transitions_table.size()) {
                const auto& virtual_transitions = negative_information.virtual_transitions_table[virtual_transition_index];
                for (const state_transition& transition : virtual_transitions) {
                    sizevalue target_index = transition.index();
                    if (target_index < content.size()) {
                        successors.push_back(target_index);
                    }
                }
            }
        }
        
        return successors;
    };

    set<sizevalue> current_index_set(negative_information.index_of_heads.begin(), negative_information.index_of_heads.end());
    sizevalue current_length = 0;
    for (sizevalue length : length_array) {
        if (length == 0) {
            continue;
        }
        for (sizevalue current_index : current_index_set) {
            current_index_set.erase(current_index);
            auto successors = get_successors(current_index);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return;
            }
            if (current_length == length) {
                std::for_each(successors.begin(), successors.end(), [&negative_information](sizevalue index) {
                    if (std::count(negative_information.index_of_tails.begin(), negative_information.index_of_tails.end(), index) == 0) {
                        negative_information.index_of_tails.push_back(index);
                    }
                });
            }
            current_index_set.insert(successors.begin(), successors.end());
        }
        ++current_length;
    }
}

// 逻辑规范：
// 前置条件：negative_information 不含阻塞节点，且有效
// 后置条件：输出所有字面节点变为通配符节点，且去除所有 index_of_heads 中指向的节点的与 negative_information 对应的通配信息结构
expression_information generate_wildcard_information(expression_information& negative_information, sizevalue index_of_exception_pool)
{
    // 辅助函数：获取一个状态节点的所有后继节点索引（考虑虚转移表）
    auto get_successors = [&negative_information, &index_of_exception_pool](sizevalue node_index) -> vector<sizevalue> {
        vector<sizevalue> successors;
        const regular_table& content = negative_information.content;
        
        // 如果节点是虚转移节点，它本身不拥有后继
        if (content[node_index].is_transfer_transition()) {
            return successors;
        }
        
        sizevalue next_index = node_index + 1;
        // 如果节点是反交集节点，需要特殊处理 next_index
        if (next_index < content.size() && content[node_index].type == state_transition_type::NEGATION_INTERSECTION) {
            while (content[next_index].type == state_transition_type::NEGATION_INTERSECTION) {
                next_index += 1;
                runtime_assert(next_index < content.size(), "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
            }
            runtime_assert(content[next_index].type == state_transition_type::NEGATION, "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            next_index += 1;
        }
        
        // 情况1：检查直接相邻的后继节点（如果存在且不是虚转移节点）
        if (next_index < content.size()) {
            const state_transition& next_node = content[next_index];
            if (!next_node.is_transfer_transition()) {
                successors.push_back(next_index);
            }
        }
        
        // 情况2：通过紧随其后的虚转移节点获取转移目标
        if (next_index < content.size() && content[next_index].is_transfer_transition()) {
            sizevalue virtual_transition_index = content[next_index].index();
            if (virtual_transition_index < negative_information.virtual_transitions_table.size()) {
                const auto& virtual_transitions = negative_information.virtual_transitions_table[virtual_transition_index];
                for (const state_transition& transition : virtual_transitions) {
                    sizevalue target_index = transition.index();
                    if (target_index < content.size()) {
                        successors.push_back(target_index);
                    }
                }
            }
        }
        
        return successors;
    };

    // 递归生成通配信息结构
    auto generate = [&negative_information, &get_successors, &index_of_exception_pool](sizevalue index, auto&& self) -> expression_information {
        expression_information result{};
        result.index_of_heads.push_back(0);
        while (index < negative_information.content.size()) {
            result.content.push_back(state_transition(0, state_transition_type::ANY));
            // 如果这个索引处被截断，生成的通配结构在此处也应该被截断，因此先后继虚转移节点进行铺垫
            if (std::count(negative_information.index_of_tails.begin(), negative_information.index_of_tails.end(), index) != 0) {
                result.content.push_back(state_transition(result.virtual_transitions_table.size()));
                result.virtual_transitions_table.push_back({});
            }
            auto successors = get_successors(index); // 获取后继
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            // 去除是通配符的后继
            for (sizevalue i = successors.size() - 1; i != sizevalue_max; --i) {
                if (negative_information.content[successors[i]].type == state_transition_type::ANY) {
                    successors.erase(successors.begin() + i);
                }
            }
            // 如果后继为空，跳出循环
            if (successors.empty()) {
                break;
            }
            // 如果后继只有一个，那么说明还是线性的结构，继续循环生成
            else if (successors.size() == 1) {
                index = successors[0];
                if (negative_information.content[index].type == state_transition_type::ANY) {
                    return {}; // 对于结尾是通配节点的线性结构，不进行生成
                }
            }
            // 否则说明是分支的结构，分批递归处理，然后结束
            else {
                result.index_of_tails.push_back(result.content.size() - 1);
                vector<expression_information> branches(successors.size());
                struct branch_information {
                    sizevalue index_of_node;
                    sizevalue position;
                };
                vector<branch_information> branch_informations(branches.size());
                for (sizevalue i = 0; i < branches.size(); ++i) {
                    branch_informations.push_back({ successors[i], i });
                }
                auto generate_branches = [&branches, &self](branch_information& brinfo) {
                    branches[brinfo.position] = self(brinfo.index_of_node, self);
                };
                // 递归处理
                std::for_each(std::execution::par, branch_informations.begin(), branch_informations.end(), generate_branches);
                // 进行并运算连接
                for (sizevalue i = 1; i < branches.size(); ++i) {
                    join_expression_information(branches.front(), branches[i]);
                }
                // 连接到结果中
                concatenate_expression_information(result, branches.front());
                break;
            }
        }
        return std::move(result);
    };

    expression_information wildcard_information{};
    vector<sizevalue> index_of_second_nodes{}; // 存储所有第二个节点(head 后继的节点)的索引
    // 获取第二个节点的索引
    for (sizevalue head : negative_information.index_of_heads) {
        auto successors = get_successors(head);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        for (sizevalue successor : successors) {
            if (negative_information.content[successor].type == state_transition_type::ANY) {
                continue; // 不获取通配节点的索引
            }
            if (std::count(index_of_second_nodes.begin(), index_of_second_nodes.end(), successor) == 0) {
                index_of_second_nodes.push_back(successor);
            }
        }
    }
    vector<expression_information> branches(index_of_second_nodes.size()); // 存储所有第二个节点引出的分支
    struct branch_information {
        sizevalue index_of_node;
        sizevalue position;
    };
    vector<branch_information> start_informations(index_of_second_nodes.size());
    for (sizevalue i = 0; i < index_of_second_nodes.size(); ++i) {
        start_informations.push_back({ index_of_second_nodes[i], i });
    }
    // 开始生成
    std::for_each(std::execution::par, start_informations.begin(), start_informations.end(), [&branches, &generate](branch_information& brinfo) { branches[brinfo.position] = generate(brinfo.index_of_node, generate); });
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return {};
    }
    // 进行并运算连接
    for (sizevalue i = 1; i < branches.size(); ++i) {
        join_expression_information(branches.front(), branches[i]);
    }
    // 连接到结果中
    concatenate_expression_information(wildcard_information, branches.front());

    // 添加截断到 index_of_tails 中
    for (sizevalue i = 0; i < wildcard_information.content.size(); ++i) {
        if (wildcard_information.content[i].is_transfer_transition()) {
            if (wildcard_information.virtual_transitions_table[wildcard_information.content[i].index()].empty()) {
                wildcard_information.index_of_tails.push_back(i);
            }
        }
    }
    return std::move(wildcard_information);
}

// 逻辑规范：
// 前置条件：negative, wildcard 有效对应
// 后置条件：negative 连接上 wildcard，同时 negative 中的通配节点变为指向 wildcard 对应处的虚转移节点
void combine_negative_and_wildcard(expression_information& negative, expression_information& wildcard, sizevalue index_of_exception_pool)
{
    // 辅助函数：获取一个状态节点的所有后继节点索引（考虑虚转移表）
    auto get_successors = [&index_of_exception_pool](expression_information& information, sizevalue node_index) -> vector<sizevalue> {
        vector<sizevalue> successors;
        const regular_table& content = information.content;
        
        // 如果节点是虚转移节点，它本身不拥有后继
        if (content[node_index].is_transfer_transition()) {
            return successors;
        }
        
        sizevalue next_index = node_index + 1;
        // 如果节点是反交集节点，需要特殊处理 next_index
        if (next_index < content.size() && content[node_index].type == state_transition_type::NEGATION_INTERSECTION) {
            while (content[next_index].type == state_transition_type::NEGATION_INTERSECTION) {
                next_index += 1;
                runtime_assert(next_index < content.size(), "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return {};
                }
            }
            runtime_assert(content[next_index].type == state_transition_type::NEGATION, "禁止出现不以NEGATION节点为结尾的NEGATION_INTERSECTION组");
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            next_index += 1;
        }
        
        // 情况1：检查直接相邻的后继节点（如果存在且不是虚转移节点）
        if (next_index < content.size()) {
            const state_transition& next_node = content[next_index];
            if (!next_node.is_transfer_transition()) {
                successors.push_back(next_index);
            }
        }
        
        // 情况2：通过紧随其后的虚转移节点获取转移目标
        if (next_index < content.size() && content[next_index].is_transfer_transition()) {
            sizevalue virtual_transition_index = content[next_index].index();
            if (virtual_transition_index < information.virtual_transitions_table.size()) {
                const auto& virtual_transitions = information.virtual_transitions_table[virtual_transition_index];
                for (const state_transition& transition : virtual_transitions) {
                    sizevalue target_index = transition.index();
                    if (target_index < content.size()) {
                        successors.push_back(target_index);
                    }
                }
            }
        }
        
        return successors;
    };

    // 辅助函数：判断当前后继的结构是否是反运算修饰规则形成的结构 (第一个分支是一个长度为1的表达式后继通配节点)
    auto is_negative_structure = [&index_of_exception_pool, &get_successors](expression_information& information, vector<sizevalue>& successors) -> bool {
        if (successors.empty()) {
            return false;
        }
        auto next_successors = get_successors(information, successors[0]);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return {};
        }
        sizevalue final_unique_successor = sizevalue_max;
        for (sizevalue successor : next_successors) {
            auto final_successors = get_successors(information, successor);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            if (final_successors.size() != 1) {
                return false;
            }
            if (final_unique_successor == sizevalue_max) {
                final_unique_successor = final_successors[0];
            }
            else if (final_unique_successor != final_successors[0]) {
                return false;
            }
        }
        return information.content[final_unique_successor].type == state_transition_type::ANY;
    };

    // 辅助函数：修改 negative 中的通配节点变为指向 wildcard 对应处的虚转移节点
    auto modify = [&negative, &wildcard, &index_of_exception_pool, &get_successors, &is_negative_structure](sizevalue index_of_negative, vector<sizevalue> index_array_of_wildcard, auto&& self) {
        while (index_of_negative < negative.content.size()) {
            auto negative_successors = get_successors(negative, index_of_negative);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return;
            }
            if (negative_successors.empty()) {
                return;
            }
            // 不是反运算修饰规则形成的结构
            if (!is_negative_structure(negative, negative_successors)) {
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return;
                }
                if (negative_successors.empty()) {
                    return;
                }
                // 线性
                else if (negative_successors.size() == 1) {
                    index_of_negative = negative_successors[0];
                    vector<sizevalue> next_index_array_of_wildcard{};
                    for (sizevalue index_of_wildcard : index_array_of_wildcard) {
                        auto part = get_successors(wildcard, index_of_wildcard);
                        if (length_of_exception_pool(index_of_exception_pool) != 0) {
                            return;
                        }
                        next_index_array_of_wildcard.insert(next_index_array_of_wildcard.end(), part.begin(), part.end());
                    }
                    index_array_of_wildcard = std::move(next_index_array_of_wildcard);
                }
                // 非线性
                else {
                    vector<sizevalue> next_index_array_of_wildcard{};
                    for (sizevalue index_of_wildcard : index_array_of_wildcard) {
                        auto part = get_successors(wildcard, index_of_wildcard);
                        if (length_of_exception_pool(index_of_exception_pool) != 0) {
                            return;
                        }
                        next_index_array_of_wildcard.insert(next_index_array_of_wildcard.end(), part.begin(), part.end());
                    }
                    index_array_of_wildcard = std::move(next_index_array_of_wildcard);
                    std::for_each(std::execution::par, negative_successors.begin(), negative_successors.end(), [&self, &next_index_array_of_wildcard](sizevalue successor) { self(successor, next_index_array_of_wildcard, self); });
                    return;
                }
            }
            // 是反运算线性修饰规则形成的结构
            else if (negative_successors.size() <= 2) {
                // 修改通配节点
                sizevalue index_of_wildcard_node_in_neagtive = negative_successors.front();
                negative.content[index_of_wildcard_node_in_neagtive] = state_transition(negative.virtual_transitions_table.size());
                negative.virtual_transitions_table.push_back({});
                for (sizevalue index_of_wildcard : index_array_of_wildcard) {
                    negative.virtual_transitions_table.back().push_back(negative.content.size() + index_of_wildcard);
                }
                // 更新 index_of_negative
                index_of_negative = negative_successors.back();
                // 获取 wildcard 的进一步后继
                vector<sizevalue> next_index_array_of_wildcard{};
                for (sizevalue index_of_wildcard : index_array_of_wildcard) {
                    auto part = get_successors(wildcard, index_of_wildcard);
                    if (length_of_exception_pool(index_of_exception_pool) != 0) {
                        return;
                    }
                    next_index_array_of_wildcard.insert(next_index_array_of_wildcard.end(), part.begin(), part.end());
                }
                index_array_of_wildcard = std::move(next_index_array_of_wildcard);
            }
            // 是反运算分支修饰规则形成的结构
            else {
                // 修改通配节点
                sizevalue index_of_wildcard_node_in_neagtive = negative_successors.front();
                negative.content[index_of_wildcard_node_in_neagtive] = state_transition(negative.virtual_transitions_table.size());
                negative.virtual_transitions_table.push_back({});
                for (sizevalue index_of_wildcard : index_array_of_wildcard) {
                    negative.virtual_transitions_table.back().push_back(negative.content.size() + index_of_wildcard);
                }
                // 递归处理分支
                struct index_and_ordinal_number {
                    sizevalue index;
                    sizevalue ordinal_number;
                };
                vector<index_and_ordinal_number> brinfo(negative_successors.size() - 1);
                for (sizevalue i = 1; i < negative_successors.size(); ++i) {
                    brinfo[i - 1] = { negative_successors[i], i - 1 };
                }
                std::for_each(std::execution::par, brinfo.begin(), brinfo.end(), [&self, &index_array_of_wildcard](index_and_ordinal_number& info) { self(info.index, { index_array_of_wildcard[info.ordinal_number] }, self); });
                return;
            }
        }
    };

    // 确保 negative 以虚转移节点结尾
    if (negative.content.empty()) {
        return;
    }
    if (!negative.content.back().is_transfer_transition()) {
        negative.content.push_back(state_transition(negative.virtual_transitions_table.size()));
        negative.virtual_transitions_table.push_back({});
    }
    vector<sizevalue> index_of_second_nodes{}; // 存储所有第二个节点(head 后继的节点)的索引
    // 获取第二个节点的索引
    for (sizevalue head : negative.index_of_heads) {
        auto successors = get_successors(negative, head);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return;
        }
        for (sizevalue successor : successors) {
            if (negative.content[successor].type == state_transition_type::ANY) {
                continue; // 不获取通配节点的索引
            }
            if (std::count(index_of_second_nodes.begin(), index_of_second_nodes.end(), successor) == 0) {
                index_of_second_nodes.push_back(successor);
            }
        }
    }
    // 生成用于递归的信息
    struct index_pair {
        sizevalue index1;
        sizevalue index2;
    };
    vector<index_pair> brinfo(index_of_second_nodes.size());
    for (sizevalue i = 0; i < index_of_second_nodes.size(); ++i) {
        brinfo[i] = { index_of_second_nodes[i], wildcard.index_of_heads[i] };
    }
    // 进行递归修改
    std::for_each(std::execution::par, brinfo.begin(), brinfo.end(), [&modify](index_pair& p) { modify(p.index1, { p.index2 }, modify); });
    // 进行连接
    concatenate_expression_information(negative, wildcard);
}

// 逻辑规范：
// 前置条件：target, source 皆有效
// 后置条件：target 和 source 取并集作为结果赋值到 target 中
static void join_expression_information(expression_information& target, expression_information& source)
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

static API::expression_information* build_api_expression_information(expression_information information)
{
    API::expression_information* result = new API::expression_information();
    // 初始化 table
    result->pointer_of_table = reinterpret_cast<address>(new state_transition[information.content.size()]());
    std::memcpy(reinterpret_cast<void*>(result->pointer_of_table), information.content.data(), information.content.size() * sizeof(state_transition));
    result->length_of_table = information.content.size();
    // 初始化尾部
    result->pointer_of_index_of_tails = reinterpret_cast<address>(new sizevalue[information.index_of_tails.size()]());
    std::memcpy(reinterpret_cast<void*>(result->pointer_of_index_of_tails), information.index_of_tails.data(), information.index_of_tails.size() * sizeof(sizevalue));
    result->length_of_index_of_tails = information.index_of_tails.size();
    // 初始化头部
    result->pointer_of_index_of_heads = reinterpret_cast<address>(new sizevalue[information.index_of_heads.size()]());
    std::memcpy(reinterpret_cast<void*>(result->pointer_of_index_of_heads), information.index_of_heads.data(), information.index_of_heads.size() * sizeof(sizevalue));
    result->length_of_index_of_heads = information.index_of_heads.size();
    // 初始化虚转移表
    result->pointer_of_virtual_transitions_table = reinterpret_cast<address>(new API::regular_table[information.virtual_transitions_table.size()]());
    result->length_of_virtual_transitions_table = information.virtual_transitions_table.size();
    API::regular_table* virtual_transitions_table = reinterpret_cast<API::regular_table*>(result->pointer_of_virtual_transitions_table);
    for (sizevalue i = 0; i < result->length_of_virtual_transitions_table; ++i) {
        virtual_transitions_table[i].pointer_of_table = reinterpret_cast<address>(new state_transition[information.virtual_transitions_table[i].size()]());
        memcpy(reinterpret_cast<void*>(virtual_transitions_table[i].pointer_of_table), information.virtual_transitions_table[i].data(), information.virtual_transitions_table[i].size() * sizeof(state_transition));
        virtual_transitions_table[i].length_of_table = information.virtual_transitions_table[i].size();
    }
    // 初始化被贯穿标志
    result->exists_escape_transition = information.exists_escape_transition;
    return result;
};

namespace API
{
    API::expression_information* tlide(address pointer_of_expression, sizevalue length_of_expression, sizevalue index_of_operation, sizevalue operation_id, address pointer_of_functional_operations, sizevalue length_of_functional_operations, sizevalue index_of_exception_pool)
    {
        auto information = tlide(::expression_with_operation{str_view(reinterpret_cast<character*>(pointer_of_expression), length_of_expression), index_of_operation, operation_id}, span<functional_operation>(reinterpret_cast<functional_operation*>(pointer_of_functional_operations), length_of_functional_operations), index_of_exception_pool);
        return build_api_expression_information(information);
    }
}