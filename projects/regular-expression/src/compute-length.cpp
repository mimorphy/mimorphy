#include <compute-length>
#include <basic>
#include <algorithm>
#include <execution>
#include <unordered_set>
#include <stack>
#include <runtime-exception>

using std::stack;
using std::unordered_set;

// 逻辑规范：
// 前置条件：information 有效且无环
// 后置条件：输出 information 的所有可能长度
vector<sizevalue> compute_length_of_expression_information(expression_information& information, sizevalue index_of_exception_pool)
{
    vector<sizevalue> length_array{};
    
    // 如果存在贯穿路径，那么至少存在长度为0的路径
    if (information.exists_escape_transition) {
        length_array.push_back(0);
    }

    // 如果起始节点列表或终止节点列表为空，则没有路径，返回空数组
    if (information.index_of_heads.empty() || information.index_of_tails.empty()) {
        return length_array;
    }
    
    // 辅助函数：检查节点是否为阻塞节点
    auto is_dead_end = [](const state_transition& node) -> bool {
        return !node.is_transfer_transition() && node.type == state_transition_type::DEAD_END;
    };
    
    // 辅助函数：计算从指定索引开始的节点组的长度贡献
    // 注意：连续的 NEGATION_INTERSECTION 节点 + NEGATION 节点序列整体只贡献1个长度
    auto get_length_contribution_and_skip_group = [&information, &index_of_exception_pool](sizevalue node_index, sizevalue& next_index_to_check) -> sizevalue {
        const state_transition& node = information.content[node_index];
        
        // 如果是转移节点，不贡献长度
        if (node.is_transfer_transition()) {
            next_index_to_check = node_index + 1;
            return 0;
        }
        
        // 如果是阻塞节点，不贡献长度（该分支将被删除）
        if (node.type == state_transition_type::DEAD_END) {
            next_index_to_check = node_index + 1;
            return 0;
        }
        
        // 处理 NEGATION_INTERSECTION 节点组的情况
        if (node.type == state_transition_type::NEGATION_INTERSECTION) {
            // 检查是否是NEGATION_INTERSECTION节点组的开始
            sizevalue current_index = node_index;
            
            // 跳过所有连续的NEGATION_INTERSECTION节点
            while (current_index < information.content.size() && !information.content[current_index].is_transfer_transition() && information.content[current_index].type == state_transition_type::NEGATION_INTERSECTION) {
                current_index++;
            }
            
            // 检查下一个节点是否为NEGATION节点（根据文档，序列以NEGATION节点结尾）
            if (current_index < information.content.size() && !information.content[current_index].is_transfer_transition() && information.content[current_index].type == state_transition_type::NEGATION) {
                // 整个节点组（多个NEGATION_INTERSECTION + 一个NEGATION）只贡献1个长度
                next_index_to_check = current_index + 1; // 跳过NEGATION节点
                return 1;
            } else {
                // 如果没有找到结尾的NEGATION节点，这不是一个完整的节点组，是一个错误状态，进行报错
                runtime_assert(false, "检测到错误的NEGATION_INTERSECTION节点组：不以NEGATION节点结尾", index_of_exception_pool);
                return 0;
            }
        }
        
        // 对于NEGATION节点，检查它是否属于前面的NEGATION_INTERSECTION节点组
        if (node.type == state_transition_type::NEGATION) {
            // 向前检查是否有NEGATION_INTERSECTION节点
            sizevalue prev_index = node_index - 1;
            bool found_intersection_group = false;
            
            if (prev_index != sizevalue_max) {
                const state_transition& prev_node = information.content[prev_index];
                // 如果遇到转移节点，继续向前
                if (!prev_node.is_transfer_transition() && prev_node.type == state_transition_type::NEGATION_INTERSECTION) {
                    found_intersection_group = true;
                }
            }
            
            if (found_intersection_group) {
                // 这个NEGATION节点已经在之前的NEGATION_INTERSECTION节点组中计算过了
                next_index_to_check = node_index + 1;
                return 0;
            } else {
                // 单独的NEGATION节点贡献1个长度
                next_index_to_check = node_index + 1;
                return 1;
            }
        }
        
        // 对于其他类型的实际匹配节点（DEFAULT, ANY），贡献1个长度
        next_index_to_check = node_index + 1;
        return 1;
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
    
    // 深度优先搜索（DFS）函数
    auto dfs_from_start = [&](sizevalue start_index, vector<sizevalue>& local_lengths) -> void {
        struct StackFrame {
            sizevalue node_index;
            sizevalue current_length;
            unordered_set<sizevalue> visited;
        };
        
        if (is_dead_end(information.content[start_index])) {
            return; // 主分支被阻塞，没有有效长度
        }
        stack<StackFrame> stack;
        
        // 计算起始节点的长度贡献
        sizevalue next_index;
        sizevalue start_length = get_length_contribution_and_skip_group(start_index, next_index);
        if (length_of_exception_pool(index_of_exception_pool) != 0) {
            return;
        }
        
        stack.push({ start_index, start_length, { start_index } });
        
        while (!stack.empty()) {
            StackFrame frame = std::move(stack.top());
            stack.pop();
            
            sizevalue current_node = frame.node_index;
            sizevalue current_len = frame.current_length;
            unordered_set<sizevalue> visited = std::move(frame.visited);
            
            // 检查当前节点是否是终止节点
            if (std::find(information.index_of_tails.begin(), information.index_of_tails.end(), current_node) != information.index_of_tails.end()) {
                local_lengths.push_back(current_len);
            }
            
            // 获取当前节点的所有后继
            vector<sizevalue> successors = get_successors(current_node);
            if (length_of_exception_pool(index_of_exception_pool) != 0) {
                return {};
            }
            
            for (sizevalue succ : successors) {
                // 检测环：如果后继节点已在当前路径的已访问集合中，则检测到环
                if (visited.find(succ) != visited.end()) {
                    runtime_assert(false, "检测到环：正则表中存在循环路径，无法计算有限长度", index_of_exception_pool);
                    return;
                }
                
                // 创建新的已访问集合
                unordered_set<sizevalue> new_visited = visited;
                new_visited.insert(succ);
                
                // 计算新节点的长度贡献，并处理可能的节点组
                sizevalue skip_to_index;
                sizevalue length_contribution = get_length_contribution_and_skip_group(succ, skip_to_index);
                if (length_of_exception_pool(index_of_exception_pool) != 0) {
                    return;
                }
                sizevalue new_length = current_len + length_contribution;
                
                stack.push({succ, new_length, std::move(new_visited)});
            }
        }
    };
    
    // 并行执行DFS搜索
    vector<vector<sizevalue>> per_start_results(information.index_of_heads.size());
    
    // 使用并行执行策略遍历所有起始节点
    std::for_each(std::execution::par,
                  per_start_results.begin(), per_start_results.end(),
                  [&](vector<sizevalue>& local_vec) {
                      sizevalue idx = &local_vec - &per_start_results[0];
                      dfs_from_start(information.index_of_heads[idx], local_vec);
                  });
    if (length_of_exception_pool(index_of_exception_pool) != 0) {
        return length_array;
    }
    
    // 合并所有线程收集的长度
    for (auto& vec : per_start_results) {
        length_array.insert(length_array.end(), vec.begin(), vec.end());
    }
    
    // 排序并去重
    std::sort(length_array.begin(), length_array.end());
    auto last = std::unique(length_array.begin(), length_array.end());
    length_array.erase(last, length_array.end());
    
    return std::move(length_array);
}