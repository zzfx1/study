#ifndef SIMPLEMPL_SATFASTCOLORING_H
#define SIMPLEMPL_SATFASTCOLORING_H

#include "Namespace.h"
#include "SATBilevelColoring.h"
#include "SATExactColoring.h"
#include <limbo/algorithms/coloring/Coloring.h>

#include <vector>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <iostream>
#include <cassert>
#include <queue>
#include <numeric>
#include <cmath>
#include <ctime>
#include <chrono>

SIMPLEMPL_BEGIN_NAMESPACE

template <typename GraphType>
class SATFastColoring
    : public limbo::algorithms::coloring::Coloring<GraphType>
{
public:
    typedef GraphType graph_type;
    typedef limbo::algorithms::coloring::Coloring<graph_type> base_type;
    typedef typename base_type::graph_vertex_type vertex_descriptor;
    typedef typename base_type::graph_edge_type edge_descriptor;
    typedef typename base_type::vertex_iterator_type vertex_iterator;
    typedef typename base_type::edge_iterator_type edge_iterator;
    typedef typename base_type::adjacency_iterator adjacency_iterator;
    typedef typename base_type::edge_weight_type edge_weight_type;

    SATFastColoring(graph_type const& g)
        : base_type(g), m_batch_size(300), m_parent_count(0), m_alpha(0.1) {}

    virtual ~SATFastColoring() {}
    void setBatchSize(uint32_t bs) { m_batch_size = bs; }
    void setAlpha(double a) { m_alpha = a; }

protected:
    uint32_t m_batch_size;
    uint32_t m_parent_count;
    double   m_alpha;

    // 论文第VI节, 图7: 统一框架的阈值
    static const uint32_t N1_THRESHOLD = 200;
    static const uint32_t N2_THRESHOLD = 2000;
    static const uint32_t MAX_SUBPROBLEM_EDGES = 10000;

    // 简化和边排序的辅助成员
    std::vector<uint32_t> m_simplified_verts;
    std::unordered_map<uint32_t, uint32_t> m_simplified_neighbor;
    std::unordered_set<uint32_t> m_simplified_set;
    std::vector<uint32_t> m_parent_node_ids;

    // 优化：使用预构建的邻接表代替反复查询boost图
    // m_adj_conflict[v] = 冲突邻居列表 (权重>=0)
    // m_adj_stitch[v]   = 缝合邻居列表 (权重<0)
    std::vector<std::vector<uint32_t>> m_adj_conflict;
    std::vector<std::vector<uint32_t>> m_adj_stitch;
    // m_full_adj[v] = {(邻居, 是否冲突)}
    std::vector<std::vector<std::pair<uint32_t, bool>>> m_full_adj_vec;

    static uint64_t edgeKey(uint32_t u, uint32_t v) {
        if (u > v) std::swap(u, v);
        return (static_cast<uint64_t>(u) << 32) | v;
    }

    BilevelEdge toBilevelEdge(uint32_t u, uint32_t v, bool is_conf, double w) const {
        BilevelEdge e;
        e.u_idx = u; e.v_idx = v;
        e.u_parent = m_parent_node_ids[u];
        e.v_parent = m_parent_node_ids[v];
        e.is_conflict = is_conf;
        e.weight = w;
        return e;
    }

    // ============================================================
    // 主着色入口 - 实现统一框架
    // 论文伪代码: Algorithm SAT-Fast
    // 输入: 冲突图G, 颜色数K
    // 输出: 着色方案
    // ============================================================
    virtual double coloring()
    {
        //auto t_start = std::chrono::high_resolution_clock::now();

        const uint32_t n = boost::num_vertices(this->m_graph);
        this->m_vColor.assign(n, -1);
        if (n == 0) return 0.0;

        // 步骤1: 图简化 - 移除度为0和度为1   顶点
        m_parent_count = 0;
        //simplify_graph();

        // 步骤2: 计算父节点ID（用于缝合边分组）
        compute_parent_node_ids();

        // 步骤3: 预构建邻接表（关键性能优化）
        build_adjacency_lists();

        // 步骤4: BFS排序所有边
        std::vector<BilevelEdge> all_edges;
        bfs_sort_edges(all_edges);
        uint32_t ec = static_cast<uint32_t>(all_edges.size());

        if (ec == 0) {
            for (uint32_t i = 0; i < n; i++)
                if (this->m_vColor[i] < 0) this->m_vColor[i] = 0;
            restore_simplified_vertices();
            return this->calc_cost(this->m_vColor);
        }

        // 步骤5: 根据边数选择算法（论文第VI节, 图7）
        if (ec <= N1_THRESHOLD) {
            //mplPrint(kINFO, "SAT-Framwork: Using SAT-EXACT (edges=%u <= %u)\n", ec, N1_THRESHOLD);
            solve_exact(all_edges);
        } else if (ec <= N2_THRESHOLD) {
            //mplPrint(kINFO, "SATSAT-Framwork: Using SAT-Bilevel (edges=%u <= %u)\n", ec, N2_THRESHOLD);
            solve_bilevel(all_edges);
        } else {
            //mplPrint(kINFO, "SATSAT-Framwork: Using SAT-Fast incremental (edges=%u > %u)\n", ec, N2_THRESHOLD);
            solve_fast_incremental(all_edges);
        }

        /*auto t_end = std::chrono::high_resolution_clock::now();
        double elapsed = std::chrono::duration<double>(t_end - t_start).count();
        if (elapsed <= 1)
            mplPrint(kINFO, "SAT-Framwork: Total time for subgraph: %.4fs\n", elapsed);
        else
            mplPrint(kINFO, "SAT-Framwork: Total time for subgraph: %.4fs !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n", elapsed);*/

        // 步骤6: 恢复简化的顶点
        //restore_simplified_vertices();

        // 步骤7: 为未着色顶点分配默认颜色
        /*for (uint32_t i = 0; i < n; i++)
            if (this->m_vColor[i] < 0) this->m_vColor[i] = 0;*/

        return this->calc_cost(this->m_vColor);
    }

    // ============================================================
    // 求解器封装
    // ============================================================

    void solve_exact(const std::vector<BilevelEdge>& edges) {
        std::unordered_set<uint32_t> vset;
        vset.reserve(edges.size() * 2);
        for (const auto& e : edges) { vset.insert(e.u_idx); vset.insert(e.v_idx); }
        std::vector<uint32_t> verts(vset.begin(), vset.end());
        std::sort(verts.begin(), verts.end());

        uint32_t m = static_cast<uint32_t>(verts.size());
        std::unordered_map<uint32_t, uint32_t> g2l;
        g2l.reserve(m);
        for (uint32_t i = 0; i < m; ++i) g2l[verts[i]] = i;

        std::vector<int8_t> fixed(m, -1);
        for (uint32_t i = 0; i < m; ++i)
            if (this->m_vColor[verts[i]] >= 0) fixed[i] = this->m_vColor[verts[i]];

        std::vector<int8_t> result(m, -1);
        ExactSATEngine::solve(verts, edges, g2l, fixed, result, this->m_color_num, m_alpha);

        for (uint32_t i = 0; i < m; ++i)
            if (result[i] >= 0) this->m_vColor[verts[i]] = result[i];
    }

    void solve_bilevel(const std::vector<BilevelEdge>& edges) {
        std::unordered_set<uint32_t> vset;
        vset.reserve(edges.size() * 2);
        for (const auto& e : edges) { vset.insert(e.u_idx); vset.insert(e.v_idx); }
        std::vector<uint32_t> verts(vset.begin(), vset.end());
        std::sort(verts.begin(), verts.end());

        uint32_t m = static_cast<uint32_t>(verts.size());
        std::unordered_map<uint32_t, uint32_t> g2l;
        g2l.reserve(m);
        for (uint32_t i = 0; i < m; ++i) g2l[verts[i]] = i;

        std::vector<int8_t> fixed(m, -1);
        std::vector<int8_t> result(m, -1);
        BilevelSATEngine::solve(verts, edges, g2l, fixed, result, this->m_color_num);

        for (uint32_t i = 0; i < m; ++i)
            if (result[i] >= 0) this->m_vColor[verts[i]] = result[i];
    }

    // ============================================================
    // SAT-Fast增量求解 - 论文核心算法
    //
    // 论文伪代码对应:
    //   1. 将边按BFS顺序排列
    //   2. 分批处理，每批N条边
    //   3. 每批中：
    //      a. 收集批次中的顶点
    //      b. 添加批次顶点之间的历史边（已处理过的边）
    //      c. 添加与已着色顶点的冻结约束
    //      d. 调用SAT求解器
    //      e. 更新着色结果
    //   4. 最后进行贪心缝合优化
    // ============================================================
    void solve_fast_incremental(const std::vector<BilevelEdge>& sorted_edges) {
        const uint32_t total = static_cast<uint32_t>(sorted_edges.size());
        if (total == 0) return;

        //auto t_inc_start = std::chrono::high_resolution_clock::now();

        // 优化：预构建 顶点->边索引 的映射，使用vector代替unordered_map
        const uint32_t n = boost::num_vertices(this->m_graph);
        std::vector<std::vector<uint32_t>> vert_edges(n);
        for (uint32_t i = 0; i < total; ++i) {
            vert_edges[sorted_edges[i].u_idx].push_back(i);
            vert_edges[sorted_edges[i].v_idx].push_back(i);
        }

        uint32_t N = m_batch_size;
        uint32_t x = 0;
        uint32_t batch_count = 0;

        while (x < total) {
            //auto t_batch_start = std::chrono::high_resolution_clock::now();
            
            uint32_t batch_end = std::min(x + N, total);

            // 步骤3a: 收集当前批次的顶点和边
            std::unordered_set<uint32_t> batch_verts;
            batch_verts.reserve((batch_end - x) * 2);
            std::vector<BilevelEdge> local_edges;
            local_edges.reserve(batch_end - x + 256);
            std::unordered_set<uint64_t> local_edge_set;
            local_edge_set.reserve((batch_end - x) * 2);

            for (uint32_t i = x; i < batch_end; ++i) {
                const auto& e = sorted_edges[i];
                uint64_t k = edgeKey(e.u_idx, e.v_idx);
                if (local_edge_set.insert(k).second) {
                    local_edges.push_back(e);
                }
                batch_verts.insert(e.u_idx);
                batch_verts.insert(e.v_idx);
            }
            //printf("%ld",local_edges.size());

            // free_set: 当前批次中需要着色的顶点
            std::unordered_set<uint32_t> free_set = batch_verts;

            // 步骤3b: 添加批次顶点之间的历史约束边
            // 论文要求：对于批次中的每对顶点，如果它们之间
            // 存在已经在之前批次中处理过的边，也需要加入约束
            for (uint32_t v : batch_verts) {
                if (local_edges.size() >= MAX_SUBPROBLEM_EDGES) break;
                const auto& ve = vert_edges[v];
                for (uint32_t ei : ve) {
                    if (ei >= x) continue;  // 只看之前批次的边
                    const auto& e = sorted_edges[ei];
                    uint32_t other = (e.u_idx == v) ? e.v_idx : e.u_idx;
                    if (!batch_verts.count(other)) continue;
                    uint64_t k = edgeKey(e.u_idx, e.v_idx);
                    if (local_edge_set.insert(k).second) {
                        local_edges.push_back(e);
                    }
                }
            }

            // 步骤3c: 添加冻结约束 - 与已着色的外部顶点的边
            // 这些顶点的颜色被固定，作为约束传入求解器
            std::unordered_set<uint32_t> extra_verts;
            for (uint32_t v : batch_verts) {
                if (local_edges.size() >= MAX_SUBPROBLEM_EDGES) break;
                if (v >= m_full_adj_vec.size()) continue;
                for (const auto& nb_pair : m_full_adj_vec[v]) {
                    uint32_t u = nb_pair.first;
                    // 只添加已着色且不在当前批次中的邻居
                    if (batch_verts.count(u) || this->m_vColor[u] < 0) continue;
                    uint64_t k = edgeKey(v, u);
                    if (local_edge_set.insert(k).second) {
                        local_edges.push_back(toBilevelEdge(v, u, nb_pair.second, 1.0));
                        extra_verts.insert(u);
                    }
                }
            }

            // 合并所有涉及的顶点
            std::unordered_set<uint32_t> all_verts = batch_verts;
            all_verts.insert(extra_verts.begin(), extra_verts.end());

            if (local_edges.empty()) {
                for (uint32_t v : free_set)
                    if (this->m_vColor[v] < 0) this->m_vColor[v] = 0;
                x = batch_end;
                continue;
            }

            // 构建局部到全局的映射
            std::vector<uint32_t> verts(all_verts.begin(), all_verts.end());
            std::sort(verts.begin(), verts.end());

            uint32_t m = static_cast<uint32_t>(verts.size());
            std::unordered_map<uint32_t, uint32_t> g2l;
            g2l.reserve(m);
            for (uint32_t i = 0; i < m; ++i) g2l[verts[i]] = i;

            // 设置固定颜色约束：
            // - 外部已着色顶点（extra_verts）的颜色被冻结
            // - 批次内已在之前批次中着色的顶点也被冻结
            std::vector<int8_t> fixed(m, -1);
            for (uint32_t i = 0; i < m; ++i) {
                uint32_t gv = verts[i];
                if (!free_set.count(gv) && this->m_vColor[gv] >= 0)
                    fixed[i] = this->m_vColor[gv];
            }

            // 步骤3d: 调用SAT求解器
            std::vector<int8_t> result(m, -1);

            uint32_t local_ec = static_cast<uint32_t>(local_edges.size());
   
            //mplPrint(kINFO, "SAT-Fast(%u): Select SAT-Bilevel !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n",local_ec);
            BilevelSATEngine::solve(verts, local_edges, g2l, fixed, result, this->m_color_num);

            // 步骤3e: 更新着色结果（只更新自由顶点）
            for (uint32_t i = 0; i < m; ++i) {
                uint32_t gv = verts[i];
                if (free_set.count(gv) && result[i] >= 0)
                    this->m_vColor[gv] = result[i];
            }

            /*auto t_batch_end = std::chrono::high_resolution_clock::now();
            double batch_time = std::chrono::duration<double>(t_batch_end - t_batch_start).count();*/
            
            batch_count++;

            /*if (batch_time > 1) {
                mplPrint(kINFO, "SAT-Fast: %u batches takes %.4f s (%u edges, %u vertices, x=%u/%u)\n",
                         batch_count, batch_time,
                         static_cast<uint32_t>(local_edges.size()),
                         m, x, total);
            }*/

            x = batch_end;
        }

        /*auto t_inc_end = std::chrono::high_resolution_clock::now();
        double inc_time = std::chrono::duration<double>(t_inc_end - t_inc_start).count();
        mplPrint(kINFO, "SAT-Fast: Incremental solving has done, total batches %u, takes %.4fs\n", batch_count, inc_time);*/

        // 步骤4: 贪心缝合优化
        /*auto t_stitch_start = std::chrono::high_resolution_clock::now();
        greedy_stitch_refinement(3);
        auto t_stitch_end = std::chrono::high_resolution_clock::now();
        double stitch_time = std::chrono::duration<double>(t_stitch_end - t_stitch_start).count();
        mplPrint(kINFO, "SAT-Fast: Stitch refinement takes %.4fs\n", stitch_time);*/
    }

    // ============================================================
    // 辅助函数
    // ============================================================

    // 预构建邻接表 - 关键性能优化
    // 避免在greedy_stitch_refinement和can_recolor中
    // 反复通过boost接口查询图结构
    void build_adjacency_lists() {
        const uint32_t n = boost::num_vertices(this->m_graph);
        m_adj_conflict.assign(n, std::vector<uint32_t>());
        m_adj_stitch.assign(n, std::vector<uint32_t>());
        m_full_adj_vec.assign(n, std::vector<std::pair<uint32_t, bool>>());

        edge_iterator ei, ei_end;
        for (boost::tie(ei, ei_end) = boost::edges(this->m_graph); ei != ei_end; ++ei) {
            vertex_descriptor s = boost::source(*ei, this->m_graph);
            vertex_descriptor t = boost::target(*ei, this->m_graph);
            if (s == t) continue;
            uint32_t si = boost::get(boost::vertex_index, this->m_graph, s);
            uint32_t ti = boost::get(boost::vertex_index, this->m_graph, t);
            if (m_simplified_set.count(si) || m_simplified_set.count(ti)) continue;
            edge_weight_type w = boost::get(boost::edge_weight, this->m_graph, *ei);
            bool is_conflict = (w >= 0);

            m_full_adj_vec[si].push_back({ti, is_conflict});
            m_full_adj_vec[ti].push_back({si, is_conflict});

            if (is_conflict) {
                m_adj_conflict[si].push_back(ti);
                m_adj_conflict[ti].push_back(si);
            } else {
                m_adj_stitch[si].push_back(ti);
                m_adj_stitch[ti].push_back(si);
            }
        }
    }

    // BFS排序边 - 论文要求的空间局部性排序
    void bfs_sort_edges(std::vector<BilevelEdge>& sorted) {
        const uint32_t n = boost::num_vertices(this->m_graph);
        std::vector<bool> visited(n, false);
        sorted.clear();

        // 预计算每个非简化顶点的度
        std::vector<std::pair<int, uint32_t>> degree_vertex;
        degree_vertex.reserve(n);
        vertex_iterator vi, vi_end;
        for (boost::tie(vi, vi_end) = boost::vertices(this->m_graph); vi != vi_end; ++vi) {
            uint32_t idx = boost::get(boost::vertex_index, this->m_graph, *vi);
            if (m_simplified_set.count(idx)) continue;
            int d = static_cast<int>(boost::degree(*vi, this->m_graph));
            if (d > 0) degree_vertex.push_back({-d, idx}); // 负数用于降序排序
        }
        std::sort(degree_vertex.begin(), degree_vertex.end());

        // 使用预排序的顶点列表避免反复扫描
        std::set<uint64_t> edge_visited;

        for (const auto& dv : degree_vertex) {
            uint32_t v0_idx = dv.second;
            if (visited[v0_idx]) continue;

            vertex_descriptor v0 = boost::vertex(v0_idx, this->m_graph);
            visited[v0_idx] = true;

            std::queue<vertex_descriptor> Q;
            Q.push(v0);

            while (!Q.empty()) {
                vertex_descriptor v = Q.front(); Q.pop();
                uint32_t v_idx = boost::get(boost::vertex_index, this->m_graph, v);

                adjacency_iterator ai, ai_end;
                for (boost::tie(ai, ai_end) = boost::adjacent_vertices(v, this->m_graph); ai != ai_end; ++ai) {
                    uint32_t u_idx = boost::get(boost::vertex_index, this->m_graph, *ai);
                    if (m_simplified_set.count(u_idx)) continue;

                    uint64_t ek = edgeKey(v_idx, u_idx);
                    if (edge_visited.count(ek)) continue;
                    edge_visited.insert(ek);

                    auto ep = boost::edge(v, *ai, this->m_graph);
                    if (!ep.second) continue;
                    double w = boost::get(boost::edge_weight, this->m_graph, ep.first);
                    sorted.push_back(toBilevelEdge(v_idx, u_idx, w >= 0, std::abs(w)));

                    if (!visited[u_idx]) {
                        visited[u_idx] = true;
                        Q.push(*ai);
                    }
                }
            }
        }
    }
        /*void density_aware_bfs_sort_edges(std::vector<BilevelEdge>& sorted) {
        const uint32_t n = boost::num_vertices(this->m_graph);
        std::vector<bool> visited(n, false);
        sorted.clear();

        std::vector<std::pair<double, uint32_t>> score_vertex;
        score_vertex.reserve(n);
        vertex_iterator vi, vi_end;
        for (boost::tie(vi, vi_end) = boost::vertices(this->m_graph); vi != vi_end; ++vi) {
            uint32_t idx = boost::get(boost::vertex_index, this->m_graph, *vi);
            if (m_simplified_set.count(idx)) continue;
            int d = static_cast<int>(boost::degree(*vi, this->m_graph));
            if (d <= 0) continue;

            double self_den = static_cast<double>(m_conflict_degree[idx]);
            double nb_avg = 0;
            int nb_cnt = 0;
            if (idx < m_adj_conflict.size()) {
                const std::vector<uint32_t>& conf_nbs = m_adj_conflict[idx];
                for (size_t j = 0; j < conf_nbs.size(); ++j) {
                    if (conf_nbs[j] < m_conflict_degree.size()) {
                        nb_avg += m_conflict_degree[conf_nbs[j]];
                        nb_cnt++;
                    }
                }
            }
            if (nb_cnt > 0) nb_avg /= nb_cnt;
            double score = 0.7 * self_den + 0.3 * nb_avg;
            score_vertex.push_back(std::make_pair(-score, idx));
        }
        std::sort(score_vertex.begin(), score_vertex.end());

        std::set<uint64_t> edge_visited;

        for (size_t si = 0; si < score_vertex.size(); ++si) {
            uint32_t v0_idx = score_vertex[si].second;
            if (visited[v0_idx]) continue;

            vertex_descriptor v0 = boost::vertex(v0_idx, this->m_graph);
            visited[v0_idx] = true;

            std::queue<vertex_descriptor> Q;
            Q.push(v0);

            while (!Q.empty()) {
                vertex_descriptor v = Q.front(); Q.pop();
                uint32_t v_idx = boost::get(boost::vertex_index, this->m_graph, v);

                adjacency_iterator ai, ai_end;
                for (boost::tie(ai, ai_end) = boost::adjacent_vertices(v, this->m_graph);
                     ai != ai_end; ++ai)
                {
                    uint32_t u_idx = boost::get(boost::vertex_index, this->m_graph, *ai);
                    if (m_simplified_set.count(u_idx)) continue;

                    uint64_t ek = edgeKey(v_idx, u_idx);
                    if (edge_visited.count(ek)) continue;
                    edge_visited.insert(ek);

                    std::pair<edge_descriptor, bool> ep = boost::edge(v, *ai, this->m_graph);
                    if (!ep.second) continue;
                    double w = boost::get(boost::edge_weight, this->m_graph, ep.first);
                    sorted.push_back(toBilevelEdge(v_idx, u_idx, w >= 0, std::abs(w)));

                    if (!visited[u_idx]) {
                        visited[u_idx] = true;
                        Q.push(*ai);
                    }
                }
            }
        }
    }*/

    // 计算父节点ID - 通过缝合边连接的顶点属于同一父节点
    void compute_parent_node_ids() {
        const uint32_t n = boost::num_vertices(this->m_graph);
        m_parent_node_ids.assign(n, static_cast<uint32_t>(-1));
        m_parent_count = 0;
        vertex_iterator vi, vi_end;
        for (boost::tie(vi, vi_end) = boost::vertices(this->m_graph); vi != vi_end; ++vi) {
            uint32_t idx = boost::get(boost::vertex_index, this->m_graph, *vi);
            if (m_parent_node_ids[idx] != static_cast<uint32_t>(-1)) continue;
            m_parent_node_ids[idx] = m_parent_count;

            // BFS遍历所有通过缝合边连接的顶点
            std::queue<vertex_descriptor> q;
            q.push(*vi);
            while (!q.empty()) {
                vertex_descriptor cur = q.front(); q.pop();
                adjacency_iterator ai, ai_end;
                for (boost::tie(ai, ai_end) = boost::adjacent_vertices(cur, this->m_graph); ai != ai_end; ++ai) {
                    auto ep = boost::edge(cur, *ai, this->m_graph);
                    if (!ep.second || boost::get(boost::edge_weight, this->m_graph, ep.first) >= 0) continue;
                    uint32_t ni = boost::get(boost::vertex_index, this->m_graph, *ai);
                    if (m_parent_node_ids[ni] == static_cast<uint32_t>(-1)) {
                        m_parent_node_ids[ni] = m_parent_count;
                        q.push(*ai);
                    }
                }
            }
            ++m_parent_count;
        }
    }

    // 图简化 - 迭代移除度0和度1的顶点
    void simplify_graph() {
        const uint32_t n = boost::num_vertices(this->m_graph);
        m_simplified_verts.clear();
        m_simplified_neighbor.clear();
        m_simplified_set.clear();

        // 优化：预计算每个顶点的有效度，避免每次迭代重新扫描
        std::vector<int> effective_degree(n, 0);
        std::vector<bool> removed(n, false);

        // 初始化有效度
        vertex_iterator vi, vi_end;
        for (boost::tie(vi, vi_end) = boost::vertices(this->m_graph); vi != vi_end; ++vi) {
            uint32_t idx = boost::get(boost::vertex_index, this->m_graph, *vi);
            adjacency_iterator ai, ai_end;
            int deg = 0;
            for (boost::tie(ai, ai_end) = boost::adjacent_vertices(*vi, this->m_graph); ai != ai_end; ++ai) {
                uint32_t ni = boost::get(boost::vertex_index, this->m_graph, *ai);
                if (ni != idx) deg++;
            }
            effective_degree[idx] = deg;
        }

        // 使用队列驱动的简化，避免反复全图扫描
        std::queue<uint32_t> work_queue;
        for (uint32_t i = 0; i < n; ++i) {
            if (effective_degree[i] <= 1) work_queue.push(i);
        }

        while (!work_queue.empty()) {
            uint32_t idx = work_queue.front();
            work_queue.pop();

            if (removed[idx]) continue;

            // 重新计算当前有效度（可能因邻居被移除而变化）
            vertex_descriptor v = boost::vertex(idx, this->m_graph);
            int deg = 0;
            uint32_t last_neighbor = idx;
            adjacency_iterator ai, ai_end;
            for (boost::tie(ai, ai_end) = boost::adjacent_vertices(v, this->m_graph); ai != ai_end; ++ai) {
                uint32_t ni = boost::get(boost::vertex_index, this->m_graph, *ai);
                if (!removed[ni] && ni != idx) {
                    deg++;
                    last_neighbor = ni;
                }
            }

            if (deg == 0) {
                this->m_vColor[idx] = 0;
                removed[idx] = true;
                m_simplified_verts.push_back(idx);
                m_simplified_set.insert(idx);

                // 通知邻居度数可能变化
                for (boost::tie(ai, ai_end) = boost::adjacent_vertices(v, this->m_graph); ai != ai_end; ++ai) {
                    uint32_t ni = boost::get(boost::vertex_index, this->m_graph, *ai);
                    if (!removed[ni]) work_queue.push(ni);
                }
            } else if (deg == 1) {
                removed[idx] = true;
                m_simplified_neighbor[idx] = last_neighbor;
                m_simplified_verts.push_back(idx);
                m_simplified_set.insert(idx);

                // 通知邻居度数可能变化
                for (boost::tie(ai, ai_end) = boost::adjacent_vertices(v, this->m_graph); ai != ai_end; ++ai) {
                    uint32_t ni = boost::get(boost::vertex_index, this->m_graph, *ai);
                    if (!removed[ni]) work_queue.push(ni);
                }
            }
        }

        mplPrint(kINFO, "图简化: 移除了 %lu 个顶点 (总共 %u 个)\n",
                 m_simplified_verts.size(), n);
    }

    // 恢复简化的顶点 - 逆序处理
    void restore_simplified_vertices() {
        const uint32_t K = this->m_color_num;
        for (int i = static_cast<int>(m_simplified_verts.size()) - 1; i >= 0; i--) {
            uint32_t v = m_simplified_verts[i];
            if (this->m_vColor[v] >= 0) continue;

            auto it = m_simplified_neighbor.find(v);
            if (it == m_simplified_neighbor.end()) {
                this->m_vColor[v] = 0;
                continue;
            }

            uint32_t nb = it->second;
            int8_t nbc = this->m_vColor[nb];

            auto ep = boost::edge(boost::vertex(v, this->m_graph),
                                  boost::vertex(nb, this->m_graph), this->m_graph);
            if (ep.second) {
                if (boost::get(boost::edge_weight, this->m_graph, ep.first) >= 0) {
                    // 冲突边：选择不同颜色
                    for (int8_t c = 0; c < static_cast<int8_t>(K); c++)
                        if (c != nbc) { this->m_vColor[v] = c; break; }
                } else {
                    // 缝合边：选择相同颜色
                    this->m_vColor[v] = (nbc >= 0) ? nbc : 0;
                }
            } else {
                this->m_vColor[v] = 0;
            }
        }
    }

    // 贪心缝合优化 - 减少缝合代价
    void greedy_stitch_refinement(int rounds) {
        const uint32_t K = this->m_color_num;
        const uint32_t n = boost::num_vertices(this->m_graph);

        for (int r = 0; r < rounds; ++r) {
            bool imp = false;

            // 阶段1: 父节点内多数投票统一
            std::unordered_map<uint32_t, std::vector<uint32_t>> pm;
            for (uint32_t v = 0; v < n; ++v) {
                if (!m_simplified_set.count(v) && this->m_vColor[v] >= 0)
                    pm[m_parent_node_ids[v]].push_back(v);
            }

            for (auto& pair : pm) {
                if (pair.second.size() <= 1) continue;
                std::vector<int> cnt(K, 0);
                for (uint32_t v : pair.second)
                    if (this->m_vColor[v] >= 0 && this->m_vColor[v] < static_cast<int8_t>(K))
                        cnt[this->m_vColor[v]]++;
                int8_t maj = static_cast<int8_t>(
                    std::distance(cnt.begin(), std::max_element(cnt.begin(), cnt.end())));
                for (uint32_t v : pair.second)
                    if (this->m_vColor[v] != maj && can_recolor_fast(v, maj)) {
                        this->m_vColor[v] = maj;
                        imp = true;
                    }
            }

            // 阶段2: 逐顶点缝合代价最小化
            for (uint32_t v = 0; v < n; ++v) {
                if (m_simplified_set.count(v) || this->m_vColor[v] < 0) continue;
                int8_t cur = this->m_vColor[v];
                int cs = count_active_stitches_fast(v);
                if (cs == 0) continue;

                int8_t best = cur;
                int bs = cs;
                for (int8_t c = 0; c < static_cast<int8_t>(K); ++c) {
                    if (c == cur || !can_recolor_fast(v, c)) continue;
                    this->m_vColor[v] = c;
                    int ns = count_active_stitches_fast(v);
                    this->m_vColor[v] = cur;
                    if (ns < bs) { bs = ns; best = c; }
                }
                if (best != cur) { this->m_vColor[v] = best; imp = true; }
            }

            if (!imp) break;
        }
    }

    // 使用预构建邻接表的快速重着色检查
    bool can_recolor_fast(uint32_t v, int8_t c) const {
        if (v >= m_adj_conflict.size()) return true;
        for (uint32_t u : m_adj_conflict[v]) {
            if (this->m_vColor[u] == c) return false;
        }
        return true;
    }

    // 使用预构建邻接表的快速缝合计数
    int count_active_stitches_fast(uint32_t v) const {
        if (v >= m_adj_stitch.size()) return 0;
        int cnt = 0;
        for (uint32_t u : m_adj_stitch[v]) {
            if (this->m_vColor[v] != this->m_vColor[u]) cnt++;
        }
        return cnt;
    }

    // 保留原始版本作为后备（使用boost接口）
    bool can_recolor(uint32_t v, int8_t c) const {
        adjacency_iterator ai, ai_end;
        for (boost::tie(ai, ai_end) = boost::adjacent_vertices(
                 boost::vertex(v, this->m_graph), this->m_graph); ai != ai_end; ++ai) {
            auto ep = boost::edge(boost::vertex(v, this->m_graph), *ai, this->m_graph);
            if (ep.second &&
                boost::get(boost::edge_weight, this->m_graph, ep.first) >= 0 &&
                this->m_vColor[boost::get(boost::vertex_index, this->m_graph, *ai)] == c)
                return false;
        }
        return true;
    }

    int count_active_stitches(uint32_t v) const {
        int cnt = 0;
        adjacency_iterator ai, ai_end;
        for (boost::tie(ai, ai_end) = boost::adjacent_vertices(
                 boost::vertex(v, this->m_graph), this->m_graph); ai != ai_end; ++ai) {
            auto ep = boost::edge(boost::vertex(v, this->m_graph), *ai, this->m_graph);
            if (ep.second &&
                boost::get(boost::edge_weight, this->m_graph, ep.first) < 0 &&
                this->m_vColor[v] != this->m_vColor[boost::get(boost::vertex_index, this->m_graph, *ai)])
                cnt++;
        }
        return cnt;
    }

    virtual std::string algorithm_name() const { return "SAT_FAST"; }
};

SIMPLEMPL_END_NAMESPACE

#endif
