#ifndef SIMPLEMPL_DPSATCOLORING_H
#define SIMPLEMPL_DPSATCOLORING_H

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
class DPSATColoring
    : public limbo::algorithms::coloring::Coloring<GraphType>
{
public:
    typedef GraphType                                          graph_type;
    typedef limbo::algorithms::coloring::Coloring<graph_type>  base_type;
    typedef typename base_type::graph_vertex_type               vertex_descriptor;
    typedef typename base_type::graph_edge_type                 edge_descriptor;
    typedef typename base_type::vertex_iterator_type            vertex_iterator;
    typedef typename base_type::edge_iterator_type              edge_iterator;
    typedef typename base_type::adjacency_iterator              adjacency_iterator;
    typedef typename base_type::edge_weight_type                edge_weight_type;

    DPSATColoring(graph_type const& g)
        : base_type(g), m_batch_size(80), m_parent_count(0), m_alpha(0.1) {}

    virtual ~DPSATColoring() {}
    void setBatchSize(uint32_t bs) { m_batch_size = bs; }
    void setAlpha(double a) { m_alpha = a; }

protected:
    uint32_t m_batch_size;
    uint32_t m_parent_count;
    double   m_alpha;

    // 阈值常量
    static const uint32_t N1_THRESHOLD = 200;
    static const uint32_t N2_THRESHOLD = 2000;
    static const uint32_t MAX_SUBPROBLEM_EDGES = 2000;
    static const uint32_t MAX_ANCHOR_COUNT = 0;         
    static const uint32_t B_min = 80;    // 最高密度时的最小分块80
    static const uint32_t B_max = 120;   // 最低密度时的最大分块120
    static const uint32_t E_min = 0;    // 最高密度时的最小分块80
    static const uint32_t E_max = 300;   // 最低密度时的最大分块120

    // 简化辅助
    std::vector<uint32_t>                          m_simplified_verts;
    std::unordered_map<uint32_t, uint32_t>         m_simplified_neighbor;
    std::unordered_set<uint32_t>                   m_simplified_set;
    std::vector<uint32_t>                          m_parent_node_ids;

    // 预构建邻接表
    std::vector<std::vector<uint32_t>>                        m_adj_conflict;
    std::vector<std::vector<uint32_t>>                        m_adj_stitch;
    std::vector<std::vector<std::pair<uint32_t, bool>>>       m_full_adj_vec;

    // 密度信息
    std::vector<uint32_t>  m_conflict_degree;
    double                 m_density_mean;
    double                 m_density_sigma;
    double                 m_high_density_thr;

    // ============================================================
    // 工具函数
    // ============================================================
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
    // 主着色入口
    //
    // 整体流程:
    //   1. 图简化（移除度0/度1顶点）
    //   2. 计算父节点ID、构建邻接表、计算密度统计
    //   3. 密度感知BFS排序所有边
    //   4. 根据边数选择算法:
    //      - 小规模(<=200): SAT-EXACT
    //      - 中规模(<=2000): SAT-Bilevel
    //      - 大规模(>2000): DP-SAT（锚点+分块）
    //   5. 恢复简化顶点
    // ============================================================
    virtual double coloring()
    {
        std::chrono::high_resolution_clock::time_point t_start =
            std::chrono::high_resolution_clock::now();

        const uint32_t n = boost::num_vertices(this->m_graph);
        this->m_vColor.assign(n, -1);
        if (n == 0) return 0.0;

        // 步骤1: 图简化
        m_parent_count = 0;

        // 步骤2: 预处理
        compute_parent_node_ids();
        build_adjacency_lists();
        compute_density_statistics();

        // 步骤3: 密度感知BFS排序
        std::vector<BilevelEdge> all_edges;
        //bfs_sort_edges(all_edges);
        density_aware_bfs_sort_edges(all_edges);
        uint32_t ec = static_cast<uint32_t>(all_edges.size());


        // 步骤4: 根据边数选择算法
        if (ec <= N1_THRESHOLD) {
            solve_exact(all_edges);
        } else if (ec <= N2_THRESHOLD) {
            solve_bilevel(all_edges);
        } else {
            //compute_density_statistics();
            solve_dpsat(all_edges);
        }

        // 步骤5: 恢复和收尾

        for (uint32_t i = 0; i < n; i++)
            if (this->m_vColor[i] < 0) this->m_vColor[i] = 0;

        return this->calc_cost(this->m_vColor);
    }

    // ============================================================
    // 求解器封装
    // ============================================================
    void solve_exact(const std::vector<BilevelEdge>& edges) {
        std::unordered_set<uint32_t> vset;
        vset.reserve(edges.size() * 2);
        for (size_t i = 0; i < edges.size(); ++i) {
            vset.insert(edges[i].u_idx);
            vset.insert(edges[i].v_idx);
        }
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
        for (size_t i = 0; i < edges.size(); ++i) {
            vset.insert(edges[i].u_idx);
            vset.insert(edges[i].v_idx);
        }
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
        BilevelSATEngine::solve(verts, edges, g2l, fixed, result, this->m_color_num);
        for (uint32_t i = 0; i < m; ++i)
            if (result[i] >= 0) this->m_vColor[verts[i]] = result[i];
    }

    // ============================================================
    // DP-SAT 核心算法
    //
    // 流程:
    //   阶段1: 选择锚点（高密度+分散的关键顶点）
    //   阶段2: 锚点子图统一着色（SAT-Bilevel）
    //   阶段3: 以锚点为中心BFS分块，各分块独立着色（SAT-Bilevel）
    //   阶段4: 处理遗漏的未着色顶点
    //   阶段5: 贪心缝合优化
    // ============================================================
    void solve_dpsat(const std::vector<BilevelEdge>& sorted_edges) {
        const uint32_t total = static_cast<uint32_t>(sorted_edges.size());
        if (total == 0) return;

        const uint32_t n = boost::num_vertices(this->m_graph);

        // ============================================================
        // 阶段1: 选择锚点
        // ============================================================

        std::vector<uint32_t> anchor_vertices;
        select_anchor_vertices(anchor_vertices);

        // ============================================================
        // 阶段2: 锚点子图统一着色
        // ============================================================

        if (!anchor_vertices.empty()) {
            solve_anchor_subgraph(anchor_vertices, sorted_edges);
        }

        // ============================================================
        // 阶段3: 以锚点为中心分块，各分块独立着色
        // ============================================================
        solve_blocks_around_anchors(sorted_edges);

        // ============================================================
        // 阶段5: 贪心缝合优化
        // ============================================================
        greedy_stitch_refinement(3);

    }

    // ============================================================
    // 阶段1: 选择锚点
    //
    // 策略:
    //   - 按冲突度降序排列所有活跃顶点
    //   - 只选密度 > 高密度阈值的顶点
    //   - 锚点之间至少间隔2跳（保证分散性）
    //   - 数量上限 MAX_ANCHOR_COUNT
    // ============================================================
    void select_anchor_vertices(std::vector<uint32_t>& anchors) {
        const uint32_t n = boost::num_vertices(this->m_graph);
        anchors.clear();

        // 收集活跃顶点，按冲突度降序
        std::vector<std::pair<uint32_t, uint32_t>> candidates;
        for (uint32_t v = 0; v < n; ++v) {
            //if (m_simplified_set.count(v)) continue;
            if (v < m_conflict_degree.size() && m_conflict_degree[v] > 0) {
                candidates.push_back(std::make_pair(m_conflict_degree[v], v));
            }
        }
        std::sort(candidates.begin(), candidates.end(),
                  [](const std::pair<uint32_t, uint32_t>& a,
                     const std::pair<uint32_t, uint32_t>& b) {
                      return a.first > b.first;
                  });

        if (candidates.empty()) return;

        // 选择锚点（分散性约束）
        std::vector<bool> too_close(n, false);

        for (size_t i = 0; i < candidates.size() && anchors.size() < MAX_ANCHOR_COUNT; ++i) {
            uint32_t v = candidates[i].second;
            uint32_t deg = candidates[i].first;

            if (deg <= static_cast<uint32_t>(m_high_density_thr)) break;
            if (too_close[v]) continue;

            anchors.push_back(v);

            if (v < m_adj_conflict.size()) {
                const std::vector<uint32_t>& nb1 = m_adj_conflict[v];
                for (size_t j = 0; j < nb1.size(); ++j) {
                    too_close[nb1[j]] = true;
                    if (nb1[j] < m_adj_conflict.size()) {
                        const std::vector<uint32_t>& nb2 = m_adj_conflict[nb1[j]];
                        for (size_t k = 0; k < nb2.size(); ++k) {
                            too_close[nb2[k]] = true;
                        }
                    }
                }
            }
        }
    }

        // ============================================================
    // 计算分块大小
    //
    // 公式: BlockSize = B_max - (B_max - B_min) × clamp((d - μ) / (3σ), 0, 1)
    //
    // 其中:
    //   d     = 种子顶点的冲突度
    //   μ     = 全局平均冲突度
    //   σ     = 全局冲突度标准差
    //   B_max = 分块顶点数上限（低密度时）
    //   B_min = 分块顶点数下限（高密度时）
    //
    // 效果:
    //   d ≤ μ        → BlockSize = B_max (150)
    //   d = μ + 3σ   → BlockSize = B_min (40)
    //   d 在两者之间  → 线性插值
    // ============================================================
    uint32_t compute_block_size(uint32_t seed_degree) const {

        if (m_density_sigma < 1e-6) {
            // 标准差为0，所有顶点密度相同，用默认值
            return (B_max + B_min) / 2;
        }

        // 计算归一化密度: (d - μ) / (3σ)，截断到 [0, 1]
        double normalized = (static_cast<double>(seed_degree) - m_density_mean) 
                            / (3.0 * m_density_sigma);
        if (normalized < 0.0) normalized = 0.0;
        if (normalized > 1.0) normalized = 1.0;

        // 线性插值: 密度越高 → 分块越小
        uint32_t block_size = static_cast<uint32_t>(
            B_max - (B_max - B_min) * normalized
        );

        return block_size;
    }
    
    uint32_t compute_block_edge_size(uint32_t seed_degree) const {

        if (m_density_sigma < 1e-6) {
            // 标准差为0，所有顶点密度相同，用默认值
            return (E_max + E_min) / 2;
        }

        // 计算归一化密度: (d - μ) / (3σ)，截断到 [0, 1]
        double normalized = (static_cast<double>(seed_degree) - m_density_mean) 
                            / (6.0 * m_density_sigma);
        if (normalized < 0.0) normalized = 0.0;
        if (normalized > 1.0) normalized = 1.0;

        // 线性插值: 密度越高 → 分块越小
        uint32_t block_edge_size = static_cast<uint32_t>(
            E_max - (E_max - E_min) * normalized
        );

        return block_edge_size;
    }

    // ============================================================
    // 阶段2: 锚点子图统一着色
    //
    // 收集:
    //   - 锚点之间的边
    //   - 锚点与其直接邻居之间的边（邻居作为辅助约束）
    // 全部使用 SAT-Bilevel 着色
    // 只保留锚点的着色结果
    // ============================================================
    void solve_anchor_subgraph(const std::vector<uint32_t>& anchors,
                               const std::vector<BilevelEdge>& all_edges)
    {
        if (anchors.empty()) return;

        std::unordered_set<uint32_t> anchor_set(anchors.begin(), anchors.end());

        // 收集锚点之间的边
        std::vector<BilevelEdge> anchor_edges;
        std::unordered_set<uint64_t> edge_set;

        // 收集锚点与直接邻居之间的边（辅助约束，控制总规模）
        std::unordered_set<uint32_t> aux_verts;
        for (size_t i = 0; i < anchors.size(); ++i) {
            uint32_t v = anchors[i];
            if (v >= m_full_adj_vec.size()) continue;
            const std::vector<std::pair<uint32_t, bool>>& neighbors = m_full_adj_vec[v];
            for (size_t j = 0; j < neighbors.size(); ++j) {
                uint32_t u = neighbors[j].first;
                if (anchor_set.count(u)) continue;       // 已经在锚点集合中
                if (anchor_edges.size() >= N2_THRESHOLD) break; // 控制规模上限
                uint64_t k = edgeKey(v, u);
                if (edge_set.insert(k).second) {
                    anchor_edges.push_back(
                        toBilevelEdge(v, u, neighbors[j].second, 1.0));
                    aux_verts.insert(u);
                }
            }
            if (anchor_edges.size() >= N2_THRESHOLD) break;
        }

        if (anchor_edges.empty()) {
            // 锚点之间没有边，给默认颜色
            for (size_t i = 0; i < anchors.size(); ++i) {
                if (this->m_vColor[anchors[i]] < 0)
                    this->m_vColor[anchors[i]] = 0;
            }
            return;
        }

        // 构建顶点集合
        std::unordered_set<uint32_t> all_verts_set(anchors.begin(), anchors.end());
        all_verts_set.insert(aux_verts.begin(), aux_verts.end());

        std::vector<uint32_t> verts(all_verts_set.begin(), all_verts_set.end());
        std::sort(verts.begin(), verts.end());
        uint32_t m = static_cast<uint32_t>(verts.size());

        std::unordered_map<uint32_t, uint32_t> g2l;
        g2l.reserve(m);
        for (uint32_t i = 0; i < m; ++i) g2l[verts[i]] = i;

        // 辅助顶点如果已有颜色则固定
        std::vector<int8_t> fixed(m, -1);

        uint32_t aec = static_cast<uint32_t>(anchor_edges.size());

        // 统一使用 Bilevel 着色
        std::vector<int8_t> result(m, -1);
        BilevelSATEngine::solve(verts, anchor_edges, g2l, fixed, result, this->m_color_num);

        // 只保留锚点的着色结果（辅助顶点的结果丢弃）
        for (uint32_t i = 0; i < m; ++i) {
            uint32_t gv = verts[i];
            if (anchor_set.count(gv) && result[i] >= 0) {
                this->m_vColor[gv] = result[i];
            }
        }
    }

    // ============================================================
    // 阶段3: 以锚点为中心分块，各分块独立着色
    //
    // 策略:
    //   - 按密度降序选择种子（未着色的高密度顶点优先）
    //   - 从种子BFS扩展，形成分块
    //   - 高密度种子 -> 小分块；低密度种子 -> 大分块
    //   - 每个分块收集内部边 + 已着色邻居的冻结约束
    //   - 使用 SAT-Bilevel 独立着色
    // ============================================================
    void solve_blocks_around_anchors(const std::vector<BilevelEdge>& all_edges) {
        const uint32_t n = boost::num_vertices(this->m_graph);

        // 构建 顶点->边索引 映射
        std::vector<std::vector<uint32_t>> vert_edges(n);
        for (uint32_t i = 0; i < all_edges.size(); ++i) {
            vert_edges[all_edges[i].u_idx].push_back(i);
            vert_edges[all_edges[i].v_idx].push_back(i);
        }

        // 标记已处理的顶点
        std::vector<bool> processed(n, false);

        // 按密度降序排列种子候选（未着色的活跃顶点）
        std::vector<std::pair<uint32_t, uint32_t>> seed_candidates;
        for (uint32_t v = 0; v < n; ++v) {
            if (processed[v]) continue;
            if (this->m_vColor[v] >= 0) {
                // 已着色（锚点），标记为已处理
                processed[v] = true;
                continue;
            }
            if (v < m_conflict_degree.size() && m_conflict_degree[v] > 0) {
                seed_candidates.push_back(std::make_pair(m_conflict_degree[v], v));
            }
        }
        std::sort(seed_candidates.begin(), seed_candidates.end(),
                  [](const std::pair<uint32_t, uint32_t>& a,
                     const std::pair<uint32_t, uint32_t>& b) {
                      return a.first > b.first;
                  });

        uint32_t block_count = 0;
        uint32_t total_block_verts = 0;

        for (size_t si = 0; si < seed_candidates.size(); ++si) {
            uint32_t seed = seed_candidates[si].second;
            if (processed[seed]) continue;
            
            
	    uint32_t max_block_verts = compute_block_size(m_conflict_degree[seed]);
	    
            // BFS扩展分块（只扩展未着色的顶点）
            std::vector<uint32_t> block_verts;
            std::queue<uint32_t> bfs_q;
            bfs_q.push(seed);
            processed[seed] = true;
            block_verts.push_back(seed);
            

            while (!bfs_q.empty() && block_verts.size() < max_block_verts) {
                uint32_t v = bfs_q.front(); bfs_q.pop();
                if (v >= m_full_adj_vec.size()) continue;
                const std::vector<std::pair<uint32_t, bool>>& neighbors = m_full_adj_vec[v];
                for (size_t j = 0; j < neighbors.size(); ++j) {
                    uint32_t u = neighbors[j].first;
                    if (!processed[u] && this->m_vColor[u] < 0 &&
                        block_verts.size() < max_block_verts)
                    {
                        processed[u] = true;
                        block_verts.push_back(u);
                        bfs_q.push(u);
                    }
                }
            }

            if (block_verts.empty()) continue;

            // 收集分块内部边
            std::unordered_set<uint32_t> block_set(block_verts.begin(), block_verts.end());
            std::vector<BilevelEdge> block_edges;
            std::unordered_set<uint64_t> block_edge_set;

            for (size_t vi = 0; vi < block_verts.size(); ++vi) {
                uint32_t v = block_verts[vi];
                const std::vector<uint32_t>& ve = vert_edges[v];
                for (size_t j = 0; j < ve.size(); ++j) {
                    const BilevelEdge& e = all_edges[ve[j]];
                    uint32_t other = (e.u_idx == v) ? e.v_idx : e.u_idx;
                    if (block_set.count(other)) {
                        uint64_t k = edgeKey(e.u_idx, e.v_idx);
                        if (block_edge_set.insert(k).second) {
                            block_edges.push_back(e);
                        }
                    }
                }
            }
            

            // 添加已着色邻居的冻结约束（锚点 + 之前分块着色的顶点）
            std::unordered_set<uint32_t> frozen_verts;
            for (size_t vi = 0; vi < block_verts.size(); ++vi) {
                uint32_t v = block_verts[vi];
                if (v >= m_full_adj_vec.size()) continue;
                if (block_edges.size() >= N2_THRESHOLD) break;
                const std::vector<std::pair<uint32_t, bool>>& neighbors = m_full_adj_vec[v];
                for (size_t j = 0; j < neighbors.size(); ++j) {
                    uint32_t u = neighbors[j].first;
                    bool is_conf = neighbors[j].second;
                    if (!block_set.count(u) && this->m_vColor[u] >= 0) {
                        uint64_t k = edgeKey(v, u);
                        if (block_edge_set.insert(k).second) {
                            block_edges.push_back(toBilevelEdge(v, u, is_conf, 1.0));
                            frozen_verts.insert(u);
                        }
                    }
                }
            }

            if (block_edges.empty()) {
                // 没有边，贪心着色
                for (size_t vi = 0; vi < block_verts.size(); ++vi) {
                    greedy_color_vertex(block_verts[vi]);
                }
                block_count++;
                total_block_verts += static_cast<uint32_t>(block_verts.size());
                continue;
            }

            // 构建映射
            std::unordered_set<uint32_t> all_block_verts(block_verts.begin(), block_verts.end());
            all_block_verts.insert(frozen_verts.begin(), frozen_verts.end());

            std::vector<uint32_t> verts_vec(all_block_verts.begin(), all_block_verts.end());
            std::sort(verts_vec.begin(), verts_vec.end());
            uint32_t m = static_cast<uint32_t>(verts_vec.size());

            std::unordered_map<uint32_t, uint32_t> g2l;
            g2l.reserve(m);
            for (uint32_t i = 0; i < m; ++i) g2l[verts_vec[i]] = i;

            // 冻结约束：已着色的非分块内顶点
            std::vector<int8_t> fixed(m, -1);
            for (uint32_t i = 0; i < m; ++i) {
                uint32_t gv = verts_vec[i];
                if (frozen_verts.count(gv) && this->m_vColor[gv] >= 0) {
                    fixed[i] = this->m_vColor[gv];
                }
            }

            // 使用 Exact,Bilevel 着色
            std::vector<int8_t> result(m, -1);
            
            if(block_edges.size() > 200) {
            	BilevelSATEngine::solve(verts_vec, block_edges, g2l, fixed, result, this->m_color_num);
            }
            else {     
            	ExactSATEngine::solve(verts_vec, block_edges, g2l, fixed, result, this->m_color_num, m_alpha);
	    }
            // 更新分块内顶点的颜色
            for (uint32_t i = 0; i < m; ++i) {
                uint32_t gv = verts_vec[i];
                if (block_set.count(gv) && result[i] >= 0) {
                    this->m_vColor[gv] = result[i];
                }
            }

            block_count++;
            total_block_verts += static_cast<uint32_t>(block_verts.size());
        }
    }

    // ============================================================
    // 贪心着色单个顶点（选一个不与冲突邻居相同的颜色）
    // ============================================================
    void greedy_color_vertex(uint32_t v) {
        if (this->m_vColor[v] >= 0) return;

        const uint32_t K = this->m_color_num;
        std::vector<bool> used(K, false);

        if (v < m_adj_conflict.size()) {
            const std::vector<uint32_t>& conf = m_adj_conflict[v];
            for (size_t i = 0; i < conf.size(); ++i) {
                int8_t c = this->m_vColor[conf[i]];
                if (c >= 0 && c < static_cast<int8_t>(K)) used[c] = true;
            }
        }

        // 优先选缝合邻居最多使用的颜色（减少stitch cost）
        if (v < m_adj_stitch.size() && !m_adj_stitch[v].empty()) {
            std::vector<int> stitch_cnt(K, 0);
            const std::vector<uint32_t>& st = m_adj_stitch[v];
            for (size_t i = 0; i < st.size(); ++i) {
                int8_t c = this->m_vColor[st[i]];
                if (c >= 0 && c < static_cast<int8_t>(K)) stitch_cnt[c]++;
            }
            int best_cnt = -1;
            int8_t best_c = -1;
            for (int8_t c = 0; c < static_cast<int8_t>(K); ++c) {
                if (!used[c] && stitch_cnt[c] > best_cnt) {
                    best_cnt = stitch_cnt[c];
                    best_c = c;
                }
            }
            if (best_c >= 0) {
                this->m_vColor[v] = best_c;
                return;
            }
        }

        // 选第一个可用颜色
        for (int8_t c = 0; c < static_cast<int8_t>(K); ++c) {
            if (!used[c]) { this->m_vColor[v] = c; return; }
        }
        this->m_vColor[v] = 0; // fallback
    }

    // ============================================================
    // 密度统计
    // ============================================================
    void compute_density_statistics() {
        const uint32_t n = boost::num_vertices(this->m_graph);
        m_conflict_degree.assign(n, 0);

        for (uint32_t v = 0; v < n; ++v) {
            if (m_simplified_set.count(v)) continue;
            if (v < m_adj_conflict.size())
                m_conflict_degree[v] = static_cast<uint32_t>(m_adj_conflict[v].size());
        }

        double sum = 0.0;
        uint32_t count = 0;
        for (uint32_t v = 0; v < n; ++v) {
            if (m_simplified_set.count(v)) continue;
            if (m_conflict_degree[v] > 0) { sum += m_conflict_degree[v]; count++; }
        }
        m_density_mean = (count > 0) ? sum / count : 0;

        double var_sum = 0.0;
        for (uint32_t v = 0; v < n; ++v) {
            if (m_simplified_set.count(v)) continue;
            if (m_conflict_degree[v] > 0) {
                double diff = m_conflict_degree[v] - m_density_mean;
                var_sum += diff * diff;
            }
        }
        m_density_sigma = (count > 1) ? std::sqrt(var_sum / count) : 0;
        m_high_density_thr = m_density_mean + 0.5 * m_density_sigma;
    }

    // ============================================================
    // 密度感知BFS排序
    // ============================================================
    void density_aware_bfs_sort_edges(std::vector<BilevelEdge>& sorted) {
        const uint32_t n = boost::num_vertices(this->m_graph);
        std::vector<bool> visited(n, false);
        sorted.clear();

        std::vector<std::pair<double, uint32_t>> score_vertex;
        score_vertex.reserve(n);
        vertex_iterator vi, vi_end;
        for (boost::tie(vi, vi_end) = boost::vertices(this->m_graph); vi != vi_end; ++vi) {
            uint32_t idx = boost::get(boost::vertex_index, this->m_graph, *vi);
            //if (m_simplified_set.count(idx)) continue;
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
    }
    
    void collect_all_edges(std::vector<BilevelEdge>& edges) {
        edges.clear();
        std::unordered_set<uint64_t> edge_set;

        edge_iterator ei, ei_end;
        for (boost::tie(ei, ei_end) = boost::edges(this->m_graph); ei != ei_end; ++ei) {
            vertex_descriptor s = boost::source(*ei, this->m_graph);
            vertex_descriptor t = boost::target(*ei, this->m_graph);
            if (s == t) continue;

            uint32_t si = boost::get(boost::vertex_index, this->m_graph, s);
            uint32_t ti = boost::get(boost::vertex_index, this->m_graph, t);

            if (m_simplified_set.count(si) || m_simplified_set.count(ti)) continue;

            uint64_t k = edgeKey(si, ti);
            if (!edge_set.insert(k).second) continue;

            double w = boost::get(boost::edge_weight, this->m_graph, *ei);
            edges.push_back(toBilevelEdge(si, ti, w >= 0, std::abs(w)));
        }
    }
    
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
                    //if (m_simplified_set.count(u_idx)) continue;

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

    // ============================================================
    // 以下为基础辅助函数（与SATFAST一致）
    // ============================================================

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

            m_full_adj_vec[si].push_back(std::make_pair(ti, is_conflict));
            m_full_adj_vec[ti].push_back(std::make_pair(si, is_conflict));

            if (is_conflict) {
                m_adj_conflict[si].push_back(ti);
                m_adj_conflict[ti].push_back(si);
            } else {
                m_adj_stitch[si].push_back(ti);
                m_adj_stitch[ti].push_back(si);
            }
        }
    }

    void compute_parent_node_ids() {
        const uint32_t n = boost::num_vertices(this->m_graph);
        m_parent_node_ids.assign(n, static_cast<uint32_t>(-1));
        m_parent_count = 0;
        vertex_iterator vi, vi_end;
        for (boost::tie(vi, vi_end) = boost::vertices(this->m_graph); vi != vi_end; ++vi) {
            uint32_t idx = boost::get(boost::vertex_index, this->m_graph, *vi);
            if (m_parent_node_ids[idx] != static_cast<uint32_t>(-1)) continue;
            m_parent_node_ids[idx] = m_parent_count;
            std::queue<vertex_descriptor> q;
            q.push(*vi);
            while (!q.empty()) {
                vertex_descriptor cur = q.front(); q.pop();
                adjacency_iterator ai, ai_end;
                for (boost::tie(ai, ai_end) = boost::adjacent_vertices(cur, this->m_graph);
                     ai != ai_end; ++ai)
                {
                    std::pair<edge_descriptor, bool> ep = boost::edge(cur, *ai, this->m_graph);
                    if (!ep.second || boost::get(boost::edge_weight, this->m_graph, ep.first) >= 0)
                        continue;
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

    void simplify_graph() {
        const uint32_t n = boost::num_vertices(this->m_graph);
        m_simplified_verts.clear();
        m_simplified_neighbor.clear();
        m_simplified_set.clear();

        std::vector<int> effective_degree(n, 0);
        std::vector<bool> removed(n, false);

        vertex_iterator vi, vi_end;
        for (boost::tie(vi, vi_end) = boost::vertices(this->m_graph); vi != vi_end; ++vi) {
            uint32_t idx = boost::get(boost::vertex_index, this->m_graph, *vi);
            adjacency_iterator ai, ai_end;
            int deg = 0;
            for (boost::tie(ai, ai_end) = boost::adjacent_vertices(*vi, this->m_graph);
                 ai != ai_end; ++ai)
            {
                uint32_t ni = boost::get(boost::vertex_index, this->m_graph, *ai);
                if (ni != idx) deg++;
            }
            effective_degree[idx] = deg;
        }

        std::queue<uint32_t> work_queue;
        for (uint32_t i = 0; i < n; ++i)
            if (effective_degree[i] <= 1) work_queue.push(i);

        while (!work_queue.empty()) {
            uint32_t idx = work_queue.front();
            work_queue.pop();
            if (removed[idx]) continue;

            vertex_descriptor v = boost::vertex(idx, this->m_graph);
            int deg = 0;
            uint32_t last_neighbor = idx;
            adjacency_iterator ai, ai_end;
            for (boost::tie(ai, ai_end) = boost::adjacent_vertices(v, this->m_graph);
                 ai != ai_end; ++ai)
            {
                uint32_t ni = boost::get(boost::vertex_index, this->m_graph, *ai);
                if (!removed[ni] && ni != idx) { deg++; last_neighbor = ni; }
            }

            if (deg == 0) {
                this->m_vColor[idx] = 0;
                removed[idx] = true;
                m_simplified_verts.push_back(idx);
                m_simplified_set.insert(idx);
                for (boost::tie(ai, ai_end) = boost::adjacent_vertices(v, this->m_graph);
                     ai != ai_end; ++ai)
                {
                    uint32_t ni = boost::get(boost::vertex_index, this->m_graph, *ai);
                    if (!removed[ni]) work_queue.push(ni);
                }
            } else if (deg == 1) {
                removed[idx] = true;
                m_simplified_neighbor[idx] = last_neighbor;
                m_simplified_verts.push_back(idx);
                m_simplified_set.insert(idx);
                for (boost::tie(ai, ai_end) = boost::adjacent_vertices(v, this->m_graph);
                     ai != ai_end; ++ai)
                {
                    uint32_t ni = boost::get(boost::vertex_index, this->m_graph, *ai);
                    if (!removed[ni]) work_queue.push(ni);
                }
            }
        }
        mplPrint(kINFO, "DPSAT: Simplified %lu vertices (total %u)\n",
                 m_simplified_verts.size(), n);
    }

    void restore_simplified_vertices() {
        const uint32_t K = this->m_color_num;
        for (int i = static_cast<int>(m_simplified_verts.size()) - 1; i >= 0; i--) {
            uint32_t v = m_simplified_verts[i];
            if (this->m_vColor[v] >= 0) continue;
            std::unordered_map<uint32_t, uint32_t>::const_iterator it =
                m_simplified_neighbor.find(v);
            if (it == m_simplified_neighbor.end()) { this->m_vColor[v] = 0; continue; }
            uint32_t nb = it->second;
            int8_t nbc = this->m_vColor[nb];
            std::pair<edge_descriptor, bool> ep = boost::edge(
                boost::vertex(v, this->m_graph),
                boost::vertex(nb, this->m_graph), this->m_graph);
            if (ep.second) {
                if (boost::get(boost::edge_weight, this->m_graph, ep.first) >= 0) {
                    for (int8_t c = 0; c < static_cast<int8_t>(K); c++)
                        if (c != nbc) { this->m_vColor[v] = c; break; }
                } else {
                    this->m_vColor[v] = (nbc >= 0) ? nbc : 0;
                }
            } else {
                this->m_vColor[v] = 0;
            }
        }
    }

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

            for (std::unordered_map<uint32_t, std::vector<uint32_t>>::iterator pit = pm.begin();
                 pit != pm.end(); ++pit)
            {
                if (pit->second.size() <= 1) continue;
                std::vector<int> cnt(K, 0);
                for (size_t j = 0; j < pit->second.size(); ++j) {
                    uint32_t v = pit->second[j];
                    if (this->m_vColor[v] >= 0 && this->m_vColor[v] < static_cast<int8_t>(K))
                        cnt[this->m_vColor[v]]++;
                }
                int8_t maj = static_cast<int8_t>(
                    std::distance(cnt.begin(), std::max_element(cnt.begin(), cnt.end())));
                for (size_t j = 0; j < pit->second.size(); ++j) {
                    uint32_t v = pit->second[j];
                    if (this->m_vColor[v] != maj && can_recolor_fast(v, maj)) {
                        this->m_vColor[v] = maj; imp = true;
                    }
                }
            }

            // 阶段2: 逐顶点缝合代价最小化
            for (uint32_t v = 0; v < n; ++v) {
                if (m_simplified_set.count(v) || this->m_vColor[v] < 0) continue;
                int8_t cur = this->m_vColor[v];
                int cs = count_active_stitches_fast(v);
                if (cs == 0) continue;
                int8_t best = cur; int bs = cs;
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

    bool can_recolor_fast(uint32_t v, int8_t c) const {
        if (v >= m_adj_conflict.size()) return true;
        const std::vector<uint32_t>& conf = m_adj_conflict[v];
        for (size_t i = 0; i < conf.size(); ++i)
            if (this->m_vColor[conf[i]] == c) return false;
        return true;
    }

    int count_active_stitches_fast(uint32_t v) const {
        if (v >= m_adj_stitch.size()) return 0;
        int cnt = 0;
        const std::vector<uint32_t>& st = m_adj_stitch[v];
        for (size_t i = 0; i < st.size(); ++i)
            if (this->m_vColor[v] != this->m_vColor[st[i]]) cnt++;
        return cnt;
    }

    virtual std::string algorithm_name() const { return "DP_SAT"; }
};

SIMPLEMPL_END_NAMESPACE

#endif // SIMPLEMPL_DPSATCOLORING_H
