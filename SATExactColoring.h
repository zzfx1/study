#ifndef SIMPLEMPL_SATEXACTCOLORING_H
#define SIMPLEMPL_SATEXACTCOLORING_H

#include "Namespace.h"
#include "MinisatPlusSolver.h"
#include <limbo/algorithms/coloring/Coloring.h>

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <cassert>
#include <queue>
#include <cmath>
#include <cstdint>
#include <chrono>

SIMPLEMPL_BEGIN_NAMESPACE

#ifndef SIMPLEMPL_BILEVELEDGE_DEFINED
#define SIMPLEMPL_BILEVELEDGE_DEFINED
struct BilevelEdge {
    uint32_t u_idx, v_idx;
    uint32_t u_parent, v_parent;
    bool   is_conflict;
    double weight;
};
#endif

class ExactSATEngine {
public:
    static uint64_t pairKey(uint32_t a, uint32_t b) {
        if (a > b) std::swap(a, b);
        return (static_cast<uint64_t>(a) << 32) | b;
    }

    static void solve(
        const std::vector<uint32_t>& verts,
        const std::vector<BilevelEdge>& edges,
        const std::unordered_map<uint32_t, uint32_t>& g2l,
        const std::vector<int8_t>& fixed,
        std::vector<int8_t>& out_colors,
        uint32_t K,
        double alpha)
    {
        uint32_t m = static_cast<uint32_t>(verts.size());
        if (m == 0) return;

        int wc, ws;
        computeIntegerWeights(alpha, wc, ws);

        MinisatPlusSolver S;
        std::vector<Minisat::Var> bit0(m), bit1(m);

        for (uint32_t i = 0; i < m; ++i) {
            bit0[i] = S.newVar();
            bit1[i] = S.newVar();
            if (K == 3 && fixed[i] < 0)
                S.addClause(~Minisat::mkLit(bit0[i]),
                            ~Minisat::mkLit(bit1[i]));
            if (fixed[i] >= 0) {
                S.fixVar(bit0[i], (fixed[i] & 1) == 1);
                S.fixVar(bit1[i], ((fixed[i] >> 1) & 1) == 1);
            }
        }

        // Group conflict edges by parent pair
        std::unordered_map<uint64_t, std::vector<uint32_t> > pair_edges;
        pair_edges.reserve(edges.size() / 2);
        std::vector<uint64_t> pair_keys;
        pair_keys.reserve(edges.size() / 2);
        std::vector<uint32_t> stitch_eids;
        stitch_eids.reserve(edges.size() / 4);
        {
            std::unordered_set<uint64_t> seen;
            seen.reserve(edges.size());
            for (uint32_t i = 0; i < static_cast<uint32_t>(edges.size()); ++i) {
                const BilevelEdge& e = edges[i];
                if (g2l.find(e.u_idx) == g2l.end() ||
                    g2l.find(e.v_idx) == g2l.end()) continue;
                if (e.is_conflict) {
                    uint64_t pk = pairKey(e.u_parent, e.v_parent);
                    pair_edges[pk].push_back(i);
                    if (seen.insert(pk).second)
                        pair_keys.push_back(pk);
                } else {
                    stitch_eids.push_back(i);
                }
            }
        }

        // Create cvars + conflict clauses
        std::vector<Minisat::Var> cvars;
        cvars.reserve(pair_keys.size());
        std::vector<Minisat::Lit> v5;
        v5.reserve(5);

        for (size_t pi = 0; pi < pair_keys.size(); ++pi) {
            uint64_t pk = pair_keys[pi];
            Minisat::Var c = S.newVar();
            cvars.push_back(c);

            const std::vector<uint32_t>& eids = pair_edges[pk];
            std::unordered_set<uint64_t> added;
            added.reserve(eids.size());

            for (size_t ei = 0; ei < eids.size(); ++ei) {
                const BilevelEdge& e = edges[eids[ei]];
                uint32_t li = g2l.find(e.u_idx)->second;
                uint32_t lj = g2l.find(e.v_idx)->second;
                uint64_t vk = pairKey(li, lj);
                if (!added.insert(vk).second) continue;

                Minisat::Lit xi0 = Minisat::mkLit(bit0[li]);
                Minisat::Lit xi1 = Minisat::mkLit(bit1[li]);
                Minisat::Lit xj0 = Minisat::mkLit(bit0[lj]);
                Minisat::Lit xj1 = Minisat::mkLit(bit1[lj]);
                Minisat::Lit cl  = Minisat::mkLit(c);

                v5.clear();
                v5.push_back(xi0); v5.push_back(xi1);
                v5.push_back(xj0); v5.push_back(xj1);
                v5.push_back(cl); S.addClause(v5);

                v5.clear();
                v5.push_back(~xi0); v5.push_back(xi1);
                v5.push_back(~xj0); v5.push_back(xj1);
                v5.push_back(cl); S.addClause(v5);

                v5.clear();
                v5.push_back(xi0); v5.push_back(~xi1);
                v5.push_back(xj0); v5.push_back(~xj1);
                v5.push_back(cl); S.addClause(v5);

                if (K == 4) {
                    v5.clear();
                    v5.push_back(~xi0); v5.push_back(~xi1);
                    v5.push_back(~xj0); v5.push_back(~xj1);
                    v5.push_back(cl); S.addClause(v5);
                }
            }
        }

        // Create svars + stitch clauses
        std::vector<Minisat::Var> svars;
        svars.reserve(stitch_eids.size());

        for (size_t idx = 0; idx < stitch_eids.size(); ++idx) {
            const BilevelEdge& e = edges[stitch_eids[idx]];
            uint32_t li = g2l.find(e.u_idx)->second;
            uint32_t lj = g2l.find(e.v_idx)->second;
            Minisat::Var s = S.newVar();
            svars.push_back(s);

            Minisat::Lit xi0 = Minisat::mkLit(bit0[li]);
            Minisat::Lit xi1 = Minisat::mkLit(bit1[li]);
            Minisat::Lit xj0 = Minisat::mkLit(bit0[lj]);
            Minisat::Lit xj1 = Minisat::mkLit(bit1[lj]);
            Minisat::Lit sl  = Minisat::mkLit(s);

            S.addClause(~xi0, xj0, sl);
            S.addClause(xi0, ~xj0, sl);
            S.addClause(~xi1, xj1, sl);
            S.addClause(xi1, ~xj1, sl);
        }

        // Initial feasibility solve
        if (!S.solve()) {
            for (uint32_t i = 0; i < m; ++i)
                out_colors[i] = (fixed[i] >= 0) ? fixed[i] : 0;
            return;
        }

        // ============================================================
        // 核心优化：双Totalizer枚举法
        //
        // 原方法：把 cvar 复制 wc 次、svar 复制 ws 次拼成一个巨大
        //         totalizer，对 alpha=0.1 时变量膨胀 10 倍。
        //
        // 新方法：分别对 cvars 和 svars 各建一个 totalizer，
        //         然后枚举冲突数 nc = 0..max_c，对每个 nc 求
        //         最小缝合数 ns，总cost = nc*wc + ns*ws。
        //         由于 nc 的范围通常很小（0~几十），总 SAT 调用
        //         次数远少于在膨胀 totalizer 上做二分搜索。
        //
        // 关键性质：冲突数 nc 一般很小（往往为0），所以外层
        //           枚举几乎不增加开销；而内层对 svars 的
        //           totalizer 规模等于缝合边数（无膨胀）。
        // ============================================================

        if (cvars.empty() && svars.empty()) {
            extractColors(S, bit0, bit1, out_colors, K, m);
            return;
        }

        int best_cost = countWeightedCost(S, cvars, svars, wc, ws);
        std::vector<int8_t> best_colors(m);
        extractColors(S, bit0, bit1, best_colors, K, m);

        if (best_cost == 0) {
            for (uint32_t i = 0; i < m; ++i)
                out_colors[i] = best_colors[i];
            return;
        }

        // 只有缝合边没有冲突边：直接对svars做totalizer最小化
        if (cvars.empty()) {
            TotalizerHandle stot = S.buildTotalizer(svars);
            minimizeExact(S, stot, svars, best_cost, ws,
                          bit0, bit1, best_colors, K, m,
                          cvars, svars, wc, ws);
            for (uint32_t i = 0; i < m; ++i)
                out_colors[i] = best_colors[i];
            return;
        }

        // 只有冲突边没有缝合边：直接对cvars做totalizer最小化
        if (svars.empty()) {
            TotalizerHandle ctot = S.buildTotalizer(cvars);
            minimizeExact(S, ctot, cvars, best_cost, wc,
                          bit0, bit1, best_colors, K, m,
                          cvars, svars, wc, ws);
            for (uint32_t i = 0; i < m; ++i)
                out_colors[i] = best_colors[i];
            return;
        }

        // 两者都有：双totalizer枚举
        TotalizerHandle ctot = S.buildTotalizer(cvars);
        TotalizerHandle stot = S.buildTotalizer(svars);

        int max_c = static_cast<int>(cvars.size());
        int max_s = static_cast<int>(svars.size());

        // 从当前解出发确定初始的冲突数上界
        int init_nc = 0;
        for (size_t i = 0; i < cvars.size(); ++i)
            if (S.isTrue(cvars[i])) init_nc++;

        // 枚举冲突数 nc = 0, 1, 2, ...
        // 对每个 nc，在 assumptions 中固定冲突 totalizer 的 bound，
        // 然后用二分搜索最小化缝合数
        for (int nc = 0; nc <= max_c; ++nc) {
            int cost_floor = nc * wc;
            if (cost_floor >= best_cost) break;  // 剪枝

            int max_stitch_budget = (best_cost - cost_floor - 1) / ws;
            if (max_stitch_budget < 0) continue;
            if (max_stitch_budget > max_s) max_stitch_budget = max_s;

            // 用 assumptions 临时设置冲突 bound = nc
            // 即 ctot 的 output[nc] 必须为 false（至多 nc 个冲突为真）
            std::vector<Minisat::Lit> c_assumps;
            {
                const auto& c_outs = ctot.rootOutputs();
                int c_sz = static_cast<int>(c_outs.size());
                for (int i = nc; i < c_sz; i++)
                    c_assumps.push_back(~Minisat::mkLit(c_outs[i]));
            }

            // 检查 nc 个冲突是否可行
            if (!S.solveWithBound(stot, max_stitch_budget, c_assumps)) {
                // 即使允许 max_stitch_budget 个缝合也不可行
                // 尝试不限制缝合数
                if (!S.solveWithBound(stot, max_s, c_assumps)) {
                    continue;  // nc 个冲突不可行
                }
            }

            // nc 个冲突可行，二分搜索最小化缝合数
            int actual_nc = 0;
            for (size_t i = 0; i < cvars.size(); ++i)
                if (S.isTrue(cvars[i])) actual_nc++;
            int actual_ns = 0;
            for (size_t i = 0; i < svars.size(); ++i)
                if (S.isTrue(svars[i])) actual_ns++;

            int cur_cost = actual_nc * wc + actual_ns * ws;
            if (cur_cost < best_cost) {
                best_cost = cur_cost;
                extractColors(S, bit0, bit1, best_colors, K, m);
                if (best_cost == 0) break;
            }

            // 二分搜索缝合数
            int s_lo = 0;
            int s_hi = actual_ns;

            while (s_lo < s_hi) {
                int s_mid = s_lo + (s_hi - s_lo) / 2;
                int trial_cost = nc * wc + s_mid * ws;
                if (trial_cost >= best_cost) {
                    s_hi = s_mid;
                    continue;
                }

                if (S.solveWithBound(stot, s_mid, c_assumps)) {
                    int ns2 = 0;
                    for (size_t i = 0; i < svars.size(); ++i)
                        if (S.isTrue(svars[i])) ns2++;
                    int nc2 = 0;
                    for (size_t i = 0; i < cvars.size(); ++i)
                        if (S.isTrue(cvars[i])) nc2++;
                    int c2 = nc2 * wc + ns2 * ws;
                    if (c2 < best_cost) {
                        best_cost = c2;
                        extractColors(S, bit0, bit1, best_colors, K, m);
                        if (best_cost == 0) break;
                    }
                    s_hi = ns2;
                } else {
                    s_lo = s_mid + 1;
                }
            }

            // 线性精修
            while (true) {
                int trial_ns = s_lo - 1;
                if (trial_ns < 0) break;
                int trial_cost = nc * wc + trial_ns * ws;
                if (trial_cost >= best_cost) break;

                if (S.solveWithBound(stot, trial_ns, c_assumps)) {
                    int ns2 = 0;
                    for (size_t i = 0; i < svars.size(); ++i)
                        if (S.isTrue(svars[i])) ns2++;
                    int nc2 = 0;
                    for (size_t i = 0; i < cvars.size(); ++i)
                        if (S.isTrue(cvars[i])) nc2++;
                    int c2 = nc2 * wc + ns2 * ws;
                    if (c2 < best_cost) {
                        best_cost = c2;
                        extractColors(S, bit0, bit1, best_colors, K, m);
                    }
                    s_lo = ns2;
                    if (s_lo == 0) break;
                } else {
                    break;
                }
            }

            if (best_cost == 0) break;
            if (best_cost <= (nc + 1) * wc) break;
        }

        for (uint32_t i = 0; i < m; ++i)
            out_colors[i] = best_colors[i];
    }

private:
    static void computeIntegerWeights(double alpha, int& wc, int& ws) {
        if (std::abs(alpha - 0.1) < 1e-12) { wc = 10; ws = 1; return; }
        if (std::abs(alpha - 0.5) < 1e-12) { wc = 2; ws = 1; return; }
        if (std::abs(alpha - 1.0) < 1e-12) { wc = 1; ws = 1; return; }
        for (int k = 1; k <= 100; ++k) {
            double val = k * alpha;
            int ival = static_cast<int>(std::round(val));
            if (std::abs(val - ival) < 1e-9) {
                wc = k; ws = ival;
                int g = gcd_impl(wc, ws);
                if (g > 1) { wc /= g; ws /= g; }
                return;
            }
        }
        wc = 1; ws = 0;
    }

    static int gcd_impl(int a, int b) {
        while (b) { int t = b; b = a % b; a = t; }
        return a;
    }

    static int countWeightedCost(
        const MinisatPlusSolver& S,
        const std::vector<Minisat::Var>& cvars,
        const std::vector<Minisat::Var>& svars,
        int wc, int ws)
    {
        int cost = 0;
        for (size_t i = 0; i < cvars.size(); ++i)
            if (S.isTrue(cvars[i])) cost += wc;
        for (size_t i = 0; i < svars.size(); ++i)
            if (S.isTrue(svars[i])) cost += ws;
        return cost;
    }

    static void extractColors(
        const MinisatPlusSolver& S,
        const std::vector<Minisat::Var>& bit0,
        const std::vector<Minisat::Var>& bit1,
        std::vector<int8_t>& colors,
        uint32_t K, uint32_t m)
    {
        for (uint32_t i = 0; i < m; ++i) {
            int b0 = S.isTrue(bit0[i]) ? 1 : 0;
            int b1 = S.isTrue(bit1[i]) ? 1 : 0;
            int8_t c = static_cast<int8_t>(b1 * 2 + b0);
            if (c >= static_cast<int8_t>(K)) c = 0;
            colors[i] = c;
        }
    }

    // 单目标totalizer最小化（只有一种变量类型时使用）
    static void minimizeExact(
        MinisatPlusSolver& S,
        TotalizerHandle& tot,
        const std::vector<Minisat::Var>& obj,
        int& best_cost,
        int weight,
        const std::vector<Minisat::Var>& bit0,
        const std::vector<Minisat::Var>& bit1,
        std::vector<int8_t>& best_colors,
        uint32_t K, uint32_t m,
        const std::vector<Minisat::Var>& cvars,
        const std::vector<Minisat::Var>& svars,
        int wc, int ws)
    {
        int lo = 0;
        int hi = static_cast<int>(obj.size());

        while (lo < hi) {
            int mid = lo + (hi - lo) / 2;
            if (S.solveWithBound(tot, mid)) {
                int c = countWeightedCost(S, cvars, svars, wc, ws);
                if (c < best_cost) {
                    best_cost = c;
                    extractColors(S, bit0, bit1, best_colors, K, m);
                }
                int cnt = 0;
                for (size_t i = 0; i < obj.size(); ++i)
                    if (S.isTrue(obj[i])) cnt++;
                hi = cnt;
                if (hi == 0) break;
            } else {
                lo = mid + 1;
            }
        }

        while (best_cost > 0 && lo > 0) {
            if (S.solveWithBound(tot, lo - 1)) {
                int c = countWeightedCost(S, cvars, svars, wc, ws);
                if (c < best_cost) {
                    best_cost = c;
                    extractColors(S, bit0, bit1, best_colors, K, m);
                }
                int cnt = 0;
                for (size_t i = 0; i < obj.size(); ++i)
                    if (S.isTrue(obj[i])) cnt++;
                lo = cnt;
            } else {
                break;
            }
        }
    }
};

template <typename GraphType>
class SATExactColoring
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

    SATExactColoring(graph_type const& g)
        : base_type(g), m_alpha(0.1), m_parent_count(0) {}
    virtual ~SATExactColoring() {}
    void setAlpha(double a) { m_alpha = a; }

protected:
    double m_alpha;
    std::vector<uint32_t> m_parent_node_ids;
    uint32_t m_parent_count;

    virtual double coloring()
    {
        //auto t_start = std::chrono::high_resolution_clock::now();

        const uint32_t n = boost::num_vertices(this->m_graph);
        const uint32_t ec = boost::num_edges(this->m_graph);

        this->m_vColor.assign(n, -1);
        if (n == 0) return 0.0;

        m_parent_count = 0;
        compute_parent_node_ids();

        std::vector<BilevelEdge> all_edges;
        all_edges.reserve(boost::num_edges(this->m_graph));

        edge_iterator ei, ei_end;
        for (boost::tie(ei, ei_end) = boost::edges(this->m_graph);
             ei != ei_end; ++ei)
        {
            vertex_descriptor s = boost::source(*ei, this->m_graph);
            vertex_descriptor t = boost::target(*ei, this->m_graph);
            if (s == t) continue;
            uint32_t si = boost::get(boost::vertex_index, this->m_graph, s);
            uint32_t ti = boost::get(boost::vertex_index, this->m_graph, t);
            double w = boost::get(boost::edge_weight, this->m_graph, *ei);

            BilevelEdge be;
            be.u_idx = si; be.v_idx = ti;
            be.u_parent = m_parent_node_ids[si];
            be.v_parent = m_parent_node_ids[ti];
            be.is_conflict = (w >= 0);
            be.weight = std::abs(w);
            all_edges.push_back(be);
        }

        if (all_edges.empty()) {
            for (uint32_t i = 0; i < n; i++)
                this->m_vColor[i] = 0;
            return 0.0;
        }

        std::unordered_set<uint32_t> vset;
        vset.reserve(all_edges.size());
        for (size_t i = 0; i < all_edges.size(); ++i) {
            vset.insert(all_edges[i].u_idx);
            vset.insert(all_edges[i].v_idx);
        }
        std::vector<uint32_t> verts(vset.begin(), vset.end());
        std::sort(verts.begin(), verts.end());

        uint32_t mv = static_cast<uint32_t>(verts.size());
        std::unordered_map<uint32_t, uint32_t> g2l;
        g2l.reserve(mv * 2);
        for (uint32_t i = 0; i < mv; ++i) g2l[verts[i]] = i;

        std::vector<int8_t> fixed(mv, -1);
        for (uint32_t i = 0; i < mv; ++i)
            if (this->m_vColor[verts[i]] >= 0)
                fixed[i] = this->m_vColor[verts[i]];

        std::vector<int8_t> result(mv, -1);
        ExactSATEngine::solve(
            verts, all_edges, g2l, fixed, result,
            this->m_color_num, m_alpha);

        /*auto t_end = std::chrono::high_resolution_clock::now();
        double elapsed = std::chrono::duration<double>(t_end - t_start).count();
        if (elapsed <= 1)
            mplPrint(kINFO, "SAT-EXACT(%u edges): Total time for subgraph: %.4fs\n", ec, elapsed);
        else mplPrint(kINFO, "SAT-EXACT(%u edges): Total time for subgraph: %.4fs !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n", ec, elapsed);*/

        for (uint32_t i = 0; i < mv; ++i)
            if (result[i] >= 0)
                this->m_vColor[verts[i]] = result[i];

        /*for (uint32_t i = 0; i < n; i++)
            if (this->m_vColor[i] < 0)
                this->m_vColor[i] = 0;*/

        return this->calc_cost(this->m_vColor);
    }

    void compute_parent_node_ids()
    {
        const uint32_t n = boost::num_vertices(this->m_graph);
        m_parent_node_ids.assign(n, static_cast<uint32_t>(-1));
        m_parent_count = 0;
        vertex_iterator vi, vi_end;
        for (boost::tie(vi, vi_end) = boost::vertices(this->m_graph);
             vi != vi_end; ++vi)
        {
            uint32_t idx = boost::get(boost::vertex_index, this->m_graph, *vi);
            if (m_parent_node_ids[idx] != static_cast<uint32_t>(-1)) continue;
            m_parent_node_ids[idx] = m_parent_count;
            std::queue<vertex_descriptor> q;
            q.push(*vi);
            while (!q.empty()) {
                vertex_descriptor cur = q.front(); q.pop();
                adjacency_iterator ai, ai_end;
                for (boost::tie(ai, ai_end) =
                         boost::adjacent_vertices(cur, this->m_graph);
                     ai != ai_end; ++ai)
                {
                    std::pair<edge_descriptor, bool> ep =
                        boost::edge(cur, *ai, this->m_graph);
                    if (!ep.second) continue;
                    edge_weight_type w = boost::get(
                        boost::edge_weight, this->m_graph, ep.first);
                    if (w >= 0) continue;
                    uint32_t ni = boost::get(
                        boost::vertex_index, this->m_graph, *ai);
                    if (m_parent_node_ids[ni] == static_cast<uint32_t>(-1)) {
                        m_parent_node_ids[ni] = m_parent_count;
                        q.push(*ai);
                    }
                }
            }
            ++m_parent_count;
        }
    }

    virtual std::string algorithm_name() const { return "SAT_EXACT"; }
};

SIMPLEMPL_END_NAMESPACE

#endif
