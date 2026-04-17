#ifndef SIMPLEMPL_SATBILEVELCOLORING_H
#define SIMPLEMPL_SATBILEVELCOLORING_H

#include "Namespace.h"
#include "MinisatPlusSolver.h"
#include <limbo/algorithms/coloring/Coloring.h>

#include <vector>
#include <set>
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

class BilevelSATEngine {
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
        uint32_t K)
    {
        uint32_t m = static_cast<uint32_t>(verts.size());
        if (m == 0) return;

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

        // ============================================================
        // Phase 1: Minimize conflicts — eq (5)
        // ============================================================
        std::vector<Minisat::Var> cvars;
        cvars.reserve(pair_keys.size());
        std::vector<bool> cvar_vals;

        if (!pair_keys.empty()) {
            Minisat::vec<Minisat::Lit> v5;

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

                    // (4c)
                    v5.clear();
                    v5.push(xi0); v5.push(xi1);
                    v5.push(xj0); v5.push(xj1);
                    v5.push(cl);
                    S.addClause(v5);

                    // (4d)
                    v5.clear();
                    v5.push(~xi0); v5.push(xi1);
                    v5.push(~xj0); v5.push(xj1);
                    v5.push(cl);
                    S.addClause(v5);

                    // (4e)
                    v5.clear();
                    v5.push(xi0); v5.push(~xi1);
                    v5.push(xj0); v5.push(~xj1);
                    v5.push(cl);
                    S.addClause(v5);

                    // (4f) QPLD only
                    if (K == 4) {
                        v5.clear();
                        v5.push(~xi0); v5.push(~xi1);
                        v5.push(~xj0); v5.push(~xj1);
                        v5.push(cl);
                        S.addClause(v5);
                    }

                    // Strengthening: 2-literal implied clauses
                    S.addClause(~xi0, ~xj0, cl);
                    S.addClause(~xi1, ~xj1, cl);
                }
            }

            TotalizerHandle ctot = S.buildTotalizer(cvars);
            int res = S.minimizeWithBinarySearch(ctot, cvars);
            if (res < 0) {
                for (uint32_t i = 0; i < m; ++i)
                    out_colors[i] = (fixed[i] >= 0) ? fixed[i] : 0;
                return;
            }
            cvar_vals.resize(cvars.size());
            for (size_t i = 0; i < cvars.size(); ++i)
                cvar_vals[i] = S.isTrue(cvars[i]);
        } else {
            if (!S.solve()) {
                for (uint32_t i = 0; i < m; ++i)
                    out_colors[i] = (fixed[i] >= 0) ? fixed[i] : 0;
                return;
            }
        }

        // Extract Phase 1 colors
        for (uint32_t i = 0; i < m; ++i) {
            int b0 = S.isTrue(bit0[i]) ? 1 : 0;
            int b1 = S.isTrue(bit1[i]) ? 1 : 0;
            int8_t c = static_cast<int8_t>(b1 * 2 + b0);
            if (c >= static_cast<int8_t>(K)) c = 0;
            out_colors[i] = c;
        }

        // ============================================================
        // Phase 2: Minimize stitches — eq (6)
        // ============================================================
        if (stitch_eids.empty()) return;

        if (!cvars.empty()) {
            for (size_t i = 0; i < cvars.size(); ++i)
                S.fixVar(cvars[i], cvar_vals[i]);
        }

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

            S.addClause(xi0, ~xj0, sl);   // (4g)
            S.addClause(~xi0, xj0, sl);   // (4h)
            S.addClause(xi1, ~xj1, sl);   // (4i)
            S.addClause(~xi1, xj1, sl);   // (4j)
        }

        if (svars.empty()) return;

        TotalizerHandle stot = S.buildTotalizer(svars);

        // Try 0 first
        if (S.solveWithBound(stot, 0)) {
            for (uint32_t i = 0; i < m; ++i) {
                int b0 = S.isTrue(bit0[i]) ? 1 : 0;
                int b1 = S.isTrue(bit1[i]) ? 1 : 0;
                int8_t c = static_cast<int8_t>(b1 * 2 + b0);
                if (c >= static_cast<int8_t>(K)) c = 0;
                out_colors[i] = c;
            }
            return;
        }

        // Get upper bound
        int max_s = static_cast<int>(svars.size());
        if (!S.solveWithBound(stot, max_s)) {
            return;
        }

        int best_ns = 0;
        for (size_t i = 0; i < svars.size(); ++i)
            if (S.isTrue(svars[i])) best_ns++;

        if (best_ns == 0) {
            for (uint32_t i = 0; i < m; ++i) {
                int b0 = S.isTrue(bit0[i]) ? 1 : 0;
                int b1 = S.isTrue(bit1[i]) ? 1 : 0;
                int8_t c = static_cast<int8_t>(b1 * 2 + b0);
                if (c >= static_cast<int8_t>(K)) c = 0;
                out_colors[i] = c;
            }
            return;
        }

        // Adaptive binary-style descent
        // Use binary search between 0 (already failed) and best_ns
        {
            int lo = 1;  // 0 already failed
            int hi = best_ns;

            while (lo < hi) {
                int mid = lo + (hi - lo) / 2;
                if (S.solveWithBound(stot, mid)) {
                    // Feasible at mid, count actual
                    int actual = 0;
                    for (size_t i = 0; i < svars.size(); ++i)
                        if (S.isTrue(svars[i])) actual++;
                    hi = actual;  // tighten: actual could be < mid
                } else {
                    lo = mid + 1;  // need more
                }
                // Limit iterations to avoid timeout on large cases
                if (hi - lo <= 1) break;
            }

            // Final: try lo if lo < hi
            if (lo < hi) {
                if (S.solveWithBound(stot, lo)) {
                    int actual = 0;
                    for (size_t i = 0; i < svars.size(); ++i)
                        if (S.isTrue(svars[i])) actual++;
                    hi = actual;
                }
            }

            best_ns = hi;
        }

        // Ensure valid model
        S.solveWithBound(stot, best_ns);

        // Extract final colors
        for (uint32_t i = 0; i < m; ++i) {
            int b0 = S.isTrue(bit0[i]) ? 1 : 0;
            int b1 = S.isTrue(bit1[i]) ? 1 : 0;
            int8_t c = static_cast<int8_t>(b1 * 2 + b0);
            if (c >= static_cast<int8_t>(K)) c = 0;
            out_colors[i] = c;
        }
    }
};

// ============================================================
// SATBilevelColoring
// ============================================================
template <typename GraphType>
class SATBilevelColoring
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

    SATBilevelColoring(graph_type const& g) : base_type(g), m_parent_count(0) {}
    virtual ~SATBilevelColoring() {}

protected:
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
        all_edges.reserve(ec);

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
        for (uint32_t i = 0; i < mv; ++i) {
            if (this->m_vColor[verts[i]] >= 0)
                fixed[i] = this->m_vColor[verts[i]];
        }

        std::vector<int8_t> result(mv, -1);
        BilevelSATEngine::solve(
            verts, all_edges, g2l, fixed, result,
            this->m_color_num);

        /*auto t_end = std::chrono::high_resolution_clock::now();
        double elapsed = std::chrono::duration<double>(t_end - t_start).count();
        if (elapsed <= 1)
            mplPrint(kINFO, "SAT-BILEVEL(%u edges): Total time for subgraph: %.4fs\n", ec, elapsed);
        else
            mplPrint(kINFO, "SAT-BILEVEL(%u edges): Total time for subgraph: %.4fs !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n", ec, elapsed);*/

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

    virtual std::string algorithm_name() const { return "SAT_BILEVEL"; }
};

SIMPLEMPL_END_NAMESPACE

#endif
