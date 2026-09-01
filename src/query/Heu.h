

#include "Utility.h"

struct HeuGCWorkspace {
    vector<ui> neighbor_mark;
    vector<ui> checked_mark;
    vector<ui> filter_mark;
    vector<ui> clique_mark;
    vector<ui> pool_mark;

    ui neighbor_token;
    ui filter_token;
    ui clique_token;
    ui pool_token;

    HeuGCWorkspace(ui n)
    {
        neighbor_mark.resize(n, 0);
        checked_mark.resize(n, 0);
        filter_mark.resize(n, 0);
        clique_mark.resize(n, 0);
        pool_mark.resize(n, 0);

        neighbor_token = 0;
        filter_token = 0;
        clique_token = 0;
        pool_token = 0;
    }
};

vector<ui> find_a_structural_clique()
{
    vector<ui> clique;

    if(n == 0) return clique;

    int idx = -1;

    ui* peels = new ui[n];
    ui* vis = new ui[n];

    for(ui i = 0; i < n; ++i) peels[i] = i;
    memset(vis, 0, sizeof(ui) * n);

    ListLinearHeap* heap = new ListLinearHeap(n, n - 1);
    heap->init(n, n - 1, peels, degree);

    for(ui i = 0; i < n; ++i) {
        ui u, key;
        heap->pop_min(u, key);

        ui current_vnum = n - i;
        ui min_degree = key;


        if(idx == -1 && min_degree == current_vnum - 1) {
            idx = (int)i;
        }

        peels[i] = u;
        vis[u] = 1;

        for(ui j = pstart[u]; j < pstart[u+1]; ++j) {
            ui v = edges[j];

            if(vis[v] == 0) {
                heap->decrement(v, 1);
            }
        }
    }

    assert(idx != -1);

    for(int i = idx; i < (int)n; ++i) {
        clique.push_back(peels[i]);
    }

    delete heap;
    delete [] peels;
    delete [] vis;

    return clique;
}

ui obtain_new_token(vector<ui>& mark, ui& token)
{
    ++token;

    if(token == 0) {
        fill(mark.begin(), mark.end(), 0);
        token = 1;
    }

    return token;
}

void obtain_gc_neighbors_by_index(ui u,
                                  vector<vector<pair<double,ui>>>& residual_sim_nei,
                                  vector<vector<ui>>& z_list,
                                  vector<vector<pair<double,ui>>>& z_R,
                                  vector<ui>& gc_neighbors,
                                  HeuGCWorkspace& workspace)
{
    gc_neighbors.clear();

    ++workspace.neighbor_token;


    if(workspace.neighbor_token == 0) {
        fill(workspace.neighbor_mark.begin(), workspace.neighbor_mark.end(), 0);
        fill(workspace.checked_mark.begin(), workspace.checked_mark.end(), 0);
        workspace.neighbor_token = 1;
    }

    ui token = workspace.neighbor_token;


    for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
        ui v = edges[i];

        if(v == u) continue;

        if(workspace.neighbor_mark[v] != token) {
            workspace.neighbor_mark[v] = token;
            gc_neighbors.push_back(v);
        }
    }


    for(const auto& simnei : residual_sim_nei[u]) {
        double score = simnei.first;
        ui v = simnei.second;

        if(score < epsi) break;
        if(v == u) continue;

        if(workspace.neighbor_mark[v] != token) {
            workspace.neighbor_mark[v] = token;
            gc_neighbors.push_back(v);
        }
    }


    for(ui z : z_list[u]) {
        assert(z < z_R.size());

        for(const auto& simnei : z_R[z]) {
            double upper_score = simnei.first;
            ui v = simnei.second;

            if(upper_score < epsi) break;
            if(v == u) continue;


            if(workspace.neighbor_mark[v] == token) continue;


            if(workspace.checked_mark[v] == token) continue;

            workspace.checked_mark[v] = token;

            auto jsp = js(u, v);

            if(jsp.first >= epsi) {
                workspace.neighbor_mark[v] = token;
                gc_neighbors.push_back(v);
            }
        }
    }
}

void compute_approximate_gc_degree(vector<vector<pair<double,ui>>>& residual_sim_nei,
                                   vector<vector<ui>>& z_list,
                                   vector<vector<pair<double,ui>>>& z_R,
                                   vector<eid>& approximate_degree)
{
    approximate_degree.resize(n);


    vector<ui> z_candidate_count(z_R.size(), 0);

    for(ui z = 0; z < z_R.size(); ++z) {
        for(const auto& e : z_R[z]) {
            if(e.first < epsi) break;
            ++z_candidate_count[z];
        }
    }

    for(ui u = 0; u < n; ++u) {
        eid score = degree[u];


        for(const auto& e : residual_sim_nei[u]) {
            if(e.first < epsi) break;
            ++score;
        }


        for(ui z : z_list[u]) {
            assert(z < z_candidate_count.size());
            score += z_candidate_count[z];
        }

        approximate_degree[u] = score;
    }
}

vector<ui> obtain_top_seed_vertices(const vector<eid>& approximate_degree, ui seed_num)
{
    using ScoreVertex = pair<eid,ui>;

    priority_queue<ScoreVertex, vector<ScoreVertex>, greater<ScoreVertex>> min_heap;

    for(ui u = 0; u < n; ++u) {
        ScoreVertex item = make_pair(approximate_degree[u], u);

        if(min_heap.size() < seed_num) {
            min_heap.push(item);
        }
        else if(item > min_heap.top()) {
            min_heap.pop();
            min_heap.push(item);
        }
    }

    vector<ui> seeds;

    while(!min_heap.empty()) {
        seeds.push_back(min_heap.top().second);
        min_heap.pop();
    }

    sort(seeds.begin(), seeds.end(), [&](ui u, ui v) {
        if(approximate_degree[u] != approximate_degree[v]) {
            return approximate_degree[u] > approximate_degree[v];
        }

        return u < v;
    });

    return seeds;
}

vector<ui> obtain_top_vertices_from_list(const vector<ui>& vertices,
                                         const vector<eid>& approximate_degree,
                                         ui top_num)
{
    vector<ui> top_vertices;

    for(ui v : vertices) {
        auto iter = top_vertices.begin();

        while(iter != top_vertices.end()) {
            ui current = *iter;

            if(approximate_degree[v] > approximate_degree[current]) break;

            if(approximate_degree[v] == approximate_degree[current] && v < current) break;

            ++iter;
        }

        top_vertices.insert(iter, v);

        if(top_vertices.size() > top_num) {
            top_vertices.pop_back();
        }
    }

    return top_vertices;
}

ui choose_next_gc_vertex(const vector<ui>& candidates,
                         const vector<eid>& approximate_degree,
                         ui lookahead,
                         vector<vector<pair<double,ui>>>& residual_sim_nei,
                         vector<vector<ui>>& z_list,
                         vector<vector<pair<double,ui>>>& z_R,
                         vector<ui>& selected_neighbors,
                         HeuGCWorkspace& workspace)
{
    assert(!candidates.empty());

    lookahead = max((ui)1, lookahead);

    vector<ui> top_candidates = obtain_top_vertices_from_list(candidates, approximate_degree, lookahead);


    ui pool_token = obtain_new_token(workspace.pool_mark, workspace.pool_token);

    for(ui v : candidates) {
        workspace.pool_mark[v] = pool_token;
    }

    ui best_vertex = top_candidates[0];
    eid best_remaining_count = 0;
    eid best_static_score = 0;

    selected_neighbors.clear();

    for(ui v : top_candidates) {
        vector<ui> v_neighbors;

        obtain_gc_neighbors_by_index(v, residual_sim_nei, z_list, z_R, v_neighbors, workspace);

        eid remaining_count = 0;

        for(ui x : v_neighbors) {
            if(workspace.pool_mark[x] == pool_token) {
                ++remaining_count;
            }
        }

        if(selected_neighbors.empty() ||
           remaining_count > best_remaining_count ||
           (remaining_count == best_remaining_count && approximate_degree[v] > best_static_score)) {

            best_vertex = v;
            best_remaining_count = remaining_count;
            best_static_score = approximate_degree[v];

            selected_neighbors.swap(v_neighbors);
        }
    }

    return best_vertex;
}

vector<ui> greedy_expand_gc(vector<ui> clique,
                            const vector<eid>& approximate_degree,
                            ui lookahead,
                            vector<vector<pair<double,ui>>>& residual_sim_nei,
                            vector<vector<ui>>& z_list,
                            vector<vector<pair<double,ui>>>& z_R,
                            HeuGCWorkspace& workspace)
{
    if(clique.empty()) return clique;


    ui clique_token = obtain_new_token(workspace.clique_mark, workspace.clique_token);

    for(ui u : clique) {
        workspace.clique_mark[u] = clique_token;
    }


    ui pivot = clique[0];

    for(ui u : clique) {
        if(approximate_degree[u] < approximate_degree[pivot]) {
            pivot = u;
        }
    }

    vector<ui> candidates;

    obtain_gc_neighbors_by_index(pivot, residual_sim_nei, z_list, z_R, candidates, workspace);


    ui write_pos = 0;

    for(ui v : candidates) {
        if(workspace.clique_mark[v] != clique_token) {
            candidates[write_pos++] = v;
        }
    }

    candidates.resize(write_pos);


    for(ui u : clique) {
        if(u == pivot) continue;
        if(candidates.empty()) break;

        vector<ui> u_neighbors;

        obtain_gc_neighbors_by_index(u, residual_sim_nei, z_list, z_R, u_neighbors, workspace);

        ui filter_token = obtain_new_token(workspace.filter_mark, workspace.filter_token);

        for(ui v : u_neighbors) {
            workspace.filter_mark[v] = filter_token;
        }

        write_pos = 0;

        for(ui v : candidates) {
            if(workspace.filter_mark[v] == filter_token) {
                candidates[write_pos++] = v;
            }
        }

        candidates.resize(write_pos);
    }


    while(!candidates.empty()) {
        vector<ui> selected_neighbors;

        ui selected = choose_next_gc_vertex(candidates,
                                            approximate_degree,
                                            lookahead,
                                            residual_sim_nei,
                                            z_list,
                                            z_R,
                                            selected_neighbors,
                                            workspace);

        clique.push_back(selected);

        ui filter_token = obtain_new_token(workspace.filter_mark, workspace.filter_token);

        for(ui v : selected_neighbors) {
            workspace.filter_mark[v] = filter_token;
        }

        write_pos = 0;

        for(ui v : candidates) {
            if(v == selected) continue;

            if(workspace.filter_mark[v] == filter_token) {
                candidates[write_pos++] = v;
            }
        }

        candidates.resize(write_pos);
    }

    return clique;
}

void improve_gc_by_drop_one(vector<ui>& best_clique,
                            const vector<eid>& approximate_degree,
                            ui try_num,
                            ui lookahead,
                            vector<vector<pair<double,ui>>>& residual_sim_nei,
                            vector<vector<ui>>& z_list,
                            vector<vector<pair<double,ui>>>& z_R,
                            HeuGCWorkspace& workspace)
{
    if(best_clique.size() <= 1) return;


    vector<ui> weak_vertices = best_clique;

    sort(weak_vertices.begin(), weak_vertices.end(), [&](ui u, ui v) {
        if(approximate_degree[u] != approximate_degree[v]) {
            return approximate_degree[u] < approximate_degree[v];
        }

        return u < v;
    });

    try_num = min(try_num, (ui)weak_vertices.size());

    for(ui i = 0; i < try_num; ++i) {
        ui removed_vertex = weak_vertices[i];

        auto position = find(best_clique.begin(), best_clique.end(), removed_vertex);

        if(position == best_clique.end()) continue;

        vector<ui> base_clique;

        for(ui u : best_clique) {
            if(u != removed_vertex) {
                base_clique.push_back(u);
            }
        }

        if(base_clique.empty()) continue;

        vector<ui> new_clique = greedy_expand_gc(base_clique,
                                                 approximate_degree,
                                                 lookahead,
                                                 residual_sim_nei,
                                                 z_list,
                                                 z_R,
                                                 workspace);

        if(new_clique.size() > best_clique.size()) {
            best_clique.swap(new_clique);

            cout << "drop-one improvement, new size: "
                 << best_clique.size() << endl;
        }
    }
}

int find_a_heu_gc_by_index_quick(vector<vector<pair<double,ui>>>& residual_sim_nei, vector<vector<ui>>& z_list, vector<vector<pair<double,ui>>>& z_R)
{
    if(n == 0) {
        res.clear();
        return 0;
    }

    double t_compute_approximate_degree = 0;
    double t_structural_clique = 0;
    double t_structural_expansion = 0;
    double t_false_twin_grouping = 0;
    double t_multi_seed = 0;
    double t_two_seed = 0;
    double t_drop_one = 0;

    Timer t;
    Timer Total_t;


    ui lookahead = 4;

    ui branch_seed_num = 8;
    ui second_vertex_num = 3;

    ui drop_one_try_num = 5;


    t.restart();
    vector<eid> approximate_degree;

    compute_approximate_gc_degree(residual_sim_nei, z_list, z_R, approximate_degree);

    HeuGCWorkspace workspace(n);

    t_compute_approximate_degree += (double)t.elapsed() / CLOCKS_PER_SEC;


    t.restart();
    vector<ui> structural_clique = find_a_structural_clique();
    t_structural_clique += (double)t.elapsed() / CLOCKS_PER_SEC;

    cout << "structural clique size: " << structural_clique.size() << endl;


    t.restart();
    vector<ui> best_clique = greedy_expand_gc(structural_clique,
                                              approximate_degree,
                                              lookahead,
                                              residual_sim_nei,
                                              z_list,
                                              z_R,
                                              workspace);
    t_structural_expansion += (double)t.elapsed() / CLOCKS_PER_SEC;
    cout << "expanded structural clique size: "
         << best_clique.size() << endl;

#ifdef _FalseTwinHeu_


    t.restart();
    {
        struct TwinItem {
            unsigned long long hash_value;
            ui degree_value;
            ui vertex;
        };

        auto mix_hash = [](unsigned long long x) {
            x += 0x9e3779b97f4a7c15ULL;
            x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
            x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
            return x ^ (x >> 31);
        };

        auto neighborhood_hash = [&](ui u) {
            unsigned long long h =
                mix_hash((unsigned long long)degree[u]);

            for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
                h ^= mix_hash(
                    (unsigned long long)edges[i] +
                    0x9e3779b97f4a7c15ULL
                );

                h = (h << 27) | (h >> 37);
                h = h * 5ULL + 0x52dce729ULL;
            }

            return mix_hash(h);
        };

        auto same_neighborhood = [&](ui u, ui v) {
            if(degree[u] != degree[v]) return false;

            ui i = pstart[u];
            ui j = pstart[v];

            while(i < pstart[u+1]) {
                if(edges[i] != edges[j]) return false;
                ++i;
                ++j;
            }

            return true;
        };

        vector<TwinItem> twin_items;
        twin_items.reserve(n);

        for(ui u = 0; u < n; ++u) {


            if(degree[u] < (ui)ComNeiThre) continue;

            TwinItem item;
            item.hash_value = neighborhood_hash(u);
            item.degree_value = degree[u];
            item.vertex = u;

            twin_items.push_back(item);
        }

        sort(
            twin_items.begin(),
            twin_items.end(),
            [](const TwinItem& a, const TwinItem& b) {
                if(a.degree_value != b.degree_value) {
                    return a.degree_value < b.degree_value;
                }

                if(a.hash_value != b.hash_value) {
                    return a.hash_value < b.hash_value;
                }

                return a.vertex < b.vertex;
            }
        );

        vector<ui> false_twin_clique;

        ui left = 0;

        while(left < twin_items.size()) {
            ui right = left + 1;

            while(right < twin_items.size() &&
                  twin_items[right].degree_value ==
                      twin_items[left].degree_value &&
                  twin_items[right].hash_value ==
                      twin_items[left].hash_value) {
                ++right;
            }

            ui group_size = right - left;


            if(group_size > best_clique.size()) {
                ui representative =
                    twin_items[left].vertex;

                bool exactly_equal = true;

                for(ui i = left + 1; i < right; ++i) {
                    if(!same_neighborhood(
                           representative,
                           twin_items[i].vertex)) {
                        exactly_equal = false;
                        break;
                    }
                }

                if(exactly_equal) {
                    false_twin_clique.clear();
                    false_twin_clique.reserve(group_size);

                    for(ui i = left; i < right; ++i) {
                        false_twin_clique.push_back(
                            twin_items[i].vertex
                        );
                    }

                    best_clique = false_twin_clique;

                    cout << "false-twin GC improvement, new size: "
                         << best_clique.size() << endl;
                }
            }

            left = right;
        }

        vector<TwinItem>().swap(twin_items);
    }
    t_false_twin_grouping += (double)t.elapsed() / CLOCKS_PER_SEC;
#endif


    double t_final_fast_expansion = 0;

    t.restart();

    {
        ui old_best_size = (ui)best_clique.size();

        if(!best_clique.empty()) {
            ui representative = best_clique[0];


            bool best_is_false_twin = false;

            if(best_clique.size() >= 2) {
                best_is_false_twin = true;

                for(ui i = 1; i < best_clique.size(); ++i) {
                    ui v = best_clique[i];

                    if(degree[v] != degree[representative]) {
                        best_is_false_twin = false;
                        break;
                    }

                    ui p1 = pstart[representative];
                    ui p2 = pstart[v];

                    while(p1 < pstart[representative + 1]) {
                        if(edges[p1] != edges[p2]) {
                            best_is_false_twin = false;
                            break;
                        }

                        ++p1;
                        ++p2;
                    }

                    if(!best_is_false_twin) break;
                }
            }


            vector<char> in_clique(n, 0);

            for(ui i = 0; i < best_clique.size(); ++i) {
                in_clique[best_clique[i]] = 1;
            }


            auto is_generalized_neighbor = [&](ui u, ui v) {


                bool structural_adjacent = false;

                if(degree[u] <= degree[v]) {
                    structural_adjacent =
                        binary_search(edges + pstart[u],
                                      edges + pstart[u + 1],
                                      v);
                }
                else {
                    structural_adjacent =
                        binary_search(edges + pstart[v],
                                      edges + pstart[v + 1],
                                      u);
                }

                if(structural_adjacent) return true;


                ui du = degree[u];
                ui dv = degree[v];

                if(du == 0 || dv == 0) return false;

                ui min_degree = du < dv ? du : dv;
                ui max_degree = du > dv ? du : dv;

                if(min_degree < (ui)ComNeiThre) return false;

                if((double)min_degree / (double)max_degree < epsi) {
                    return false;
                }


                pair<double,ui> jsp = js(u, v);

                return jsp.first >= epsi;
            };


            vector<ui> representative_neighbors;

            obtain_gc_neighbors_by_index(representative,
                                         residual_sim_nei,
                                         z_list,
                                         z_R,
                                         representative_neighbors,
                                         workspace);

            vector<ui> candidate_pool;
            candidate_pool.reserve(representative_neighbors.size());

            vector<char> in_candidate_pool(n, 0);

            for(ui i = 0; i < representative_neighbors.size(); ++i) {
                ui v = representative_neighbors[i];

                if(v >= n) continue;
                if(in_clique[v] != 0) continue;
                if(in_candidate_pool[v] != 0) continue;

                in_candidate_pool[v] = 1;
                candidate_pool.push_back(v);
            }


            ui expand_candidate_num = 128;
            ui max_new_add_num = 32;

            if(best_is_false_twin && best_clique.size() >= 1000) {
                expand_candidate_num = 1024;
                max_new_add_num = 512;
            }

            vector<ui> expand_candidates =
                obtain_top_vertices_from_list(candidate_pool,
                                              approximate_degree,
                                              expand_candidate_num);

            vector<ui> added_vertices;
            added_vertices.reserve(max_new_add_num);


            for(ui i = 0; i < expand_candidates.size(); ++i) {
                ui candidate = expand_candidates[i];

                if(in_clique[candidate] != 0) continue;

                bool can_add = true;

                if(best_is_false_twin) {


                    if(!is_generalized_neighbor(candidate, representative)) {
                        can_add = false;
                    }

                    if(can_add) {
                        for(ui j = 0; j < added_vertices.size(); ++j) {
                            if(!is_generalized_neighbor(candidate,
                                                        added_vertices[j])) {
                                can_add = false;
                                break;
                            }
                        }
                    }
                }
                else {


                    for(ui j = 0; j < best_clique.size(); ++j) {
                        if(!is_generalized_neighbor(candidate,
                                                    best_clique[j])) {
                            can_add = false;
                            break;
                        }
                    }
                }

                if(can_add) {
                    best_clique.push_back(candidate);
                    in_clique[candidate] = 1;
                    added_vertices.push_back(candidate);

                    if(added_vertices.size() >= max_new_add_num) {
                        break;
                    }
                }
            }

            if(best_clique.size() > old_best_size) {
                cout << "final fast expansion improvement, added: "
                     << best_clique.size() - old_best_size
                     << ", new size: "
                     << best_clique.size() << endl;
            }
            else {
                cout << "final fast expansion no improvement" << endl;
            }
        }
    }

    t_final_fast_expansion += (double)t.elapsed() / CLOCKS_PER_SEC;


    double t_final_quality_expansion = 0;

    t.restart();

    {
        ui old_best_size = (ui)best_clique.size();

        if(!best_clique.empty()) {
            ui representative = best_clique[0];


            bool best_is_false_twin = false;

            if(best_clique.size() >= 2) {
                best_is_false_twin = true;

                for(ui i = 1; i < best_clique.size(); ++i) {
                    ui v = best_clique[i];

                    if(degree[v] != degree[representative]) {
                        best_is_false_twin = false;
                        break;
                    }

                    ui p1 = pstart[representative];
                    ui p2 = pstart[v];

                    while(p1 < pstart[representative + 1]) {
                        if(edges[p1] != edges[p2]) {
                            best_is_false_twin = false;
                            break;
                        }

                        ++p1;
                        ++p2;
                    }

                    if(!best_is_false_twin) break;
                }
            }


            vector<char> in_clique(n, 0);

            for(ui i = 0; i < best_clique.size(); ++i) {
                in_clique[best_clique[i]] = 1;
            }


            auto is_generalized_neighbor = [&](ui u, ui v) {
                bool structural_adjacent = false;

                if(degree[u] <= degree[v]) {
                    structural_adjacent =
                        binary_search(edges + pstart[u],
                                      edges + pstart[u + 1],
                                      v);
                }
                else {
                    structural_adjacent =
                        binary_search(edges + pstart[v],
                                      edges + pstart[v + 1],
                                      u);
                }

                if(structural_adjacent) return true;

                ui du = degree[u];
                ui dv = degree[v];

                if(du == 0 || dv == 0) return false;

                ui min_degree = du < dv ? du : dv;
                ui max_degree = du > dv ? du : dv;

                if(min_degree < (ui)ComNeiThre) return false;

                if((double)min_degree / (double)max_degree < epsi) {
                    return false;
                }

                pair<double,ui> jsp = js(u, v);

                return jsp.first >= epsi;
            };


            vector<ui> representative_neighbors;

            obtain_gc_neighbors_by_index(representative,
                                         residual_sim_nei,
                                         z_list,
                                         z_R,
                                         representative_neighbors,
                                         workspace);

            vector<ui> candidate_pool;
            candidate_pool.reserve(representative_neighbors.size());

            vector<char> in_candidate_pool(n, 0);

            for(ui i = 0; i < representative_neighbors.size(); ++i) {
                ui v = representative_neighbors[i];

                if(v >= n) continue;
                if(in_clique[v] != 0) continue;
                if(in_candidate_pool[v] != 0) continue;


                if(approximate_degree[v] + 1 <= (eid)best_clique.size()) {
                    continue;
                }

                in_candidate_pool[v] = 1;
                candidate_pool.push_back(v);
            }


            ui expand_candidate_num = 5000;
            ui max_new_add_num = 3000;
            ui restart_num = 16;
            unsigned long long pair_check_budget = 3000000ULL;

            if(best_is_false_twin && best_clique.size() >= 10000) {
                expand_candidate_num = 10000;
                max_new_add_num = 8000;
                restart_num = 32;
                pair_check_budget = 8000000ULL;
            }

            if(!best_is_false_twin && best_clique.size() > 2000) {
                expand_candidate_num = 512;
                max_new_add_num = 64;
                restart_num = 4;
                pair_check_budget = 500000ULL;
            }

            vector<ui> expand_candidates =
                obtain_top_vertices_from_list(candidate_pool,
                                              approximate_degree,
                                              expand_candidate_num);


            vector<ui> best_added;
            vector<ui> current_added;

            unsigned long long pair_check_cnt = 0;

            if(restart_num > expand_candidates.size()) {
                restart_num = (ui)expand_candidates.size();
            }

            for(ui restart_idx = 0; restart_idx < restart_num; ++restart_idx) {
                if(pair_check_cnt >= pair_check_budget) break;

                current_added.clear();
                current_added.reserve(max_new_add_num);


                ui first_vertex = expand_candidates[restart_idx];

                bool first_ok = true;

                if(!best_is_false_twin) {
                    for(ui j = 0; j < best_clique.size(); ++j) {
                        ++pair_check_cnt;

                        if(pair_check_cnt >= pair_check_budget) {
                            first_ok = false;
                            break;
                        }

                        if(!is_generalized_neighbor(first_vertex,
                                                    best_clique[j])) {
                            first_ok = false;
                            break;
                        }
                    }
                }

                if(first_ok) {
                    current_added.push_back(first_vertex);
                }
                else {
                    continue;
                }


                for(ui i = 0; i < expand_candidates.size(); ++i) {
                    if(pair_check_cnt >= pair_check_budget) break;
                    if(current_added.size() >= max_new_add_num) break;

                    ui candidate = expand_candidates[i];

                    if(candidate == first_vertex) continue;

                    bool can_add = true;

                    if(best_is_false_twin) {


                        for(ui j = 0; j < current_added.size(); ++j) {
                            ++pair_check_cnt;

                            if(pair_check_cnt >= pair_check_budget) {
                                can_add = false;
                                break;
                            }

                            if(!is_generalized_neighbor(candidate,
                                                        current_added[j])) {
                                can_add = false;
                                break;
                            }
                        }
                    }
                    else {


                        for(ui j = 0; j < best_clique.size(); ++j) {
                            ++pair_check_cnt;

                            if(pair_check_cnt >= pair_check_budget) {
                                can_add = false;
                                break;
                            }

                            if(!is_generalized_neighbor(candidate,
                                                        best_clique[j])) {
                                can_add = false;
                                break;
                            }
                        }

                        if(can_add) {
                            for(ui j = 0; j < current_added.size(); ++j) {
                                ++pair_check_cnt;

                                if(pair_check_cnt >= pair_check_budget) {
                                    can_add = false;
                                    break;
                                }

                                if(!is_generalized_neighbor(candidate,
                                                            current_added[j])) {
                                    can_add = false;
                                    break;
                                }
                            }
                        }
                    }

                    if(can_add) {
                        current_added.push_back(candidate);
                    }
                }

                if(current_added.size() > best_added.size()) {
                    best_added = current_added;
                }
            }


            if(!best_added.empty()) {
                for(ui i = 0; i < best_added.size(); ++i) {
                    ui v = best_added[i];

                    if(in_clique[v] == 0) {
                        in_clique[v] = 1;
                        best_clique.push_back(v);
                    }
                }
            }

            if(best_clique.size() > old_best_size) {
                cout << "final quality expansion improvement, added: "
                     << best_clique.size() - old_best_size
                     << ", new size: "
                     << best_clique.size()
                     << ", pair checks: "
                     << pair_check_cnt << endl;
            }
            else {
                cout << "final quality expansion no improvement, pair checks: "
                     << pair_check_cnt << endl;
            }
        }
    }

    t_final_quality_expansion += (double)t.elapsed() / CLOCKS_PER_SEC;


    res.clear();
    res.push_back(best_clique);

    double total_time = (double)Total_t.elapsed()/CLOCKS_PER_SEC;

    cout << fixed << setprecision(2);

    cout << "\tHeu Time: "<<total_time<<"s"<<endl;
    cout << "\tt_compute_approximate_degree = " << t_compute_approximate_degree << " s,  " <<(double)t_compute_approximate_degree/total_time*100<<" %"<< endl;
    cout << "\tt_structural_clique          = " << t_structural_clique << " s,  " <<(double)t_structural_clique/total_time*100<<" %"<< endl;
    cout << "\tt_structural_expansion       = " << t_structural_expansion << " s,  " <<(double)t_structural_expansion/total_time*100<<" %"<< endl;
    cout << "\tt_false_twin_grouping        = " << t_false_twin_grouping << " s,  " <<(double)t_false_twin_grouping/total_time*100<<" %"<< endl;
    cout << "\tt_multi_seed                 = " << t_multi_seed << " s,  " <<(double)t_multi_seed/total_time*100<<" %"<< endl;
    cout << "\tt_two_seed                   = " << t_two_seed << " s,  " <<(double)t_two_seed/total_time*100<<" %"<< endl;
    cout << "\tt_drop_one                   = " << t_drop_one << " s,  " <<(double)t_drop_one/total_time*100<<" %"<< endl;
    cout << "\tt_final_fast_expansion       = " << t_final_fast_expansion << " s,  " <<(double)t_final_fast_expansion/total_time*100<<" %"<< endl;
    cout << "\tt_final_quality_expansion    = " << t_final_quality_expansion << " s,  " <<(double)t_final_quality_expansion/total_time*100<<" %"<< endl;

#ifdef _CheckInfo_
    cout << "heuristic GC size: " << best_clique.size() << endl;
    cout << "members: ";

    for(ui u : best_clique) {
        cout << u << ",";
    }

    cout << endl;
#endif

    return (int)best_clique.size();
}

int find_a_heu_gc_by_index(vector<vector<pair<double,ui>>>& residual_sim_nei,
                           vector<vector<ui>>& z_list,
                           vector<vector<pair<double,ui>>>& z_R)
{
    if(n == 0) {
        res.clear();
        return 0;
    }

    double t_compute_approximate_degree = 0;
    double t_structural_clique = 0;
    double t_structural_expansion = 0;
    double t_false_twin_grouping = 0;
    double t_multi_seed = 0;
    double t_two_seed = 0;
    double t_drop_one = 0;

    Timer t;
    Timer Total_t;


    ui lookahead = 4;

    ui branch_seed_num = 8;
    ui second_vertex_num = 3;

    ui drop_one_try_num = 5;


    t.restart();
    vector<eid> approximate_degree;

    compute_approximate_gc_degree(residual_sim_nei, z_list, z_R, approximate_degree);

    HeuGCWorkspace workspace(n);

    t_compute_approximate_degree += (double)t.elapsed() / CLOCKS_PER_SEC;


    t.restart();
    vector<ui> structural_clique = find_a_structural_clique();
    t_structural_clique += (double)t.elapsed() / CLOCKS_PER_SEC;

    cout << "structural clique size: " << structural_clique.size() << endl;


    t.restart();
    vector<ui> best_clique = greedy_expand_gc(structural_clique,
                                              approximate_degree,
                                              lookahead,
                                              residual_sim_nei,
                                              z_list,
                                              z_R,
                                              workspace);
    t_structural_expansion += (double)t.elapsed() / CLOCKS_PER_SEC;
    cout << "expanded structural clique size: "
         << best_clique.size() << endl;

#ifdef _FalseTwinHeu_


    t.restart();
    {
        struct TwinItem {
            unsigned long long hash_value;
            ui degree_value;
            ui vertex;
        };

        auto mix_hash = [](unsigned long long x) {
            x += 0x9e3779b97f4a7c15ULL;
            x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
            x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
            return x ^ (x >> 31);
        };

        auto neighborhood_hash = [&](ui u) {
            unsigned long long h =
                mix_hash((unsigned long long)degree[u]);

            for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
                h ^= mix_hash(
                    (unsigned long long)edges[i] +
                    0x9e3779b97f4a7c15ULL
                );

                h = (h << 27) | (h >> 37);
                h = h * 5ULL + 0x52dce729ULL;
            }

            return mix_hash(h);
        };

        auto same_neighborhood = [&](ui u, ui v) {
            if(degree[u] != degree[v]) return false;

            ui i = pstart[u];
            ui j = pstart[v];

            while(i < pstart[u+1]) {
                if(edges[i] != edges[j]) return false;
                ++i;
                ++j;
            }

            return true;
        };

        vector<TwinItem> twin_items;
        twin_items.reserve(n);

        for(ui u = 0; u < n; ++u) {


            if(degree[u] < (ui)ComNeiThre) continue;

            TwinItem item;
            item.hash_value = neighborhood_hash(u);
            item.degree_value = degree[u];
            item.vertex = u;

            twin_items.push_back(item);
        }

        sort(
            twin_items.begin(),
            twin_items.end(),
            [](const TwinItem& a, const TwinItem& b) {
                if(a.degree_value != b.degree_value) {
                    return a.degree_value < b.degree_value;
                }

                if(a.hash_value != b.hash_value) {
                    return a.hash_value < b.hash_value;
                }

                return a.vertex < b.vertex;
            }
        );

        vector<ui> false_twin_clique;

        ui left = 0;

        while(left < twin_items.size()) {
            ui right = left + 1;

            while(right < twin_items.size() &&
                  twin_items[right].degree_value ==
                      twin_items[left].degree_value &&
                  twin_items[right].hash_value ==
                      twin_items[left].hash_value) {
                ++right;
            }

            ui group_size = right - left;


            if(group_size > best_clique.size()) {
                ui representative =
                    twin_items[left].vertex;

                bool exactly_equal = true;

                for(ui i = left + 1; i < right; ++i) {
                    if(!same_neighborhood(
                           representative,
                           twin_items[i].vertex)) {
                        exactly_equal = false;
                        break;
                    }
                }

                if(exactly_equal) {
                    false_twin_clique.clear();
                    false_twin_clique.reserve(group_size);

                    for(ui i = left; i < right; ++i) {
                        false_twin_clique.push_back(
                            twin_items[i].vertex
                        );
                    }

                    best_clique = false_twin_clique;

                    cout << "false-twin GC improvement, new size: "
                         << best_clique.size() << endl;
                }
            }

            left = right;
        }

        vector<TwinItem>().swap(twin_items);
    }
    t_false_twin_grouping += (double)t.elapsed() / CLOCKS_PER_SEC;
#endif


    t.restart();

    vector<ui> seeds = obtain_top_seed_vertices(approximate_degree, seed_num);

    for(ui seed : seeds) {
        vector<ui> initial_clique;
        initial_clique.push_back(seed);

        vector<ui> current_clique = greedy_expand_gc(initial_clique,
                                                     approximate_degree,
                                                     lookahead,
                                                     residual_sim_nei,
                                                     z_list,
                                                     z_R,
                                                     workspace);

        if(current_clique.size() > best_clique.size()) {
            best_clique.swap(current_clique);

            cout << "multi-seed improvement, seed: "
                 << seed << ", new size: "
                 << best_clique.size() << endl;
        }
    }
    t_multi_seed += (double)t.elapsed() / CLOCKS_PER_SEC;


    t.restart();
    branch_seed_num = min(branch_seed_num, (ui)seeds.size());

    for(ui i = 0; i < branch_seed_num; ++i) {
        ui seed = seeds[i];

        vector<ui> seed_neighbors;

        obtain_gc_neighbors_by_index(seed,
                                     residual_sim_nei,
                                     z_list,
                                     z_R,
                                     seed_neighbors,
                                     workspace);

        vector<ui> second_vertices = obtain_top_vertices_from_list(seed_neighbors,
                                                                  approximate_degree,
                                                                  second_vertex_num);

        for(ui second : second_vertices) {
            vector<ui> initial_clique;

            initial_clique.push_back(seed);
            initial_clique.push_back(second);

            vector<ui> current_clique = greedy_expand_gc(initial_clique,
                                                         approximate_degree,
                                                         lookahead,
                                                         residual_sim_nei,
                                                         z_list,
                                                         z_R,
                                                         workspace);

            if(current_clique.size() > best_clique.size()) {
                best_clique.swap(current_clique);

                cout << "two-seed improvement, seed pair: "
                     << seed << ", " << second
                     << ", new size: "
                     << best_clique.size() << endl;
            }
        }
    }
    t_two_seed += (double)t.elapsed() / CLOCKS_PER_SEC;


    t.restart();
    improve_gc_by_drop_one(best_clique,
                           approximate_degree,
                           drop_one_try_num,
                           lookahead,
                           residual_sim_nei,
                           z_list,
                           z_R,
                           workspace);

    res.clear();
    res.push_back(best_clique);
    t_drop_one += (double)t.elapsed() / CLOCKS_PER_SEC;

    double total_time = (double)Total_t.elapsed()/CLOCKS_PER_SEC;

    cout << fixed << setprecision(2);

    cout << "\tTime: "<<total_time<<"s"<<endl;
    cout << "\tt_compute_approximate_degree = " << t_compute_approximate_degree << " s,  " <<(double)t_compute_approximate_degree/total_time*100<<" %"<< endl;
    cout << "\tt_structural_clique          = " << t_structural_clique << " s,  " <<(double)t_structural_clique/total_time*100<<" %"<< endl;
    cout << "\tt_structural_expansion       = " << t_structural_expansion << " s,  " <<(double)t_structural_expansion/total_time*100<<" %"<< endl;
    cout << "\tt_false_twin_grouping        = " << t_false_twin_grouping << " s,  " <<(double)t_false_twin_grouping/total_time*100<<" %"<< endl;
    cout << "\tt_multi_seed                 = " << t_multi_seed << " s,  " <<(double)t_multi_seed/total_time*100<<" %"<< endl;
    cout << "\tt_two_seed                   = " << t_two_seed << " s,  " <<(double)t_two_seed/total_time*100<<" %"<< endl;
    cout << "\tt_drop_one                   = " << t_drop_one << " s,  " <<(double)t_drop_one/total_time*100<<" %"<< endl;

#ifdef _CheckInfo_
    cout << "heuristic GC size: " << best_clique.size() << endl;
    cout << "members: ";

    for(ui u : best_clique) {
        cout << u << ",";
    }

    cout << endl;
#endif

    return (int)best_clique.size();
}

int find_a_heu_gc_by_index_fast(vector<vector<pair<double,ui>>>& residual_sim_nei,
                           vector<vector<ui>>& z_list,
                           vector<vector<pair<double,ui>>>& z_R)
{
    if(n == 0) {
        res.clear();
        return 0;
    }

    double t_compute_approximate_degree = 0;
    double t_structural_clique = 0;
    double t_structural_expansion = 0;
    double t_false_twin_grouping = 0;
    double t_false_twin_expansion = 0;
    double t_multi_seed = 0;
    double t_two_seed = 0;
    double t_drop_one = 0;

    Timer t;
    Timer Total_t;

    ui lookahead = 4;
    ui branch_seed_num = 8;
    ui second_vertex_num = 3;
    ui drop_one_try_num = 1;
    ui no_improvement_limit = 8;


    t.restart();

    vector<eid> approximate_degree;
    compute_approximate_gc_degree(residual_sim_nei, z_list, z_R, approximate_degree);

    HeuGCWorkspace workspace(n);

    t_compute_approximate_degree += (double)t.elapsed() / CLOCKS_PER_SEC;


    t.restart();

    vector<ui> structural_clique = find_a_structural_clique();

    t_structural_clique += (double)t.elapsed() / CLOCKS_PER_SEC;

    cout << "structural clique size: " << structural_clique.size() << endl;


    t.restart();

    vector<ui> best_clique = greedy_expand_gc(structural_clique,
                                              approximate_degree,
                                              lookahead,
                                              residual_sim_nei,
                                              z_list,
                                              z_R,
                                              workspace);

    t_structural_expansion += (double)t.elapsed() / CLOCKS_PER_SEC;

    cout << "expanded structural clique size: " << best_clique.size() << endl;

    ui expanded_structural_size = (ui)best_clique.size();


    vector<ui> false_twin_clique;

#ifdef _FalseTwinHeu_


    t.restart();

    {
        struct TwinItem {
            unsigned long long hash_value;
            ui degree_value;
            ui vertex;
        };

        auto mix_hash = [](unsigned long long x) {
            x += 0x9e3779b97f4a7c15ULL;
            x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
            x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
            return x ^ (x >> 31);
        };

        auto neighborhood_hash = [&](ui u) {
            unsigned long long h = mix_hash((unsigned long long)degree[u]);

            for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
                h ^= mix_hash((unsigned long long)edges[i] + 0x9e3779b97f4a7c15ULL);
                h = (h << 27) | (h >> 37);
                h = h * 5ULL + 0x52dce729ULL;
            }

            return mix_hash(h);
        };

        auto same_neighborhood = [&](ui u, ui v) {
            if(degree[u] != degree[v]) return false;

            ui i = pstart[u];
            ui j = pstart[v];

            while(i < pstart[u+1]) {
                if(edges[i] != edges[j]) return false;
                ++i;
                ++j;
            }

            return true;
        };

        vector<TwinItem> twin_items;
        twin_items.reserve(n);

        for(ui u = 0; u < n; ++u) {
            if(degree[u] < (ui)ComNeiThre) continue;

            TwinItem item;
            item.hash_value = neighborhood_hash(u);
            item.degree_value = degree[u];
            item.vertex = u;

            twin_items.push_back(item);
        }

        sort(twin_items.begin(), twin_items.end(),
             [](const TwinItem& a, const TwinItem& b) {
                 if(a.degree_value != b.degree_value) {
                     return a.degree_value < b.degree_value;
                 }

                 if(a.hash_value != b.hash_value) {
                     return a.hash_value < b.hash_value;
                 }

                 return a.vertex < b.vertex;
             });

        ui left = 0;

        while(left < twin_items.size()) {
            ui right = left + 1;

            while(right < twin_items.size() &&
                  twin_items[right].degree_value == twin_items[left].degree_value &&
                  twin_items[right].hash_value == twin_items[left].hash_value) {
                ++right;
            }

            ui group_size = right - left;

            if(group_size > best_clique.size()) {
                ui representative = twin_items[left].vertex;
                bool exactly_equal = true;

                for(ui i = left + 1; i < right; ++i) {
                    if(!same_neighborhood(representative, twin_items[i].vertex)) {
                        exactly_equal = false;
                        break;
                    }
                }

                if(exactly_equal) {
                    false_twin_clique.clear();
                    false_twin_clique.reserve(group_size);

                    for(ui i = left; i < right; ++i) {
                        false_twin_clique.push_back(twin_items[i].vertex);
                    }

                    best_clique = false_twin_clique;

                    cout << "false-twin GC improvement, new size: "
                         << best_clique.size() << endl;
                }
            }

            left = right;
        }
    }

    t_false_twin_grouping += (double)t.elapsed() / CLOCKS_PER_SEC;


    t.restart();

    if(!false_twin_clique.empty()) {
        ui representative = false_twin_clique[0];

        vector<ui> initial_clique;
        initial_clique.push_back(representative);

        vector<ui> representative_clique =
            greedy_expand_gc(initial_clique,
                             approximate_degree,
                             lookahead,
                             residual_sim_nei,
                             z_list,
                             z_R,
                             workspace);

        vector<char> selected(n, 0);
        vector<ui> merged_clique;

        merged_clique.reserve(false_twin_clique.size() +
                              representative_clique.size());

        for(ui i = 0; i < false_twin_clique.size(); ++i) {
            ui v = false_twin_clique[i];

            if(selected[v] == 0) {
                selected[v] = 1;
                merged_clique.push_back(v);
            }
        }

        for(ui i = 0; i < representative_clique.size(); ++i) {
            ui v = representative_clique[i];

            if(selected[v] == 0) {
                selected[v] = 1;
                merged_clique.push_back(v);
            }
        }

        if(merged_clique.size() > best_clique.size()) {
            best_clique.swap(merged_clique);

            cout << "false-twin representative expansion, new size: "
                 << best_clique.size() << endl;
        }
    }

    t_false_twin_expansion += (double)t.elapsed() / CLOCKS_PER_SEC;

#endif


    bool strong_false_twin = false;

#ifdef _FalseTwinHeu_
    if(false_twin_clique.size() >= 1000) {
        unsigned long long twin_size =
            (unsigned long long)false_twin_clique.size();

        unsigned long long structural_size =
            (unsigned long long)expanded_structural_size;

        if(structural_size == 0 ||
           twin_size >= 4ULL * structural_size) {
            strong_false_twin = true;
        }
    }
#endif

    if(strong_false_twin) {
        cout << "strong false-twin solution found; "
             << "skip multi-seed, two-seed and drop-one" << endl;
    }
    else {


        t.restart();

        vector<ui> seeds =
            obtain_top_seed_vertices(approximate_degree, seed_num);

        ui size_before_multi_seed = (ui)best_clique.size();
        ui no_improvement_cnt = 0;

        for(ui i = 0; i < seeds.size(); ++i) {
            ui seed = seeds[i];


            if(approximate_degree[seed] + 1 <=
               (eid)best_clique.size()) {
                continue;
            }

            vector<ui> initial_clique;
            initial_clique.push_back(seed);

            vector<ui> current_clique =
                greedy_expand_gc(initial_clique,
                                 approximate_degree,
                                 lookahead,
                                 residual_sim_nei,
                                 z_list,
                                 z_R,
                                 workspace);

            if(current_clique.size() > best_clique.size()) {
                best_clique.swap(current_clique);
                no_improvement_cnt = 0;

                cout << "multi-seed improvement, seed: "
                     << seed << ", new size: "
                     << best_clique.size() << endl;
            }
            else {
                ++no_improvement_cnt;
            }

            if(no_improvement_cnt >= no_improvement_limit) {
                cout << "multi-seed early stop after "
                     << no_improvement_cnt
                     << " consecutive failures" << endl;
                break;
            }
        }

        t_multi_seed += (double)t.elapsed() / CLOCKS_PER_SEC;

        bool multi_seed_improved =
            best_clique.size() > size_before_multi_seed;


        t.restart();

        if(multi_seed_improved) {
            branch_seed_num =
                min(branch_seed_num, (ui)seeds.size());

            for(ui i = 0; i < branch_seed_num; ++i) {
                ui seed = seeds[i];

                if(approximate_degree[seed] + 1 <=
                   (eid)best_clique.size()) {
                    continue;
                }

                vector<ui> seed_neighbors;

                obtain_gc_neighbors_by_index(seed,
                                             residual_sim_nei,
                                             z_list,
                                             z_R,
                                             seed_neighbors,
                                             workspace);

                vector<ui> second_vertices =
                    obtain_top_vertices_from_list(seed_neighbors,
                                                  approximate_degree,
                                                  second_vertex_num);

                for(ui j = 0; j < second_vertices.size(); ++j) {
                    ui second = second_vertices[j];

                    vector<ui> initial_clique;
                    initial_clique.push_back(seed);
                    initial_clique.push_back(second);

                    vector<ui> current_clique =
                        greedy_expand_gc(initial_clique,
                                         approximate_degree,
                                         lookahead,
                                         residual_sim_nei,
                                         z_list,
                                         z_R,
                                         workspace);

                    if(current_clique.size() > best_clique.size()) {
                        best_clique.swap(current_clique);

                        cout << "two-seed improvement, seed pair: "
                             << seed << ", " << second
                             << ", new size: "
                             << best_clique.size() << endl;
                    }
                }
            }
        }
        else {
            cout << "multi-seed has no improvement; skip two-seed" << endl;
        }

        t_two_seed += (double)t.elapsed() / CLOCKS_PER_SEC;


        t.restart();

        bool run_drop_one = false;

        if(best_clique.size() < 5000) {
            run_drop_one = true;
        }

        if(multi_seed_improved) {
            run_drop_one = true;
        }

        if(run_drop_one && !best_clique.empty()) {
            improve_gc_by_drop_one(best_clique,
                                   approximate_degree,
                                   drop_one_try_num,
                                   lookahead,
                                   residual_sim_nei,
                                   z_list,
                                   z_R,
                                   workspace);
        }
        else {
            cout << "skip drop-one heuristic" << endl;
        }

        t_drop_one += (double)t.elapsed() / CLOCKS_PER_SEC;
    }

    res.clear();
    res.push_back(best_clique);

    double total_time =
        (double)Total_t.elapsed() / CLOCKS_PER_SEC;

    cout << fixed << setprecision(2);

    cout << "\tTime: " << total_time << "s" << endl;

    cout << "\tt_compute_approximate_degree = "
         << t_compute_approximate_degree << " s,  "
         << t_compute_approximate_degree / total_time * 100
         << " %" << endl;

    cout << "\tt_structural_clique          = "
         << t_structural_clique << " s,  "
         << t_structural_clique / total_time * 100
         << " %" << endl;

    cout << "\tt_structural_expansion       = "
         << t_structural_expansion << " s,  "
         << t_structural_expansion / total_time * 100
         << " %" << endl;

    cout << "\tt_false_twin_grouping        = "
         << t_false_twin_grouping << " s,  "
         << t_false_twin_grouping / total_time * 100
         << " %" << endl;

    cout << "\tt_false_twin_expansion       = "
         << t_false_twin_expansion << " s,  "
         << t_false_twin_expansion / total_time * 100
         << " %" << endl;

    cout << "\tt_multi_seed                 = "
         << t_multi_seed << " s,  "
         << t_multi_seed / total_time * 100
         << " %" << endl;

    cout << "\tt_two_seed                   = "
         << t_two_seed << " s,  "
         << t_two_seed / total_time * 100
         << " %" << endl;

    cout << "\tt_drop_one                   = "
         << t_drop_one << " s,  "
         << t_drop_one / total_time * 100
         << " %" << endl;

#ifdef _CheckInfo_
    cout << "heuristic GC size: " << best_clique.size() << endl;
    cout << "members: ";

    for(ui i = 0; i < best_clique.size(); ++i) {
        cout << best_clique[i] << ",";
    }

    cout << endl;
#endif

    return (int)best_clique.size();
}
