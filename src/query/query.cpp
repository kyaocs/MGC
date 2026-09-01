

#include "Timer.h"
#include "Utility.h"
#include "LinearHeap.h"
#include "Heu.h"

void read_graph_binary(string dir, string name) {
    FILE *f = Utility::open_file((dir + "/" + name + "/b_degree.bin").c_str(), "rb");

    ui tt;
    fread(&tt, sizeof(ui), 1, f);
    if(tt != sizeof(ui)) {
        printf("sizeof ui is different: edge.bin(%d), machine(%d)\n", tt, (ui)sizeof(ui));
        return ;
    }
    fread(&n, sizeof(ui), 1, f);
    fread(&m, sizeof(ui), 1, f);
    if(degree == nullptr) degree = new ui[n];
    fread(degree, sizeof(ui), n, f);
    fclose(f);

    f = Utility::open_file((dir + "/" + name + "/b_adj.bin").c_str(), "rb");

    if(pstart == nullptr) pstart = new ui[n+1];
    if(edges == nullptr) edges = new ui[m];

    pstart[0] = 0;
    for(ui i = 0;i < n;i ++) {
        if(degree[i] > 0) fread(edges+pstart[i], sizeof(ui), degree[i], f);
        else exit(1);
        pstart[i+1] = pstart[i] + degree[i];
    }
    fclose(f);

    oid_mapping = new ui[n];
    for(ui i = 0; i < n; ++i) oid_mapping[i] = i;

    newid_mapping = new ui[n];
    for(ui i = 0; i < n; ++i) newid_mapping[i] = i;

#ifdef _CostlyDebug_

    for(ui i = 0; i < n; ++i) {
        vector<ui> tmpvec;
        for(ui j = pstart[i]; j < pstart[i+1]; ++j) {
            tmpvec.push_back(edges[j]);
        }
        for(int j = 0; j < tmpvec.size() - 1 ; ++j) {
            assert(tmpvec[j] < tmpvec[j+1]);
        }
    }
#endif

#ifdef _CheckInfo_
    cout<<"original graph information:"<<endl;
    for(ui i = 0; i < n; ++i) {
        cout<<"vertex "<<i<<" (deg="<<degree[i]<<"), its neighbors: ";
        for(ui j = pstart[i]; j < pstart[i+1]; ++j) {
            cout<<edges[j]<<",";
        }cout<<endl;
    }
#endif
}

vector<ui> gc_color;
vector<ui> gc_color_seen;

ui gc_color_num = 0;
ui gc_color_token = 0;
ui coloring_before_bnb(const vector<ui>& R, ui md)
{
    gc_color.assign(md, 0);
    gc_color_num = 0;
    gc_color_token = 0;

    if(R.empty()) {
        gc_color_seen.clear();
        return 0;
    }


    vector<pair<ui,ui>> degree_vertex;
    degree_vertex.reserve(R.size());

    for(ui v : R) {
        ui d = 0;

        for(ui w : R) {
            if(v != w && Matrix[trs[v]][trs[w]] != 0) {
                ++d;
            }
        }

        degree_vertex.push_back(make_pair(d, v));
    }

    sort(degree_vertex.begin(), degree_vertex.end(),
         [](const pair<ui,ui>& a, const pair<ui,ui>& b) {
             if(a.first != b.first) {
                 return a.first > b.first;
             }

             return a.second < b.second;
         });


    vector<ui> forbidden(R.size() + 1, 0);
    ui stamp = 0;

    for(const auto& item : degree_vertex) {
        ui v = item.second;

        ++stamp;


        for(ui w : R) {
            ui color_w = gc_color[trs[w]];

            if(color_w == 0) continue;

            if(Matrix[trs[v]][trs[w]] != 0) {
                forbidden[color_w] = stamp;
            }
        }


        ui color_v = 1;

        while(color_v <= gc_color_num &&
              forbidden[color_v] == stamp) {
            ++color_v;
        }


        if(color_v > gc_color_num) {
            ++gc_color_num;
            assert(color_v == gc_color_num);
        }

        gc_color[trs[v]] = color_v;
    }


    gc_color_seen.assign(gc_color_num + 1, 0);

#ifdef _CostlyDebug_


    for(ui i = 0; i < R.size(); ++i) {
        ui u = R[i];

        assert(trs[u] < gc_color.size());
        assert(gc_color[trs[u]] >= 1);
        assert(gc_color[trs[u]] <= gc_color_num);

        for(ui j = i + 1; j < R.size(); ++j) {
            ui v = R[j];

            if(gc_color[trs[u]] == gc_color[trs[v]]) {
                assert(Matrix[trs[u]][trs[v]] == 0);
                assert(Matrix[trs[v]][trs[u]] == 0);
            }
        }
    }
#endif

    return gc_color_num;
}


void degree_based_vertex_reduce_and_rebuild_graph(ui *peels, char *vis, ui *core, ui *rid, int threshold)
{
    Timer tt;

    ui queue_n = 0, new_size = 0;
    for(ui i = 0;i < n;i ++) if(degree[i] < threshold) peels[queue_n ++] = i;
    for(ui i = 0;i < queue_n;i ++) {
        ui u = peels[i]; degree[u] = 0;
        for(ui j = pstart[u];j < pstart[u+1];j ++) if(degree[edges[j]] > 0) {
            if((degree[edges[j]] --) == threshold) peels[queue_n ++] = edges[j];
        }
    }
    if(queue_n == n) {
        cout<<"reduced graph is empty"<<endl;
        n=0; m=0; return;
    }
    memset(vis, 0, sizeof(char)*n);

    for(ui i = 0;i < n;i ++) {
        if(degree[i] >= threshold) peels[queue_n + (new_size ++)] = i;
        else {
            vis[i] = 1;
            core[i] = 0;
        }
    }
    assert(queue_n + new_size == n);
    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    heap->init(new_size, new_size-1, peels+queue_n, degree);
    ui max_core = 0;
    for(ui i = 0;i < new_size;i ++) {
        ui u, key;
        heap->pop_min(u, key);
        if(key > max_core) max_core = key;
        core[u] = max_core;
        peels[queue_n + i] = u;
        vis[u] = 1;
        for(ui j = pstart[u];j < pstart[u+1];j ++) if(vis[edges[j]] == 0) {
            heap->decrement(edges[j], 1);
        }
    }
    delete heap;


    ui cnt = 0;
    for(ui i = 0; i < n; ++i) if(core[i]>=threshold) {
        rid[i] = cnt;
        oid_mapping[cnt] = oid_mapping[i];
        ++ cnt;
    }
    assert(cnt==new_size);
    cnt = 0;
    ui pos = 0;
    for(ui i = 0;i < n;i ++) if(core[i]>=threshold) {
        ui t_start = pstart[i];
        pstart[cnt] = pos;
        for(ui j = t_start;j < pstart[i+1];j ++) if(core[edges[j]]>=threshold) {
            edges[pos] = rid[edges[j]];
            f_edges[pos] = f_edges[j];
            ++ pos;
        }
        ++ cnt;
    }
    pstart[cnt] = pos;
    assert(cnt==new_size);
    n = cnt;
    m = pos;
    cout<<"vr: (n="<<n<<", m="<<m<<")"<<endl;


    for(ui i = 0; i < n; ++i) {
        peels[i] = rid[peels[queue_n+i]];
        assert(oid_mapping[i] >= i);
        core[i] = core[oid_mapping[i]];
    }

    for(ui i = 0; i < n; ++i) rid[peels[i]] = i;

#ifdef _CostlyDebug_
    for(ui u = 0; u < n; ++u) {
        assert(core[u] >= threshold);
        for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
            ui v = edges[i];
            if(rid[v] > rid[u]) assert(core[v] >= core[u]);
            else {
                assert(rid[v] < rid[u] && core[v] <= core[u]);
            }
        }
    }
#endif

#ifdef _CheckInfo_
    cout<<"after reassign vid, the graph information:"<<endl;
    for(ui u = 0; u < n; ++u) {
        cout<<"vertex "<<oid_mapping[u]<<", its neighbors :";
        for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
            if(f_edges[i]==0)cout<<oid_mapping[edges[i]]<<"(o), ";
            else {
                assert(f_edges[i]==1);
                cout<<oid_mapping[edges[i]]<<"(s), ";
            }
        }cout<<endl;
    }
    for(ui i = 0; i < n; ++i) cout<<"vertex "<<oid_mapping[i]<<" -> "<<i<<endl;
    cout<<"peels[], core[], and rid[] information:"<<endl;
    cout<<"peels[]:"; for(ui u = 0; u < n; ++u) cout<<peels[u]<<","; cout<<endl;
    cout<<"core[] :"; for(ui u = 0; u < n; ++u) cout<<core[u]<<","; cout<<endl;
    cout<<"rid[]  :"; for(ui u = 0; u < n; ++u) cout<<rid[u]<<","; cout<<endl;
#endif
}

void compute_degeneracy_ordering_of_original_graph(ui *peels, ui *vis, ui *core, ui *rid )
{
    memset(vis, 0, sizeof(char)*n);
    for(ui i = 0; i < n; ++i) peels[i] = i;
    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    heap->init(n, n-1, peels, degree);
    ui max_core = 0;
    for(ui i = 0;i < n;i ++) {
        ui u, key;
        heap->pop_min(u, key);
        if(key > max_core) max_core = key;
        core[u] = max_core;
        peels[i] = u;
        vis[u] = 1;
        for(ui j = pstart[u];j < pstart[u+1];j ++) if(vis[edges[j]] == 0) {
            heap->decrement(edges[j], 1);
        }
    }
    for(ui i = 0; i < n; ++i) {
        rid[peels[i]] = i;
    }
    delete heap;
#ifdef _CheckInfo_
    cout<<"peels: "; for(ui i = 0; i < n; ++i) cout<<peels[i]<<","; cout<<endl;
#endif
}

void compute_degeneracy_ordering_of_tmp_graph(ui *peels, ui *vis, ui *core, ui *rid, ui* tmp_pstart, ui* tmp_edges, ui* tmp_degree)
{
    memset(vis, 0, sizeof(ui)*n);
    for(ui i = 0; i < n; ++i) peels[i] = i;
    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    heap->init(n, n-1, peels, tmp_degree);
    ui max_core = 0;
    for(ui i = 0;i < n;i ++) {
        ui u, key;
        heap->pop_min(u, key);
        if(key > max_core) max_core = key;
        core[u] = max_core;
        peels[i] = u;
        vis[u] = 1;
        for(ui j = tmp_pstart[u];j < tmp_pstart[u+1];j ++) if(vis[tmp_edges[j]] == 0) {
            heap->decrement(tmp_edges[j], 1);
        }
    }
    for(ui i = 0; i < n; ++i) {
        rid[peels[i]] = i;
    }
    delete heap;
#ifdef _CheckInfo_
    cout<<"peels: "; for(ui i = 0; i < n; ++i) cout<<peels[i]<<","; cout<<endl;
#endif
}

void compute_degeneracy_ordering_of_tmp_graph(
    ui* peels,
    ui* vis,
    ui* core,
    ui* rid,
    ui* tmp_pstart,
    ui* tmp_edges,
    ui* tmp_degree,
    vector<vector<pair<double,ui>>>& residual_sim_nei,
    vector<vector<ui>>& z_list,
    vector<vector<pair<double,ui>>>& z_R,
    ui* del)
{


    memset(vis, 0, sizeof(ui) * n);

    const ui original_n = (ui)residual_sim_nei.size();

    vector<ui> upper_degree(n, 0);


    vector<ui> candidate_mark(original_n, 0);
    ui token = 0;

    for(ui u = 0; u < n; ++u) {
        ++token;

        if(token == 0) {
            fill(candidate_mark.begin(),
                 candidate_mark.end(), 0);
            token = 1;
        }

        ui original_u = oid_mapping[u];
        ui degree_ub = 0;

        candidate_mark[original_u] = token;


        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];
            ui original_v = oid_mapping[v];
            if(candidate_mark[original_v] != token) {
                candidate_mark[original_v] = token;
                ++degree_ub;
            }
        }


        for(const auto& simnei :
            residual_sim_nei[original_u]) {
            double score = simnei.first;
            ui original_v = simnei.second;
            if(score < epsi) break;
            if(original_v == original_u) continue;
            if(del[original_v] != 0) continue;
            if(candidate_mark[original_v] != token) {
                candidate_mark[original_v] = token;
                ++degree_ub;
            }
        }


        for(ui z : z_list[original_u]) {
            assert(z < z_R.size());

            for(const auto& nei : z_R[z]) {
                double upper_score = nei.first;
                ui original_v = nei.second;

                if(upper_score < epsi) break;

                if(original_v == original_u) continue;
                if(del[original_v] != 0) continue;


                if(candidate_mark[original_v] == token) {
                    continue;
                }


                candidate_mark[original_v] = token;

                ui du = degree[original_u];
                ui dv = degree[original_v];

                if(du == 0 || dv == 0) continue;

                ui min_degree = min(du, dv);
                ui max_degree = max(du, dv);


                if(min_degree < (ui)ComNeiThre) {
                    continue;
                }


                if((double)min_degree /
                   (double)max_degree < epsi) {
                    continue;
                }

                ++degree_ub;
            }
        }

        assert(degree_ub < n);

        upper_degree[u] = degree_ub;


        core[u] = degree_ub;
        peels[u] = u;
    }


    sort(peels, peels + n,
         [&](ui u, ui v) {
             if(upper_degree[u] != upper_degree[v]) {
                 return upper_degree[u] <
                        upper_degree[v];
             }

             if(tmp_degree[u] != tmp_degree[v]) {
                 return tmp_degree[u] <
                        tmp_degree[v];
             }

             return oid_mapping[u] <
                    oid_mapping[v];
         });

    for(ui i = 0; i < n; ++i) {
        rid[peels[i]] = i;
    }

#ifdef _CheckInfo_
    cout << "upper-degree ordering:" << endl;

    for(ui i = 0; i < n; ++i) {
        ui u = peels[i];

        cout << "(" << u
             << "," << upper_degree[u]
             << "),";
    }

    cout << endl;
#endif
}


void materialize_graph_query(ui query_point)
{
    Timer tt;
    tt_mat = 0;

    assert(query_point < n);


    ui * in_subgraph = new ui[n];
    memset(in_subgraph, 0, sizeof(ui) * n);

    vector<ui> sub_vertices;
    sub_vertices.reserve(degree[query_point] * 10 + 1);


    in_subgraph[query_point] = 1;
    sub_vertices.push_back(query_point);


    for(ui i = pstart[query_point]; i < pstart[query_point + 1]; ++i) {
        ui v = edges[i];

        if(in_subgraph[v] == 0) {
            in_subgraph[v] = 1;
            sub_vertices.push_back(v);
        }
    }


    for(ui i = pstart[query_point]; i < pstart[query_point + 1]; ++i) {
        ui u = edges[i];

        for(ui j = pstart[u]; j < pstart[u + 1]; ++j) {
            ui v = edges[j];

            if(in_subgraph[v] == 0) {
                in_subgraph[v] = 1;
                sub_vertices.push_back(v);
            }
        }
    }

    cout << "query_point: " << query_point << endl;
    cout << "query_subgraph_vertices: "
         << Utility::integer_to_string(sub_vertices.size()) << endl;


    ui * vis = new ui[n];
    memset(vis, 0, sizeof(ui) * n);

    ui * comnei_cnt = new ui[n];
    memset(comnei_cnt, 0, sizeof(ui) * n);

    vector<vector<ui>> ver_sim_neis(n);

    long long similar_edges_cnt = 0;

    for(auto u : sub_vertices) {

        vector<ui> u_nei;


        for(ui i = pstart[u]; i < pstart[u + 1]; ++i) {
            ui v = edges[i];

            u_nei.push_back(v);
            vis[v] = 1;
        }

        vector<ui> u_2hopnei;


        for(auto e : u_nei) {

            for(ui i = pstart[e]; i < pstart[e + 1]; ++i) {

                ui v = edges[i];


                if(in_subgraph[v] == 0)
                    continue;


                if(vis[v] == 1 || v == u)
                    continue;

                if(vis[v] == 0) {
                    u_2hopnei.push_back(v);
                    vis[v] = 2;
                }

                ++comnei_cnt[v];
            }
        }


        for(auto v : u_2hopnei) {

            double sim_score =
                (double)comnei_cnt[v] /
                (degree[v] + degree[u] - comnei_cnt[v]);

            if(sim_score >= epsi &&
               comnei_cnt[v] >= ComNeiThre) {

                ver_sim_neis[u].push_back(v);
            }

#ifdef _CheckInfo_
            cout << "common neighbors information:" << endl;
            cout << u << ", " << v
                 << ", comnei_cnt=" << comnei_cnt[v]
                 << ", sim_score=" << sim_score
                 << endl;
#endif
        }

        similar_edges_cnt += ver_sim_neis[u].size();


        for(auto v : u_nei) {
            assert(vis[v] == 1);
            vis[v] = 0;
        }

        for(auto v : u_2hopnei) {
            comnei_cnt[v] = 0;

            assert(vis[v] == 2);
            vis[v] = 0;
        }

#ifdef _CostlyDebug_
        for(ui i = 0; i < n; ++i) {
            assert(vis[i] == 0);
            assert(comnei_cnt[i] == 0);
        }
#endif
    }


    delete [] vis;
    delete [] comnei_cnt;


    cout << "query_similar_edges_cnt: "
         << Utility::integer_to_string(similar_edges_cnt)
         << endl;


    long long original_edges_cnt = 0;

    for(auto u : sub_vertices) {

        for(ui i = pstart[u]; i < pstart[u + 1]; ++i) {

            ui v = edges[i];

            if(in_subgraph[v]) {
                ++original_edges_cnt;
            }
        }
    }

    cout << "query_original_edges_cnt: "
         << Utility::integer_to_string(original_edges_cnt)
         << endl;


    long long total_edges_ll =
        original_edges_cnt + similar_edges_cnt;

    ui t_m = (ui)total_edges_ll;

    ui * t_pstart = new ui[n + 1];
    ui * t_edges = new ui[t_m];


    if(f_edges != nullptr) {
        delete [] f_edges;
    }

    f_edges = new char[t_m];
    memset(f_edges, 0, sizeof(char) * t_m);

    ui pos = 0;

    for(ui u = 0; u < n; ++u) {

        t_pstart[u] = pos;


        if(in_subgraph[u] == 0) {
            degree[u] = 0;
            continue;
        }


        for(ui i = pstart[u]; i < pstart[u + 1]; ++i) {

            ui v = edges[i];

            if(in_subgraph[v] == 0)
                continue;

            t_edges[pos] = v;
            f_edges[pos] = 0;

            ++pos;
        }


        for(auto v : ver_sim_neis[u]) {

            assert(in_subgraph[v]);

            t_edges[pos] = v;
            f_edges[pos] = 1;

            ++pos;
        }

        degree[u] = pos - t_pstart[u];
    }

    t_pstart[n] = pos;

    assert(pos == t_m);


    delete [] pstart;
    delete [] edges;

    pstart = t_pstart;
    edges = t_edges;
    m = t_m;


    delete [] in_subgraph;


    cout << "query_materialized_edges: "
         << Utility::integer_to_string(m)
         << endl;

    cout << "mat_time: "
         << (double)tt.elapsed() / CLOCKS_PER_SEC
         << "s"
         << endl << flush;

    tt_mat = tt.elapsed();


#ifdef _CheckInfo_

    cout << "materialized query graph information:" << endl;

    for(ui u = 0; u < n; ++u) {

        if(degree[u] == 0)
            continue;

        cout << "vertex " << u
             << ", (deg=" << degree[u] << "), its neighbors: ";

        for(ui i = pstart[u]; i < pstart[u + 1]; ++i) {

            if(f_edges[i] == 0) {
                cout << edges[i] << "(o), ";
            }
            else {
                assert(f_edges[i] == 1);
                cout << edges[i] << "(s), ";
            }
        }

        cout << endl;
    }

#endif
}

void materialize_graph()
{
    Timer tt;
    tt_mat=0;
    ui * vis = new ui[n];
    memset(vis, 0, sizeof(ui)*n);

    ui * comnei_cnt = new ui[n];
    memset(comnei_cnt, 0, sizeof(ui)*n);

    vector<vector<ui>> ver_sim_neis;
    ver_sim_neis.resize(n);

    long long similar_edges_cnt = 0;
    for(ui u = 0; u < n; ++u) {
        vector<ui> u_nei;
        for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
            u_nei.push_back(edges[i]);
            vis[edges[i]] = 1;
        }

        vector<ui> u_2hopnei;
        for(auto e : u_nei) {
            for(ui i = pstart[e]; i < pstart[e+1]; ++i) {
                ui v = edges[i];
                if(vis[v] == 1 || v == u) continue;
                if(vis[v] == 0) {
                    u_2hopnei.push_back(v);
                    vis[v] = 2;
                }
                ++comnei_cnt[v];
            }
        }
        for(auto e : u_2hopnei) {
            double sim_score = (double) comnei_cnt[e] / (degree[e] + degree[u] - comnei_cnt[e]);
            if(sim_score >= epsi && comnei_cnt[e] >= ComNeiThre) ver_sim_neis[u].push_back(e);
#ifdef _CheckInfo_
            cout<<"common neighbors information:"<<endl;
            cout<<u<<", "<<e<<", comnei_cnt="<<comnei_cnt[e]<<", sim_score="<<sim_score<<endl;
#endif
        }
        similar_edges_cnt += ver_sim_neis[u].size();

        for(auto e : u_nei) {
            assert(vis[e] == 1);
            vis[e] = 0;
        }
        for(auto e : u_2hopnei) {
            comnei_cnt[e] = 0;
            assert(vis[e] == 2);
            vis[e] = 0;
        }
#ifdef _CostlyDebug_
        for(ui i = 0; i < n; ++i) {
            assert(vis[i]==0);
            assert(comnei_cnt[i]==0);
        }
#endif
    }
    delete [] vis;
    delete [] comnei_cnt;

    cout<<"se_cnt: "<<Utility::integer_to_string(similar_edges_cnt)<<endl;

    ui t_m = m + (ui)similar_edges_cnt;
    ui * t_pstart = new ui[n+1];
    ui * t_edges = new ui[t_m];
    if(f_edges == nullptr) f_edges = new char[t_m];
    memset(f_edges, 0, sizeof(char)*t_m);
    ui pos = 0;
    for(ui u = 0; u < n; ++u) {
        t_pstart[u] = pos;
        for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
            t_edges[pos] = edges[i];
            f_edges[pos] = 0;
            ++ pos;
        }
        for(auto e : ver_sim_neis[u]) {
            t_edges[pos] = e;
            f_edges[pos] = 1;
            ++ pos;
        }
        degree[u] = pos - t_pstart[u];
    }
    t_pstart[n] = pos;
    assert(pos==t_m);
    delete [] pstart;
    delete [] edges;
    pstart = t_pstart;
    edges = t_edges;
    m = t_m;
    cout<<"mat_time: "<<(double)tt.elapsed()/CLOCKS_PER_SEC<<"s"<<endl<<flush;
    tt_mat = tt.elapsed();
#ifdef _CheckInfo_
    cout<<"materialized graph information:"<<endl;
    for(ui u = 0; u < n; ++u) {
        cout<<"vertex "<<u<<", (deg="<<degree[u]<<"), its neighbors: ";
        for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
            if(f_edges[i]==0)cout<<edges[i]<<"(o), ";
            else {
                assert(f_edges[i]==1);
                cout<<edges[i]<<"(s), ";
            }
        }cout<<endl;
    }
#endif
}

void bnb_find_max(vector<ui>C,vector<ui>R,vector<ui>X)
{
    ++ ss;
    if(C.size()+R.size()<=max_gc_size) return;
    if(R.empty()) {
        if(X.empty() && C.size() > max_gc_size) {
            max_gc_size = C.size();
#ifdef _CollectRes_
            res.clear();
            vector<ui> tmpC;
            for(auto e : C) tmpC.push_back(oid_mapping[e]);
            res.push_back(tmpC);
#endif
        }
        return;
    }
    vector<ui> branchf, skipR;
    branchf.resize(R.size(),0);
#ifdef _Pivot_

    ui pivot, md = 0;
    for(auto e : R) {
        ui td = 0;
        for(auto u : R) if(Matrix[trs[e]][trs[u]]==1) ++td;
        if(td > md) {
            md = td;
            pivot = e;
        }
    }
    for(auto e : X) {
        ui td = 0;
        for(auto u : R) if(Matrix[trs[e]][trs[u]]==1) ++td;
        if(td > md) {
            md = td;
            pivot = e;
        }
    }
    if(md!=0) {
        for(ui i = 0; i < R.size(); ++i) if(Matrix[trs[R[i]]][trs[pivot]]==1) branchf[i]=1;
    }
#endif

    for(ui i = 0; i < R.size(); ++i) {
        if(branchf[i]==1) {
            skipR.push_back(R[i]);
            continue;
        }
        ui u = R[i];
        C.push_back(u);
        vector<ui> tR;
        for(ui j = i+1; j < R.size(); ++j) if(Matrix[trs[R[j]]][trs[u]]==1) tR.push_back(R[j]);
        for(auto e : skipR) if(Matrix[trs[e]][trs[u]]==1) tR.push_back(e);
        vector<ui> tX;
        for(auto e : X) if(Matrix[trs[e]][trs[u]]==1) tX.push_back(e);

        bnb_find_max(C, tR, tX);

        assert(C.back()==u);
        C.pop_back();
        X.push_back(u);
    }
}

void bnb(vector<ui>C,vector<ui>R,vector<ui>X)
{
    ++ ss;
    if(C.size()+R.size()<max_gc_size) return;
    if(R.empty()) {
        if(X.empty()) {
            ++ resnum;
            if(C.size() > max_gc_size) max_gc_size = C.size();
#ifdef _CollectRes_
            vector<ui> tmpC;
            for(auto e : C) tmpC.push_back(oid_mapping[e]);
            res.push_back(tmpC);
#endif
        }
        return;
    }
    vector<ui> branchf, skipR;
    branchf.resize(R.size(),0);
#ifdef _Pivot_

    ui pivot, md = 0;
    for(auto e : R) {
        ui td = 0;
        for(auto u : R) if(Matrix[trs[e]][trs[u]]==1) ++td;
        if(td > md) {
            md = td;
            pivot = e;
        }
    }
    for(auto e : X) {
        ui td = 0;
        for(auto u : R) if(Matrix[trs[e]][trs[u]]==1) ++td;
        if(td > md) {
            md = td;
            pivot = e;
        }
    }
    if(md!=0) {
        for(ui i = 0; i < R.size(); ++i) if(Matrix[trs[R[i]]][trs[pivot]]==1) branchf[i]=1;
    }
#endif

    for(ui i = 0; i < R.size(); ++i) {
        if(branchf[i]==1) {
            skipR.push_back(R[i]);
            continue;
        }
        ui u = R[i];
        C.push_back(u);
        vector<ui> tR;
        for(ui j = i+1; j < R.size(); ++j) if(Matrix[trs[R[j]]][trs[u]]==1) tR.push_back(R[j]);
        for(auto e : skipR) if(Matrix[trs[e]][trs[u]]==1) tR.push_back(e);
        vector<ui> tX;
        for(auto e : X) if(Matrix[trs[e]][trs[u]]==1) tX.push_back(e);

        bnb(C, tR, tX);

        assert(C.back()==u);
        C.pop_back();
        X.push_back(u);
    }
}

void construct_egosg_and_core_pruning(vector<ui>&C,vector<ui>&R,vector<ui>&X,char * vis)
{
    vector<ui> S;
    for(auto e : C) S.push_back(e);
    for(auto e : R) S.push_back(e);
    for(auto e : X) S.push_back(e);
    for(auto u : S) {
        assert(vis[u]==1);
        s_pend[u] = s_pstart[u];
        for(ui i = pstart[u]; i < pstart[u+1]; ++i) if(vis[edges[i]]==1) s_edges[s_pend[u]++] = edges[i];
        s_degree[u] = s_pend[u]-s_pstart[u];
    }
#ifdef _CheckInfo_
    cout<<"C, R, X, information:"<<endl;
    cout<<"C: ";for(auto e : C) cout<<e<<",";cout<<endl;
    cout<<"R: ";for(auto e : R) cout<<e<<",";cout<<endl;
    cout<<"X: ";for(auto e : X) cout<<e<<",";cout<<endl;

    cout<<"ego subgraph information:"<<endl;
    for(auto e : S) {
        cout<<"vertex "<<e<<", (deg="<<s_degree[e]<<"), its neighbors: ";
        for(ui i = s_pstart[e]; i < s_pend[e]; ++i) cout<<s_edges[i]<<","; cout<<endl;
    }
#endif
    int threshold = sz - 1;
    queue<ui> Q;
    for(auto e : S) if(s_degree[e] < threshold) Q.push(e);
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        vis[u]=0;
        for(ui i = s_pstart[u]; i < s_pend[u]; ++i) {
            if(s_degree[s_edges[i]]--==threshold)Q.push(s_edges[i]);
        }
    }
    ui C_idx = 0;
    for(ui i = 0; i < C.size(); ++i) if(vis[C[i]]) C[C_idx++] = C[i];
    C.resize(C_idx);

    ui R_idx = 0;
    for(ui i = 0; i < R.size(); ++i) if(vis[R[i]]) R[R_idx++] = R[i];
    R.resize(R_idx);

    ui X_idx = 0;
    for(ui i = 0; i < X.size(); ++i) if(vis[X[i]]) X[X_idx++] = X[i];
    X.resize(X_idx);
#ifdef _CheckInfo_
    cout<<"C', R', X', information:"<<endl;
    cout<<"C': ";for(auto e : C) cout<<e<<",";cout<<endl;
    cout<<"R': ";for(auto e : R) cout<<e<<",";cout<<endl;
    cout<<"X': ";for(auto e : X) cout<<e<<",";cout<<endl;
#endif
}

void construct_egosg_and_core_pruning(ui u, vector<ui>&StructNei, vector<ui>&SimNei, ui*vis, vector<ui>&sg_vs, vector<ui>&sg_ve, vector<ui>&sg_e, vector<ui>&sg_deg, vector<vector<ui>>&progress_sim_nei_list)
{
    vector<ui> S;
    S.push_back(u);
    for(auto e : StructNei) S.push_back(e);
    for(auto e : SimNei) S.push_back(e);
    sg_e.clear();
    ui pos = 0;
    for(auto v : S) {
        sg_vs[v] = pos;
        for(ui i = pstart[v]; i < pstart[v+1]; ++i) if(vis[edges[i]]!=0) {
            ui w = edges[i];
            sg_e.push_back(w);
            ++pos;
        }
        for(auto w : progress_sim_nei_list[v]) if(vis[w]!=0) {
            sg_e.push_back(w);
            ++pos;
        }
        sg_ve[v] = pos;
        assert(sg_ve[v] >= sg_vs[v]);
        sg_deg[v] = sg_ve[v] - sg_vs[v];
    }
    int thre = max_gc_size;
    queue<ui> Q;
    for(auto e : S) if(sg_deg[e] < thre) Q.push(e);
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        assert(vis[u]!=0);
        vis[u]=0;
        for(ui i = sg_vs[u]; i < sg_ve[u]; ++i) {
            if(sg_deg[sg_e[i]]--==thre)Q.push(sg_e[i]);
        }
    }
    ui R_idx = 0;
    for(ui i = 0; i < StructNei.size(); ++i) if(vis[StructNei[i]]!=0) StructNei[R_idx++] = StructNei[i];
    StructNei.resize(R_idx);

    ui X_idx = 0;
    for(ui i = 0; i < SimNei.size(); ++i) if(vis[SimNei[i]]!=0) SimNei[X_idx++] = SimNei[i];
    SimNei.resize(X_idx);
}

void build_matrix(vector<ui>&C,vector<ui>&R,vector<ui>&X,char*vis)
{
    ui idx = 0;
    vector<ui> S;
    for(auto e : C) S.push_back(e);
    for(auto e : R) S.push_back(e);
    for(auto e : X) S.push_back(e);
    for(auto e : S) trs[e] = idx++;
    for(ui i = 0; i < idx; i++) for(ui j = 0; j < idx; j++) Matrix[i][j] = 0;
    for(auto e :S) {
        for(ui i = s_pstart[e]; i < s_pend[e]; ++i) if(vis[s_edges[i]]) Matrix[trs[e]][trs[s_edges[i]]]=1;
    }
#ifdef _CheckInfo_
    cout<<"check Matrix information:"<<endl;
    S.clear();
    for(auto e : C) S.push_back(e);
    for(auto e : R) S.push_back(e);
    for(auto e : X) S.push_back(e);
    for(auto u : S) {
        cout<<"vertex "<<u<<", its neighbors: ";
        for(auto v : S) {
            if(u==v) continue;
            if(Matrix[trs[u]][trs[v]]==1)cout<<v<<",";
        }
        cout<<endl;
    }
#endif
}

void build_matrix(ui u,vector<ui>&StructNei,vector<ui>&SimNei,ui*vis,vector<vector<ui>>&progress_sim_nei_list)
{
    ui idx = 0;
    vector<ui> S;

    S.push_back(u);
    for(auto e : StructNei) S.push_back(e);
    for(auto e : SimNei) S.push_back(e);

    for(auto e : S) trs[e] = idx++;

    for(ui i = 0; i < idx; i++) for(ui j = 0; j < idx; j++) Matrix[i][j] = 0;

    for(auto v :S) {
        for(ui i = pstart[v]; i < pstart[v+1]; ++i) {
            ui w = edges[i];
            if(vis[w] != 0){
                assert(Matrix[trs[v]][trs[w]]==0);
                Matrix[trs[v]][trs[w]]=1;
            }
        }
        for(auto w : progress_sim_nei_list[v]) {
            if(vis[w] != 0) {
                assert(Matrix[trs[v]][trs[w]]==0);
                Matrix[trs[v]][trs[w]]=2;
            }
        }
    }
#ifdef _CheckInfo_
    cout<<"check Matrix information:"<<endl;
    for(auto u : S) {
        cout<<"vertex "<<u<<", its neighbors: "<<endl;
        cout<<"\tits structural neighbors: ";
        for(auto v : S) {
            if(u==v) continue;
            if(Matrix[trs[u]][trs[v]]==1)cout<<v<<",";
        }
        cout<<endl;
        cout<<"\tits similar neighbors: ";
        for(auto v : S) {
            if(u==v) continue;
            if(Matrix[trs[u]][trs[v]]==2)cout<<v<<",";
        }
        cout<<endl;
    }
#endif
}

void build_matrix(ui u,vector<ui>&StructNei,ui*vis,vector<vector<ui>>&progress_sim_nei,ui* tmp_pstart, ui* tmp_edges, ui* tmp_degree)
{
    ui idx = 0;
    vector<ui> S;

    S.push_back(u);
    for(auto e : StructNei) S.push_back(e);

    for(auto e : S) trs[e] = idx++;

    for(ui i = 0; i < idx; i++) for(ui j = 0; j < idx; j++) Matrix[i][j] = 0;

    for(auto v :S) {
        for(ui i = tmp_pstart[v]; i < tmp_pstart[v+1]; ++i) {
            ui w = tmp_edges[i];
            if(vis[w] != 0){
                assert(Matrix[trs[v]][trs[w]]==0);
                Matrix[trs[v]][trs[w]]=1;
            }
        }
        for(auto w : progress_sim_nei[v]) {
            if(vis[w] != 0) {
                assert(Matrix[trs[v]][trs[w]]==0);
                Matrix[trs[v]][trs[w]]=2;
            }
        }
    }
#ifdef _CheckInfo_


#endif
}

void maximal_generalized_clique_enum_by_materialization()
{
    Timer tt;

    ss = 0;
    resnum = 0;
    max_gc_size = 0;
    res.clear();

    materialize_graph();

    ui * peels = new ui[n];
    char * vis = new char[n];
    ui * core = new ui[n];
    ui * rid = new ui[n];
    degree_based_vertex_reduce_and_rebuild_graph(peels,vis,core,rid,sz - 1);
    if(n>0)
    {
        ui md = 0;
        for(ui u = 0; u < n; ++u) if(pstart[u+1]-pstart[u]>md) md=pstart[u+1]-pstart[u];
        Matrix = new char*[md+1];
        for(int i = 0; i < md+1; i++) Matrix[i] = new char[md+1];
        s_pstart = new ui[n+1];
        memcpy(s_pstart, pstart, sizeof(ui)*(n+1));
        s_pend = new ui[n];
        s_edges = new ui[m];
        s_degree = new ui[n];
        trs = new ui[n];
        memset(vis, 0, sizeof(char)*n);
        ui gap = n/10;
        for(ui i = 0; i < n; ++i) {
            if(i%gap==0)cout<<(i*10)/gap<<"%,"<<flush;if(i==n-1)cout<<"100%"<<endl<<flush;
#ifdef _CheckInfo_
            cout<<endl<<"processing vertex "<<peels[i]<<endl;
#endif
            ui u = peels[i];
            vector<ui>C;
            vector<ui>R;
            vector<ui>X;
            C.push_back(u);
            vis[u]=1;

            for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
                ui v = edges[i];
                vis[v]=1;
                if(rid[v]>rid[u]) R.push_back(v);
                else X.push_back(v);
            }
            construct_egosg_and_core_pruning(C,R,X,vis);
            if(C.empty() || C.size()+R.size()<sz) {
                for(auto e : C) vis[e] = 0;
                for(auto e : R) vis[e] = 0;
                for(auto e : X) vis[e] = 0;
                continue;
            }
            build_matrix(C,R,X,vis);
            bnb(C,R,X);
            for(auto e : C) vis[e] = 0;
            for(auto e : R) vis[e] = 0;
            for(auto e : X) vis[e] = 0;
#ifdef _CostlyDebug_
            for(ui i = 0; i < n; ++i) assert(vis[i]==0);
#endif
        }
        for(int i = 0; i < md+1; i++) {
            delete [] Matrix[i];
            Matrix[i] = nullptr;
        }
        delete [] Matrix;
    }
    delete [] peels;
    delete [] core;
    delete [] vis;
    delete [] rid;

    cout<<"res: "<<resnum<<", Max GC: "<<max_gc_size<<", search space: "<<ss<<endl;
    cout<<"time: "<<(double)tt.elapsed()/CLOCKS_PER_SEC<<"s,    (mat_time: "<<(double)tt_mat*100/tt.elapsed()<<"%)"<<endl;

    for(ui i = 0; i < res.size(); ++i) {
        if(res[i].size() < max_gc_size) continue;
        sort(res[i].begin(),res[i].end());
        cout<<i+1<<" Res members: "; for(auto e : res[i]) cout<<e<<","; cout<<endl;
    }
}

int find_a_heu_gc()
{

    int idx = -1;
    vector<ui> mcvec;
    ui * core = new ui[n];
    ui * peels = new ui[n];
    for(ui i = 0; i < n; ++i) peels[i]=i;
    ui * vis = new ui[n];
    memset(vis, 0, sizeof(ui)*n);
    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    heap->init(n, n-1, peels, degree);
    ui max_core = 0;
    for(ui i = 0;i < n;i ++) {
        ui u, key;
        heap->pop_min(u, key);
        int current_vnum = (int)(n-i);
        int min_deg = (int) key;
        if( idx == -1 && min_deg == (current_vnum-1) ) {
            idx = (int)i;
        }
        peels[i] = u;
        vis[u] = 1;
        for(ui j = pstart[u];j < pstart[u+1];j ++) if(vis[edges[j]] == 0) {
            heap->decrement(edges[j], 1);
        }
    }

    for(int j = idx; j < n; j++) mcvec.push_back(peels[j]);
    res.clear();
    res.push_back(mcvec);

    delete heap;
    delete [] core;
    delete [] peels;
    delete [] vis;
#ifdef _CheckInfo_
    cout<<"geu mc size = "<<mcvec.size()<<", members: "<<endl; for(auto e : mcvec) cout<<e<<","; cout<<endl;
#endif
    return mcvec.size();
}

void materialize_graph_query_v2(ui query_point)
{
    Timer tt;
    tt_mat = 0;

    const ui original_n = n;

    assert(query_point < original_n);


    ui* in_subgraph = new ui[original_n];
    memset(in_subgraph, 0, sizeof(ui) * original_n);

    vector<ui> sub_vertices;

    in_subgraph[query_point] = 1;
    sub_vertices.push_back(query_point);


    for(ui i = pstart[query_point];
        i < pstart[query_point + 1];
        ++i)
    {
        ui v = edges[i];

        if(in_subgraph[v] == 0) {
            in_subgraph[v] = 1;
            sub_vertices.push_back(v);
        }
    }


    for(ui i = pstart[query_point];
        i < pstart[query_point + 1];
        ++i)
    {
        ui u = edges[i];

        for(ui j = pstart[u];
            j < pstart[u + 1];
            ++j)
        {
            ui v = edges[j];

            if(in_subgraph[v] == 0) {
                in_subgraph[v] = 1;
                sub_vertices.push_back(v);
            }
        }
    }

    const ui query_n = (ui)sub_vertices.size();

    cout << "query_point: "
         << query_point << endl;

    cout << "query_subgraph_vertices: "
         << query_n << endl;


    ui* local_id = new ui[original_n];

    for(ui i = 0; i < query_n; ++i) {

        ui original_u = sub_vertices[i];

        local_id[original_u] = i;


        oid_mapping[i] = original_u;
    }


    ui* vis = new ui[original_n];
    memset(vis, 0, sizeof(ui) * original_n);

    ui* comnei_cnt = new ui[original_n];
    memset(comnei_cnt, 0, sizeof(ui) * original_n);


    vector<vector<ui>> ver_sim_neis(query_n);

    unsigned long long similar_edges_cnt = 0;


    for(ui local_u = 0;
        local_u < query_n;
        ++local_u)
    {
        ui u = sub_vertices[local_u];

        vector<ui> u_nei;


        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            ui v = edges[i];

            u_nei.push_back(v);
            vis[v] = 1;
        }


        vector<ui> u_2hopnei;


        for(auto e : u_nei)
        {
            for(ui i = pstart[e];
                i < pstart[e + 1];
                ++i)
            {
                ui v = edges[i];


                if(in_subgraph[v] == 0)
                    continue;


                if(vis[v] == 1 || v == u)
                    continue;


                if(vis[v] == 0) {
                    u_2hopnei.push_back(v);
                    vis[v] = 2;
                }

                ++comnei_cnt[v];
            }
        }


        for(auto v : u_2hopnei)
        {
            double sim_score =
                (double)comnei_cnt[v] /
                (degree[v] +
                 degree[u] -
                 comnei_cnt[v]);


            if(sim_score >= epsi &&
               comnei_cnt[v] >= ComNeiThre)
            {
                ui local_v =
                    local_id[v];

                ver_sim_neis[local_u].
                    push_back(local_v);
            }


#ifdef _CheckInfo_

            cout << "common neighbors information:"
                 << endl;

            cout << u
                 << ", "
                 << v
                 << ", comnei_cnt="
                 << comnei_cnt[v]
                 << ", sim_score="
                 << sim_score
                 << endl;

#endif
        }


        similar_edges_cnt +=
            ver_sim_neis[local_u].size();


        for(auto v : u_nei)
        {
            assert(vis[v] == 1);
            vis[v] = 0;
        }


        for(auto v : u_2hopnei)
        {
            comnei_cnt[v] = 0;

            assert(vis[v] == 2);

            vis[v] = 0;
        }


#ifdef _CostlyDebug_

        for(ui i = 0;
            i < original_n;
            ++i)
        {
            assert(vis[i] == 0);
            assert(comnei_cnt[i] == 0);
        }

#endif
    }


    delete [] vis;
    delete [] comnei_cnt;


    cout << "query_similar_edges_cnt: "
         << Utility::integer_to_string(
                similar_edges_cnt)
         << endl;


    unsigned long long original_edges_cnt = 0;


    for(auto u : sub_vertices)
    {
        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            ui v = edges[i];

            if(in_subgraph[v])
                ++original_edges_cnt;
        }
    }


    cout << "query_original_edges_cnt: "
         << Utility::integer_to_string(
                original_edges_cnt)
         << endl;


    unsigned long long total_edges_ull =
        original_edges_cnt +
        similar_edges_cnt;


    assert(
        total_edges_ull <=
        (unsigned long long)
        numeric_limits<ui>::max()
    );


    ui t_m =
        (ui)total_edges_ull;


    ui* t_pstart =
        new ui[query_n + 1];

    ui* t_edges =
        new ui[t_m];


    if(f_edges != nullptr) {
        delete [] f_edges;
        f_edges = nullptr;
    }


    f_edges =
        new char[t_m];

    memset(
        f_edges,
        0,
        sizeof(char) * t_m
    );


    ui pos = 0;


    for(ui local_u = 0;
        local_u < query_n;
        ++local_u)
    {
        ui original_u =
            sub_vertices[local_u];


        t_pstart[local_u] =
            pos;


        for(ui i = pstart[original_u];
            i < pstart[original_u + 1];
            ++i)
        {
            ui original_v =
                edges[i];


            if(in_subgraph[original_v] == 0)
                continue;


            ui local_v =
                local_id[original_v];


            t_edges[pos] =
                local_v;

            f_edges[pos] =
                0;

            ++pos;
        }


        for(auto local_v :
            ver_sim_neis[local_u])
        {
            t_edges[pos] =
                local_v;

            f_edges[pos] =
                1;

            ++pos;
        }


        degree[local_u] =
            pos - t_pstart[local_u];
    }


    t_pstart[query_n] =
        pos;


    assert(pos == t_m);


    delete [] pstart;
    delete [] edges;


    pstart =
        t_pstart;

    edges =
        t_edges;


    n =
        query_n;

    m =
        t_m;


    delete [] local_id;
    delete [] in_subgraph;


    cout << "compact query graph: n="
         << n
         << ", m="
         << m
         << endl;


    cout << "mat_time: "
         << (double)tt.elapsed()
            / CLOCKS_PER_SEC
         << "s"
         << endl
         << flush;


    tt_mat =
        tt.elapsed();


#ifdef _CheckInfo_

    cout << "materialized compact query graph:"
         << endl;


    for(ui u = 0;
        u < n;
        ++u)
    {
        cout << "vertex "
             << u
             << "(original="
             << oid_mapping[u]
             << "), deg="
             << degree[u]
             << ", neighbors: ";


        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            if(f_edges[i] == 0)
            {
                cout << edges[i]
                     << "(original="
                     << oid_mapping[edges[i]]
                     << ",o), ";
            }
            else
            {
                assert(
                    f_edges[i] == 1
                );

                cout << edges[i]
                     << "(original="
                     << oid_mapping[edges[i]]
                     << ",s), ";
            }
        }

        cout << endl;
    }

#endif
}

void degree_based_vertex_reduce_and_rebuild_graph_query(
    ui* peels,
    char* vis,
    ui* core,
    ui* rid,
    int threshold)
{
    Timer tt;

    const ui old_n = n;

    ui queue_n = 0;
    ui new_size = 0;


    for(ui i = 0; i < n; ++i)
    {
        if(degree[i] < threshold)
            peels[queue_n++] = i;
    }


    for(ui i = 0;
        i < queue_n;
        ++i)
    {
        ui u =
            peels[i];

        degree[u] =
            0;


        for(ui j = pstart[u];
            j < pstart[u + 1];
            ++j)
        {
            ui v =
                edges[j];


            if(degree[v] > 0)
            {
                if((degree[v]--) ==
                   (ui)threshold)
                {
                    peels[queue_n++] =
                        v;
                }
            }
        }
    }


    if(queue_n == n)
    {
        cout << "reduced graph is empty"
             << endl;

        n = 0;
        m = 0;

        return;
    }


    memset(
        vis,
        0,
        sizeof(char) * n
    );


    for(ui i = 0;
        i < n;
        ++i)
    {
        if(degree[i] >=
           (ui)threshold)
        {
            peels[
                queue_n +
                (new_size++)
            ] = i;
        }
        else
        {
            vis[i] = 1;
            core[i] = 0;
        }
    }


    assert(
        queue_n + new_size ==
        n
    );


    ListLinearHeap* heap =
        new ListLinearHeap(
            n,
            n - 1
        );


    heap->init(
        new_size,
        new_size - 1,
        peels + queue_n,
        degree
    );


    ui max_core = 0;


    for(ui i = 0;
        i < new_size;
        ++i)
    {
        ui u, key;

        heap->pop_min(
            u,
            key
        );


        if(key > max_core)
            max_core = key;


        core[u] =
            max_core;


        peels[
            queue_n + i
        ] = u;


        vis[u] =
            1;


        for(ui j = pstart[u];
            j < pstart[u + 1];
            ++j)
        {
            ui v =
                edges[j];


            if(vis[v] == 0)
            {
                heap->decrement(
                    v,
                    1
                );
            }
        }
    }


    delete heap;


    vector<ui> old_id_by_new(
        new_size
    );

    vector<ui> original_id_by_new(
        new_size
    );

    vector<ui> new_core(
        new_size
    );


    ui cnt = 0;


    for(ui old_u = 0;
        old_u < old_n;
        ++old_u)
    {
        if(core[old_u] >=
           (ui)threshold)
        {
            rid[old_u] =
                cnt;

            old_id_by_new[cnt] =
                old_u;

            original_id_by_new[cnt] =
                oid_mapping[old_u];

            new_core[cnt] =
                core[old_u];

            ++cnt;
        }
    }


    assert(
        cnt ==
        new_size
    );


    cnt = 0;

    ui pos = 0;


    for(ui old_u = 0;
        old_u < old_n;
        ++old_u)
    {
        if(core[old_u] <
           (ui)threshold)
        {
            continue;
        }


        ui old_start =
            pstart[old_u];


        pstart[cnt] =
            pos;


        for(ui j = old_start;
            j < pstart[old_u + 1];
            ++j)
        {
            ui old_v =
                edges[j];


            if(core[old_v] >=
               (ui)threshold)
            {
                edges[pos] =
                    rid[old_v];

                f_edges[pos] =
                    f_edges[j];

                ++pos;
            }
        }


        ++cnt;
    }


    pstart[cnt] =
        pos;


    assert(
        cnt ==
        new_size
    );


    n =
        new_size;

    m =
        pos;


    cout << "vr: (n="
         << n
         << ", m="
         << m
         << ")"
         << endl;


    vector<ui> new_peels(
        new_size
    );


    for(ui i = 0;
        i < new_size;
        ++i)
    {
        ui old_u =
            peels[
                queue_n + i
            ];


        new_peels[i] =
            rid[old_u];
    }


    for(ui i = 0;
        i < new_size;
        ++i)
    {
        peels[i] =
            new_peels[i];

        core[i] =
            new_core[i];


        oid_mapping[i] =
            original_id_by_new[i];
    }


    for(ui i = 0;
        i < n;
        ++i)
    {
        rid[peels[i]] =
            i;
    }


#ifdef _CostlyDebug_

    for(ui u = 0;
        u < n;
        ++u)
    {
        assert(
            core[u] >=
            (ui)threshold
        );


        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            ui v =
                edges[i];


            if(rid[v] > rid[u])
            {
                assert(
                    core[v] >=
                    core[u]
                );
            }
            else
            {
                assert(
                    rid[v] <
                    rid[u]
                );

                assert(
                    core[v] <=
                    core[u]
                );
            }
        }
    }

#endif


#ifdef _CheckInfo_

    cout << "after query graph reassign vid:"
         << endl;


    for(ui u = 0;
        u < n;
        ++u)
    {
        cout << "vertex "
             << u
             << "(original="
             << oid_mapping[u]
             << "), its neighbors: ";


        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            ui v =
                edges[i];


            cout << v
                 << "(original="
                 << oid_mapping[v];


            if(f_edges[i] == 0)
                cout << ",o), ";
            else
                cout << ",s), ";
        }


        cout << endl;
    }

#endif
}

void restrict_to_query_closed_neighborhood(ui query_local)
{
    assert(query_local < n);

    const ui old_n = n;


    vector<char> keep(old_n, 0);
    vector<ui> new2old;

    keep[query_local] = 1;
    new2old.push_back(query_local);

    for(ui i = pstart[query_local];
        i < pstart[query_local + 1];
        ++i)
    {
        ui v = edges[i];

        if(!keep[v]) {
            keep[v] = 1;
            new2old.push_back(v);
        }
    }

    const ui new_n = (ui)new2old.size();

    cout << "query compatible region: n="
         << new_n << endl;


    vector<ui> old2new(old_n, numeric_limits<ui>::max());

    for(ui new_u = 0;
        new_u < new_n;
        ++new_u)
    {
        old2new[new2old[new_u]] = new_u;
    }

    assert(old2new[query_local] == 0);


    vector<ui> new_oid(new_n);

    for(ui new_u = 0;
        new_u < new_n;
        ++new_u)
    {
        ui old_u = new2old[new_u];

        new_oid[new_u] = oid_mapping[old_u];
    }


    unsigned long long new_m_ull = 0;

    for(ui new_u = 0;
        new_u < new_n;
        ++new_u)
    {
        ui old_u = new2old[new_u];

        for(ui i = pstart[old_u];
            i < pstart[old_u + 1];
            ++i)
        {
            ui old_v = edges[i];

            if(keep[old_v])
                ++new_m_ull;
        }
    }

    assert(
        new_m_ull <=
        (unsigned long long)numeric_limits<ui>::max()
    );

    ui new_m = (ui)new_m_ull;


    ui* new_pstart = new ui[new_n + 1];
    ui* new_edges = new ui[new_m];
    char* new_f_edges = new char[new_m];

    ui pos = 0;

    for(ui new_u = 0;
        new_u < new_n;
        ++new_u)
    {
        ui old_u = new2old[new_u];

        new_pstart[new_u] = pos;

        for(ui i = pstart[old_u];
            i < pstart[old_u + 1];
            ++i)
        {
            ui old_v = edges[i];

            if(!keep[old_v])
                continue;

            ui new_v = old2new[old_v];

            new_edges[pos] = new_v;

            if(f_edges != nullptr)
                new_f_edges[pos] = f_edges[i];
            else
                new_f_edges[pos] = 0;

            ++pos;
        }

        degree[new_u] =
            pos - new_pstart[new_u];
    }

    new_pstart[new_n] = pos;

    assert(pos == new_m);


    delete [] pstart;
    delete [] edges;

    if(f_edges != nullptr)
        delete [] f_edges;

    pstart = new_pstart;
    edges = new_edges;
    f_edges = new_f_edges;

    n = new_n;
    m = new_m;


    for(ui u = 0;
        u < n;
        ++u)
    {
        oid_mapping[u] = new_oid[u];
    }


    assert(oid_mapping[0] == new_oid[0]);
    assert(degree[0] == n - 1);

    cout << "query closed neighborhood: (n="
         << n
         << ", m="
         << m
         << ")"
         << endl;
}

void materialize_graph_query_containing_q(ui query_point)
{
    Timer tt;
    tt_mat = 0;

    const ui original_n = n;

    assert(query_point < original_n);


    char* in_query = new char[original_n];
    memset(in_query, 0, sizeof(char) * original_n);


    char* vis = new char[original_n];
    memset(vis, 0, sizeof(char) * original_n);


    ui* comnei_cnt = new ui[original_n];

    vector<ui> query_vertices;


    in_query[query_point] = 1;
    query_vertices.push_back(query_point);


    for(ui i = pstart[query_point];
        i < pstart[query_point + 1];
        ++i)
    {
        ui v = edges[i];

        if(!in_query[v]) {
            in_query[v] = 1;
            query_vertices.push_back(v);
        }


        vis[v] = 1;
    }


    vector<ui> q_2hop_candidates;

    for(ui i = pstart[query_point];
        i < pstart[query_point + 1];
        ++i)
    {
        ui common_neighbor = edges[i];

        for(ui j = pstart[common_neighbor];
            j < pstart[common_neighbor + 1];
            ++j)
        {
            ui v = edges[j];


            if(v == query_point)
                continue;


            if(vis[v] == 1)
                continue;


            if(vis[v] == 0) {
                vis[v] = 2;

                q_2hop_candidates.push_back(v);

                comnei_cnt[v] = 1;
            }
            else {
                assert(vis[v] == 2);

                ++comnei_cnt[v];
            }
        }
    }


    for(ui v : q_2hop_candidates)
    {
        ui cn = comnei_cnt[v];

        double sim_score =
            (double)cn /
            (degree[query_point] +
             degree[v] -
             cn);

        if(sim_score >= epsi &&
           cn >= ComNeiThre)
        {


            if(!in_query[v]) {
                in_query[v] = 1;
                query_vertices.push_back(v);
            }
        }
    }


    for(ui i = pstart[query_point];
        i < pstart[query_point + 1];
        ++i)
    {
        vis[edges[i]] = 0;
    }

    for(ui v : q_2hop_candidates)
    {
        vis[v] = 0;
    }


    const ui query_n =
        (ui)query_vertices.size();


    cout << "query_point: "
         << query_point
         << endl;

    cout << "q-compatible region |V|: "
         << query_n
         << endl;

    cout << "q structural neighbors: "
         << degree[query_point]
         << endl;

    cout << "q similar neighbors: "
         << query_n
                - 1
                - degree[query_point]
         << endl;


    ui* local_id = new ui[original_n];

    for(ui local_u = 0;
        local_u < query_n;
        ++local_u)
    {
        ui original_u =
            query_vertices[local_u];

        local_id[original_u] =
            local_u;


        oid_mapping[local_u] =
            original_u;
    }

    assert(oid_mapping[0] == query_point);


    vector<vector<ui>> ver_sim_neis(query_n);

    unsigned long long similar_edges_cnt = 0;


    for(ui local_u = 0;
        local_u < query_n;
        ++local_u)
    {
        ui u =
            query_vertices[local_u];


        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            ui v = edges[i];

            vis[v] = 1;
        }


        vector<ui> u_2hop_candidates;


        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            ui common_neighbor =
                edges[i];

            for(ui j = pstart[common_neighbor];
                j < pstart[common_neighbor + 1];
                ++j)
            {
                ui v =
                    edges[j];


                if(!in_query[v])
                    continue;


                if(v == u ||
                   vis[v] == 1)
                {
                    continue;
                }


                if(vis[v] == 0)
                {
                    vis[v] = 2;

                    u_2hop_candidates.
                        push_back(v);

                    comnei_cnt[v] = 1;
                }
                else
                {
                    assert(vis[v] == 2);

                    ++comnei_cnt[v];
                }
            }
        }


        for(ui v : u_2hop_candidates)
        {
            ui cn =
                comnei_cnt[v];

            double sim_score =
                (double)cn /
                (degree[u] +
                 degree[v] -
                 cn);


            if(sim_score >= epsi &&
               cn >= ComNeiThre)
            {
                ui local_v =
                    local_id[v];

                ver_sim_neis[local_u].
                    push_back(local_v);
            }
        }


        similar_edges_cnt +=
            ver_sim_neis[local_u].
                size();


        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            vis[edges[i]] = 0;
        }

        for(ui v : u_2hop_candidates)
        {
            vis[v] = 0;
        }
    }


    delete [] vis;
    delete [] comnei_cnt;


    cout << "query_similar_edges_cnt: "
         << Utility::integer_to_string(
                similar_edges_cnt)
         << endl;


    unsigned long long original_edges_cnt = 0;


    for(ui original_u : query_vertices)
    {
        for(ui i = pstart[original_u];
            i < pstart[original_u + 1];
            ++i)
        {
            ui original_v =
                edges[i];

            if(in_query[original_v])
            {
                ++original_edges_cnt;
            }
        }
    }


    cout << "query_original_edges_cnt: "
         << Utility::integer_to_string(
                original_edges_cnt)
         << endl;


    unsigned long long total_edges_ull =
        original_edges_cnt +
        similar_edges_cnt;


    assert(
        total_edges_ull <=
        (unsigned long long)
        numeric_limits<ui>::max()
    );


    ui new_m =
        (ui)total_edges_ull;


    ui* new_pstart =
        new ui[query_n + 1];

    ui* new_edges =
        new ui[new_m];


    if(f_edges != nullptr)
    {
        delete [] f_edges;
        f_edges = nullptr;
    }


    f_edges =
        new char[new_m];


    ui pos = 0;


    for(ui local_u = 0;
        local_u < query_n;
        ++local_u)
    {
        ui original_u =
            query_vertices[local_u];

        new_pstart[local_u] =
            pos;


        for(ui i = pstart[original_u];
            i < pstart[original_u + 1];
            ++i)
        {
            ui original_v =
                edges[i];

            if(!in_query[original_v])
                continue;


            ui local_v =
                local_id[original_v];


            new_edges[pos] =
                local_v;

            f_edges[pos] =
                0;

            ++pos;
        }


        for(ui local_v :
            ver_sim_neis[local_u])
        {
            new_edges[pos] =
                local_v;

            f_edges[pos] =
                1;

            ++pos;
        }


        degree[local_u] =
            pos -
            new_pstart[local_u];
    }


    new_pstart[query_n] =
        pos;


    assert(pos == new_m);


    delete [] pstart;
    delete [] edges;


    pstart =
        new_pstart;

    edges =
        new_edges;


    n =
        query_n;

    m =
        new_m;


    delete [] local_id;
    delete [] in_query;


    assert(oid_mapping[0] == query_point);

    assert(degree[0] == n - 1);


    cout << "compact q-containing query graph: n="
         << n
         << ", m="
         << m
         << endl;


    cout << "mat_time: "
         << (double)tt.elapsed()
            / CLOCKS_PER_SEC
         << "s"
         << endl
         << flush;


    tt_mat =
        tt.elapsed();


#ifdef _CheckInfo_

    cout << "materialized q-containing query graph:"
         << endl;


    for(ui u = 0;
        u < n;
        ++u)
    {
        cout << "vertex "
             << u
             << "(original="
             << oid_mapping[u]
             << "), deg="
             << degree[u]
             << ", neighbors: ";


        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            ui v =
                edges[i];

            cout << v
                 << "(original="
                 << oid_mapping[v];

            if(f_edges[i] == 0)
                cout << ",o), ";
            else {
                assert(
                    f_edges[i] == 1
                );

                cout << ",s), ";
            }
        }

        cout << endl;
    }

#endif
}

int find_a_heu_gc_containing_query(ui query_local)
{
    int ret = find_a_heu_gc();

    assert(!res.empty());

    bool contain_q = false;

    for(ui v : res[0])
    {
        if(v == query_local) {
            contain_q = true;
            break;
        }
    }


    if(!contain_q)
    {
        res[0].push_back(query_local);

        ++ret;
    }

    return ret;
}

void maximum_generalized_clique_computation_query(ui query_point)
{
    Timer t;
    Timer tt;

    ss = 0;
    resnum = 0;
    max_gc_size = 0;
    res.clear();

    double t_materialization = 0;
    double t_heu = 0;
    double t_vr_and_rebuild = 0;
    double t_construct_subgraph = 0;
    double t_build_matrix = 0;
    double t_bnb = 0;

    tt.restart();

    materialize_graph_query_v2(query_point);
    assert(oid_mapping[0] == query_point);
    restrict_to_query_closed_neighborhood(0);


    assert(oid_mapping[0] == query_point);
    assert(degree[0] == n - 1);

    t_materialization += (double)tt.elapsed() / CLOCKS_PER_SEC;

    tt.restart();

    max_gc_size = find_a_heu_gc_containing_query(0);
    cout<<"heu solu size    : "<<max_gc_size<<endl;
    t_heu += (double)tt.elapsed() / CLOCKS_PER_SEC;

    int thre = max_gc_size;

    ui * peels = new ui[n];
    char * vis = new char[n];
    ui * core = new ui[n];
    ui * rid = new ui[n];

    tt.restart();
    degree_based_vertex_reduce_and_rebuild_graph_query(peels,vis,core,rid,thre);
    t_vr_and_rebuild += (double)tt.elapsed() / CLOCKS_PER_SEC;

    if(n>0)
    {
        ui md = 0;
        for(ui u = 0; u < n; ++u) if(pstart[u+1]-pstart[u]>md) md=pstart[u+1]-pstart[u];
        Matrix = new char*[md+1];
        for(int i = 0; i < md+1; i++) Matrix[i] = new char[md+1];
        s_pstart = new ui[n+1];
        memcpy(s_pstart, pstart, sizeof(ui)*(n+1));
        s_pend = new ui[n];
        s_edges = new ui[m];
        s_degree = new ui[n];
        trs = new ui[n];
        memset(vis, 0, sizeof(char)*n);
        ui gap = max((ui)1, n/10);
        for(ui i = 0; i < n; ++i) {
            if(i%gap==0)cout<<(i*10)/gap<<"%,"<<flush;if(i==n-1)cout<<"100%"<<endl<<flush;
#ifdef _CheckInfo_
            cout<<endl<<"processing vertex "<<peels[i]<<endl;
#endif
            ui u = peels[i];
            vector<ui>C;
            vector<ui>R;
            vector<ui>X;
            C.push_back(u);
            vis[u]=1;

            for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
                ui v = edges[i];
                vis[v]=1;
                if(rid[v]>rid[u]) R.push_back(v);
                else X.push_back(v);
            }

            tt.restart();
            construct_egosg_and_core_pruning(C,R,X,vis);
            t_construct_subgraph += (double)tt.elapsed() / CLOCKS_PER_SEC;

            if(C.empty() || C.size()+R.size()<=(ui)max_gc_size) {
                for(auto e : C) vis[e] = 0;
                for(auto e : R) vis[e] = 0;
                for(auto e : X) vis[e] = 0;
                continue;
            }

            tt.restart();
            build_matrix(C,R,X,vis);
            t_build_matrix += (double)tt.elapsed() / CLOCKS_PER_SEC;

            tt.restart();
            bnb_find_max(C,R,X);
            t_bnb += (double)tt.elapsed() / CLOCKS_PER_SEC;

            for(auto e : C) vis[e] = 0;
            for(auto e : R) vis[e] = 0;
            for(auto e : X) vis[e] = 0;
#ifdef _CostlyDebug_
            for(ui i = 0; i < n; ++i) assert(vis[i]==0);
#endif
        }
        for(int i = 0; i < md+1; i++) {
            delete [] Matrix[i];
            Matrix[i] = nullptr;
        }
        delete [] Matrix;
        Matrix = nullptr;

        delete [] s_pstart;
        s_pstart = nullptr;

        delete [] s_pend;
        s_pend = nullptr;

        delete [] s_edges;
        s_edges = nullptr;

        delete [] s_degree;
        s_degree = nullptr;

        delete [] trs;
        trs = nullptr;
    }
    delete [] peels;
    delete [] core;
    delete [] vis;
    delete [] rid;

    cout<<"Max GC: "<<max_gc_size<<", search space: "<<ss<<endl;
#ifdef _CollectRes_
    sort(res[0].begin(),res[0].end());
    cout<<"Res members: "; for(auto e : res[0]) cout<<e<<","; cout<<endl;
#endif
    cout << fixed << setprecision(2);
    double total_time = (double)t.elapsed()/CLOCKS_PER_SEC;
    cout << "\tTime: "<<total_time<<"s"<<endl;
    cout << "\tmaterialize  t = " << t_materialization << " s,  " <<(double)t_materialization/total_time*100<<" %"<< endl;
    cout << "\theu          t = " << t_heu << " s,  " <<(double)t_heu/total_time*100<<" %"<< endl;
    cout << "\tvr_&_rebuild t = " << t_vr_and_rebuild << " s,  " <<(double)t_vr_and_rebuild/total_time*100<<" %"<< endl;
    cout << "\tconstruct sg t = " << t_construct_subgraph << " s,  " <<(double)t_construct_subgraph/total_time*100<<" %"<< endl;
    cout << "\tbuild matrix t = " << t_build_matrix << " s,  " <<(double)t_build_matrix/total_time*100<<" %"<< endl;
    cout << "\tbnb t          = " << t_bnb << " s,  " <<(double)t_bnb/total_time*100<<" %"<< endl;
}

void maximum_generalized_clique_computation_query_batch( const vector<ui>& query_points)
{
    if(query_points.empty()) {
        cout << "query_points is empty!" << endl;
        return;
    }


    const ui original_n = n;
    const ui original_m = m;

    vector<ui> original_pstart(original_n + 1);
    vector<ui> original_edges(original_m);
    vector<ui> original_degree(original_n);

    memcpy(original_pstart.data(),
           pstart,
           sizeof(ui) * (original_n + 1));

    memcpy(original_edges.data(),
           edges,
           sizeof(ui) * original_m);

    memcpy(original_degree.data(),
           degree,
           sizeof(ui) * original_n);


    auto restore_original_graph = [&]() {

        delete [] pstart;
        delete [] edges;

        pstart = new ui[original_n + 1];
        edges = new ui[original_m];

        memcpy(pstart,
               original_pstart.data(),
               sizeof(ui) * (original_n + 1));

        memcpy(edges,
               original_edges.data(),
               sizeof(ui) * original_m);

        memcpy(degree,
               original_degree.data(),
               sizeof(ui) * original_n);

        n = original_n;
        m = original_m;


        if(f_edges != nullptr) {
            delete [] f_edges;
            f_edges = nullptr;
        }
    };


    double total_query_time = 0.0;
    double min_query_time = DBL_MAX;
    double max_query_time = 0.0;

    unsigned long long total_mgc_size = 0;
    unsigned long long total_search_space = 0;

    ui min_mgc_size = UINT_MAX;
    ui max_mgc_size_batch = 0;

    ui valid_query_cnt = 0;

    Timer batch_timer;


    cout << endl;
    cout << "========================================" << endl;
    cout << "Materialization Query-based MGC" << endl;
    cout << "#queries = " << query_points.size() << endl;
    cout << "========================================" << endl;


    for(ui qi = 0;
        qi < query_points.size();
        ++qi)
    {
        ui query_point = query_points[qi];

        if(query_point >= original_n) {
            cout << "invalid query point: "
                 << query_point
                 << ", skipped." << endl;
            continue;
        }


        restore_original_graph();


        Timer query_timer;


        maximum_generalized_clique_computation_query(
            query_point
        );


        double query_time =
            (double)query_timer.elapsed()
            / CLOCKS_PER_SEC;


        total_query_time +=
            query_time;

        min_query_time =
            min(min_query_time,
                query_time);

        max_query_time =
            max(max_query_time,
                query_time);


        total_mgc_size +=
            (ui)max_gc_size;

        total_search_space +=
            ss;


        min_mgc_size =
            min(min_mgc_size,
                (ui)max_gc_size);

        max_mgc_size_batch =
            max(max_mgc_size_batch,
                (ui)max_gc_size);


        ++valid_query_cnt;


        cout << "[Query "
             << valid_query_cnt
             << "/"
             << query_points.size()
             << "] q="
             << query_point
             << ", MGC="
             << max_gc_size
             << ", time="
             << fixed
             << setprecision(4)
             << query_time
             << " s"
             << endl << endl ;
    }


    restore_original_graph();


    if(valid_query_cnt == 0) {

        cout << "No valid query points!"
             << endl;

        return;
    }


    double qn =
        (double)valid_query_cnt;

    double avg_query_time =
        total_query_time / qn;

    double avg_mgc_size =
        (double)total_mgc_size / qn;

    double avg_search_space =
        (double)total_search_space / qn;

    double batch_wall_time =
        (double)batch_timer.elapsed()
        / CLOCKS_PER_SEC;


    cout << endl;
    cout << "========================================" << endl;
    cout << "QUERY-BASED MGC SUMMARY" << endl;
    cout << "========================================" << endl;

    cout << fixed
         << setprecision(4);

    cout << "#Queries          : "
         << valid_query_cnt << endl;

    cout << "Total Time        : "
         << total_query_time
         << " s" << endl;

    cout << "Avg Query Time    : "
         << avg_query_time
         << " s" << endl;

    cout << "Min Query Time    : "
         << min_query_time
         << " s" << endl;

    cout << "Max Query Time    : "
         << max_query_time
         << " s" << endl;


    cout << "Batch Wall Time   : "
         << batch_wall_time
         << " s" << endl;

    cout << "Avg MGC Size      : "
         << avg_mgc_size << endl;

    cout << "Min MGC Size      : "
         << min_mgc_size << endl;

    cout << "Max MGC Size      : "
         << max_mgc_size_batch << endl;


    cout << "========================================" << endl;
}

void maximum_generalized_clique_computation_by_materialization()
{
    Timer t;
    Timer tt;

    ss = 0;
    resnum = 0;
    max_gc_size = 0;
    res.clear();

    double t_materialization = 0;
    double t_heu = 0;
    double t_vr_and_rebuild = 0;
    double t_construct_subgraph = 0;
    double t_build_matrix = 0;
    double t_bnb = 0;

    tt.restart();
    materialize_graph();
    t_materialization += (double)tt.elapsed() / CLOCKS_PER_SEC;

    tt.restart();
    max_gc_size = find_a_heu_gc();
    cout<<"heu solu size    : "<<max_gc_size<<endl;
    t_heu += (double)tt.elapsed() / CLOCKS_PER_SEC;

    int thre = sz - 1;
    if(max_gc_size > thre) thre = max_gc_size;

    ui * peels = new ui[n];
    char * vis = new char[n];
    ui * core = new ui[n];
    ui * rid = new ui[n];

    tt.restart();
    degree_based_vertex_reduce_and_rebuild_graph(peels,vis,core,rid,thre);
    t_vr_and_rebuild += (double)tt.elapsed() / CLOCKS_PER_SEC;

    if(n>0)
    {
        ui md = 0;
        for(ui u = 0; u < n; ++u) if(pstart[u+1]-pstart[u]>md) md=pstart[u+1]-pstart[u];
        Matrix = new char*[md+1];
        for(int i = 0; i < md+1; i++) Matrix[i] = new char[md+1];
        s_pstart = new ui[n+1];
        memcpy(s_pstart, pstart, sizeof(ui)*(n+1));
        s_pend = new ui[n];
        s_edges = new ui[m];
        s_degree = new ui[n];
        trs = new ui[n];
        memset(vis, 0, sizeof(char)*n);
        ui gap = n/10;
        for(ui i = 0; i < n; ++i) {
            if(i%gap==0)cout<<(i*10)/gap<<"%,"<<flush;if(i==n-1)cout<<"100%"<<endl<<flush;
#ifdef _CheckInfo_
            cout<<endl<<"processing vertex "<<peels[i]<<endl;
#endif
            ui u = peels[i];
            vector<ui>C;
            vector<ui>R;
            vector<ui>X;
            C.push_back(u);
            vis[u]=1;

            for(ui i = pstart[u]; i < pstart[u+1]; ++i) {
                ui v = edges[i];
                vis[v]=1;
                if(rid[v]>rid[u]) R.push_back(v);
                else X.push_back(v);
            }

            tt.restart();
            construct_egosg_and_core_pruning(C,R,X,vis);
            t_construct_subgraph += (double)tt.elapsed() / CLOCKS_PER_SEC;

            if(C.empty() || C.size()+R.size()<sz) {
                for(auto e : C) vis[e] = 0;
                for(auto e : R) vis[e] = 0;
                for(auto e : X) vis[e] = 0;
                continue;
            }

            tt.restart();
            build_matrix(C,R,X,vis);
            t_build_matrix += (double)tt.elapsed() / CLOCKS_PER_SEC;

            tt.restart();
            bnb_find_max(C,R,X);
            t_bnb += (double)tt.elapsed() / CLOCKS_PER_SEC;

            for(auto e : C) vis[e] = 0;
            for(auto e : R) vis[e] = 0;
            for(auto e : X) vis[e] = 0;
#ifdef _CostlyDebug_
            for(ui i = 0; i < n; ++i) assert(vis[i]==0);
#endif
        }
        for(int i = 0; i < md+1; i++) {
            delete [] Matrix[i];
            Matrix[i] = nullptr;
        }
        delete [] Matrix;
    }
    delete [] peels;
    delete [] core;
    delete [] vis;
    delete [] rid;

    cout<<"Max GC: "<<max_gc_size<<", search space: "<<ss<<endl;
#ifdef _CollectRes_
    sort(res[0].begin(),res[0].end());
    cout<<"Res members: "; for(auto e : res[0]) cout<<e<<","; cout<<endl;
#endif
    cout << fixed << setprecision(2);
    double total_time = (double)t.elapsed()/CLOCKS_PER_SEC;
    cout << "\tTime: "<<total_time<<"s"<<endl;
    cout << "\tmaterialize  t = " << t_materialization << " s,  " <<(double)t_materialization/total_time*100<<" %"<< endl;
    cout << "\theu          t = " << t_heu << " s,  " <<(double)t_heu/total_time*100<<" %"<< endl;
    cout << "\tvr_&_rebuild t = " << t_vr_and_rebuild << " s,  " <<(double)t_vr_and_rebuild/total_time*100<<" %"<< endl;
    cout << "\tconstruct sg t = " << t_construct_subgraph << " s,  " <<(double)t_construct_subgraph/total_time*100<<" %"<< endl;
    cout << "\tbuild matrix t = " << t_build_matrix << " s,  " <<(double)t_build_matrix/total_time*100<<" %"<< endl;
    cout << "\tbnb t          = " << t_bnb << " s,  " <<(double)t_bnb/total_time*100<<" %"<< endl;
}


ui obtain_current_color_ub(const vector<ui>& R)
{
    if(R.empty()) return 0;

    ++gc_color_token;


    if(gc_color_token == 0) {
        fill(gc_color_seen.begin(), gc_color_seen.end(), 0);
        gc_color_token = 1;
    }

    ui color_ub = 0;

    for(ui v : R) {
        assert(trs[v] < gc_color.size());

        ui color_v = gc_color[trs[v]];

        assert(color_v >= 1);
        assert(color_v <= gc_color_num);


        if(gc_color_seen[color_v] != gc_color_token) {
            gc_color_seen[color_v] = gc_color_token;
            ++color_ub;
        }
    }

    return color_ub;
}


ui vertex_reduction_in_bnb(vector<ui>& R, ui current_clique_size, ui target_gc_size)
{
    if(R.empty()) return 0;


    if(current_clique_size >= target_gc_size) return 0;

    ui need = target_gc_size - current_clique_size;


    if(R.size() < need) {
        ui removed_cnt = (ui)R.size();
        R.clear();
        return removed_cnt;
    }


    if(need <= 1) return 0;

    ui degree_threshold = need - 1;
    ui r_size = (ui)R.size();


    vector<ui> r_degree(r_size, 0);
    vector<char> alive(r_size, 1);


    vector<ui> Q;
    Q.reserve(r_size);


    for(ui i = 0; i < r_size; ++i) {
        ui u = R[i];

        for(ui j = i + 1; j < r_size; ++j) {
            ui v = R[j];

            if(Matrix[trs[u]][trs[v]] != 0) {
                ++r_degree[i];
                ++r_degree[j];
            }
        }
    }


    for(ui i = 0; i < r_size; ++i) {
        if(r_degree[i] < degree_threshold) {
            alive[i] = 0;
            Q.push_back(i);
        }
    }


    ui q_head = 0;

    while(q_head < Q.size()) {
        ui deleted_position = Q[q_head++];
        ui deleted_vertex = R[deleted_position];

        for(ui j = 0; j < r_size; ++j) {
            if(alive[j] == 0) continue;

            ui v = R[j];

            if(Matrix[trs[deleted_vertex]][trs[v]] != 0) {
                assert(r_degree[j] > 0);
                --r_degree[j];

                if(r_degree[j] < degree_threshold) {
                    alive[j] = 0;
                    Q.push_back(j);
                }
            }
        }
    }


    ui write_position = 0;

    for(ui i = 0; i < r_size; ++i) {
        if(alive[i] != 0) {
            R[write_position++] = R[i];
        }
    }

    ui removed_cnt = r_size - write_position;
    R.resize(write_position);

    return removed_cnt;
}

void bnb_finding_maximum_gc(vector<ui>&C,vector<ui>&R,ui target_gc_size)
{
    ++ss;
    if(C.size() + R.size() <= max_gc_size) return;
    if(max_gc_size >= target_gc_size) return;
    if(R.empty()) {
        if(C.size() > max_gc_size) {
            max_gc_size = C.size();
#ifdef _CollectRes_
            res.clear();
            vector<ui> tmpC;
            for(auto e : C) tmpC.push_back(oid_mapping[e]);
            res.push_back(tmpC);
#endif
        }
        return;
    }
#ifdef _Coloring_
    ui color_ub = obtain_current_color_ub(R);
    if(C.size() + color_ub <= max_gc_size) return;
#endif

#ifdef _BnBVR_
    if(R.size() >= BNB_VR_SIZE_THRESHOLD &&
       C.size() <= BNB_VR_MAX_DEPTH) {
        vertex_reduction_in_bnb(R, (ui)C.size(), target_gc_size);
        if(C.size() + R.size() < target_gc_size) return;
    }
#endif

    vector<ui> branchf, skipR;
    branchf.resize(R.size(),0);
#ifdef _Pivot_

    int pivot = -1;
    ui md = 0;
    for(auto e : R) {
        ui td = 0;
        for(auto u : R) if(Matrix[trs[e]][trs[u]]!=0) ++td;
        if(td > md) {
            md = td;
            pivot = e;
        }
    }
    if(md!=0) {
        assert(pivot != -1);
        for(ui i = 0; i < R.size(); ++i) if(Matrix[trs[R[i]]][trs[pivot]]!=0) branchf[i]=1;
    }
#endif
    for(ui i = 0; i < R.size(); ++i) {
        if(branchf[i]==1) {
            skipR.push_back(R[i]);
            continue;
        }
        ui u = R[i];
        C.push_back(u);
        vector<ui> tR;
        for(ui j = i+1; j < R.size(); ++j) if(Matrix[trs[R[j]]][trs[u]]!=0) tR.push_back(R[j]);
        for(auto e : skipR) if(Matrix[trs[e]][trs[u]]!=0) tR.push_back(e);

        bnb_finding_maximum_gc(C, tR, target_gc_size);

        assert(C.back()==u);
        C.pop_back();

        if(max_gc_size >= target_gc_size) return;
    }
}

void maximum_generalized_clique_computation_Prog()
{
    Timer t;
    Timer tt;

    ss = 0;
    resnum = 0;
    max_gc_size = 0;
    res.clear();

    double t_heu = 0;
    double t_degen = 0;
    double t_simnei = 0;
    double t_construct_subgraph = 0;
    double t_build_matrix = 0;
    double t_color = 0;
    double t_bnb = 0;
    double t_clear = 0;

    tt.restart();
    max_gc_size = find_a_heu_gc();
    t_heu += (double)tt.elapsed() / CLOCKS_PER_SEC;

    cout<<"heu solu size = "<<max_gc_size<<endl;

    ui * peels = new ui[n];
    ui * vis = new ui[n];
    ui * core = new ui[n];
    ui * rid = new ui[n];

    tt.restart();
    compute_degeneracy_ordering_of_original_graph(peels,vis,core,rid);
    t_degen += (double)tt.elapsed() / CLOCKS_PER_SEC;

    memset(vis, 0, sizeof(ui)*n);
    trs = new ui[n];
    vector<vector<ui>> progress_sim_nei_list;
    progress_sim_nei_list.resize(n);
    ui * comnei_cnt = new ui[n];
    memset(comnei_cnt, 0, sizeof(ui)*n);


    vector<ui> sg_vs, sg_ve;
    sg_vs.resize(n);
    sg_ve.resize(n);
    vector<ui> sg_e;
    vector<ui> sg_deg;
    sg_deg.resize(n);
    ui gap = n/10;
    for(int i = n-1; i >=0; --i) {
        if((n-i)%gap==0)cout<<((n-i)*10)/gap<<"%,"<<flush;if(i==0)cout<<"100%"<<endl<<flush;
        ui u = peels[i];
        assert(vis[u]==0);
        vis[u]=1;

        vector<ui> StructNei, StructNei2;
        for(ui j = pstart[u]; j < pstart[u+1]; ++j) {
            if(rid[edges[j]] > rid[u]) {
                StructNei.push_back(edges[j]);
                assert(vis[edges[j]]==0);
                vis[edges[j]] = 1;
            }
            else {
                StructNei2.push_back(edges[j]);
                vis[edges[j]] = 1;
            }
        }


        vector<ui> SimNei;

        tt.restart();
        vector<ui> u_2hopnei;
        for(auto e : StructNei) {
            for(ui j = pstart[e]; j < pstart[e+1]; ++j) {
                ui v = edges[j];
                if(vis[v]==1) continue;
                if(vis[v]==0) {
                    u_2hopnei.push_back(v);
                    vis[v]=2;
                }
                assert(vis[v]==2);
                ++ comnei_cnt[v];
            }
        }
        for(auto e : StructNei2) {
            for(ui j = pstart[e]; j < pstart[e+1]; ++j) {
                ui v = edges[j];
                if(vis[v]==1) continue;
                if(vis[v]==0) {
                    u_2hopnei.push_back(v);
                    vis[v]=2;
                }
                assert(vis[v]==2);
                ++ comnei_cnt[v];
            }
        }
        for(auto e : u_2hopnei) {
            double sim_score = (double) comnei_cnt[e] / (degree[e] + degree[u] - comnei_cnt[e]);
            assert(comnei_cnt[e] > 0);
            if(sim_score >= epsi && comnei_cnt[e] >= ComNeiThre) {
                if(rid[e] > rid[u]) {
                    SimNei.push_back(e);
                    progress_sim_nei_list[u].push_back(e);
                    progress_sim_nei_list[e].push_back(u);
                }
                else {
                    assert(vis[e]==2);
                    vis[e]=0;
                }
            }
            else {
                assert(vis[e]==2);
                vis[e]=0;
            }
            comnei_cnt[e]=0;
        }
        for(auto e : StructNei2) {
            assert(vis[e]==1);
            vis[e]=0;
        }
        t_simnei += (double)tt.elapsed() / CLOCKS_PER_SEC;


#ifdef _CheckInfo_
        cout<<endl<<"@ "<<u<<endl;
        cout<<"StructNei : "; for(auto e : StructNei) cout<<e<<","; cout<<endl;
        cout<<"SimNei : "; for(auto e : SimNei) cout<<e<<","; cout<<endl;
        for(ui j = i+1; j < n; ++j) {
            ui v = peels[j];
            cout<<"\t "<<v<<" progressive_sim_nei_list : "; for(auto e : progress_sim_nei_list[v]) cout<<e<<","; cout<<endl;
        }
#endif

#ifdef _CostlyDebug_
        assert(vis[u]==1);
        for(auto e : StructNei) assert(vis[e]==1);
        for(auto e : SimNei) assert(vis[e]==2);
#endif

        if(1 + StructNei.size() + SimNei.size() <= max_gc_size) {
            vis[u]=0;
            for(auto e : StructNei) vis[e]=0;
            for(auto e : SimNei) vis[e]=0;
            continue;
        }

        tt.restart();

        construct_egosg_and_core_pruning(u, StructNei, SimNei, vis, sg_vs, sg_ve, sg_e, sg_deg, progress_sim_nei_list);
        t_construct_subgraph += (double)tt.elapsed() / CLOCKS_PER_SEC;

        if(vis[u] == 0) {
            for(auto e : StructNei) vis[e]=0;
            for(auto e : SimNei) vis[e]=0;
            continue;
        }

        tt.restart();

        ui md = StructNei.size() + SimNei.size();
        Matrix = new char*[md+1];
        for(int i = 0; i < md+1; i++) Matrix[i] = new char[md+1];
        build_matrix(u, StructNei, SimNei, vis, progress_sim_nei_list);
        t_build_matrix += (double)tt.elapsed() / CLOCKS_PER_SEC;

        vector<ui> C;
        C.push_back(u);

        vector<ui> R;
        for(auto e : StructNei) R.push_back(e);
        for(auto e : SimNei) R.push_back(e);

        #ifdef _Coloring_
        tt.restart();
        coloring_before_bnb(R, md+1);
        t_color += (double)tt.elapsed() / CLOCKS_PER_SEC;
        #endif

        tt.restart();
        bnb_finding_maximum_gc(C,R,max_gc_size+1);
        t_bnb += (double)tt.elapsed() / CLOCKS_PER_SEC;

        tt.restart();
        vis[u]=0;
        for(auto e : StructNei) vis[e]=0;
        for(auto e : SimNei) vis[e]=0;
        for(int i = 0; i < md+1; i++) {
            delete [] Matrix[i];
            Matrix[i] = nullptr;
        }
        delete [] Matrix;
        t_clear += (double)tt.elapsed() / CLOCKS_PER_SEC;

#ifdef _CostlyDebug_
        for(ui i = 0; i < n; ++i) assert(vis[i]==0);
        for(ui i = 0; i < n; ++i) assert(comnei_cnt[i]==0);
#endif

    }
    delete [] peels;
    delete [] vis;
    delete [] core;
    delete [] rid;
    delete [] comnei_cnt;

    cout<<"Max GC: "<<max_gc_size<<", search space: "<<ss<<endl;
#ifdef _CollectRes_
    sort(res[0].begin(),res[0].end());

#endif
    cout << fixed << setprecision(2);
    double total_time = (double)t.elapsed()/CLOCKS_PER_SEC;
    cout << "\tTime: "<<total_time<<"s"<<endl;
    cout << "\theu solution t = " << t_heu << " s,  " <<(double)t_heu/total_time*100<<" %"<< endl;
    cout << "\tdegeneracy t   = " << t_degen << " s,  " <<(double)t_degen/total_time*100<<" %"<< endl;
    cout << "\tsim nei t      = " << t_simnei << " s,  " <<(double)t_simnei/total_time*100<<" %"<< endl;
    cout << "\tconstruct sg t = " << t_construct_subgraph << " s,  " <<(double)t_construct_subgraph/total_time*100<<" %"<< endl;
    cout << "\tbuild matrix t = " << t_build_matrix << " s,  " <<(double)t_build_matrix/total_time*100<<" %"<< endl;
    cout << "\tcolor t        = " << t_color << " s,  " <<(double)t_color/total_time*100<<" %"<< endl;
    cout << "\tbnb t          = " << t_bnb << " s,  " <<(double)t_bnb/total_time*100<<" %"<< endl;
    cout << "\tcleanup t      = " << t_clear << " s,  " <<(double)t_clear/total_time*100<<" %"<< endl;

}

void maximum_generalized_clique_computation_by_psca()
{
    Timer t;
    Timer tt;

    ss = 0;
    resnum = 0;
    max_gc_size = 0;
    res.clear();

    double t_heu = 0;
    double t_degen = 0;
    double t_simnei = 0;
    double t_construct_subgraph = 0;
    double t_build_matrix = 0;
    double t_bnb = 0;
    double t_clear = 0;


    tt.restart();
    max_gc_size = find_a_heu_gc();
    t_heu += (double)tt.elapsed() / CLOCKS_PER_SEC;

    cout<<"heu solu size = "<<max_gc_size<<endl;

    ui * peels = new ui[n];
    ui * vis = new ui[n];
    ui * core = new ui[n];
    ui * rid = new ui[n];

    tt.restart();
    compute_degeneracy_ordering_of_original_graph(peels,vis,core,rid);
    t_degen += (double)tt.elapsed() / CLOCKS_PER_SEC;

    memset(vis, 0, sizeof(ui)*n);
    trs = new ui[n];

    vector<vector<ui>> progress_sim_nei_list;
    progress_sim_nei_list.resize(n);


    vector<ui> sg_vs, sg_ve;
    sg_vs.resize(n);
    sg_ve.resize(n);
    vector<ui> sg_e;
    vector<ui> sg_deg;
    sg_deg.resize(n);
    ui gap = n/10;
    int bingo = 0;
    for(int i = n-1; i >=0; --i) {
        if((n-i)%gap==0)cout<<((n-i)*10)/gap<<"%,"<<flush;if(i==0)cout<<"100%"<<endl<<flush;
        ui u = peels[i];
        assert(vis[u]==0);
        vis[u]=1;

        vector<ui> StructNei;
        for(ui j = pstart[u]; j < pstart[u+1]; ++j) {
            if(rid[edges[j]] > rid[u]) {
                StructNei.push_back(edges[j]);
                assert(vis[edges[j]]==0);
                vis[edges[j]] = 2;
            }
        }


        vector<ui> SimNei;

        tt.restart();
        for(ui j = i+1; j < n; ++j) if(vis[peels[j]]==0) {
            ui v = peels[j];
            assert(rid[v] > rid[u]);
            pair<double,ui> jsresult = js(u,v);
            if( jsresult.first >= epsi) {
                SimNei.push_back(v);
                vis[v] = 3;
                progress_sim_nei_list[u].push_back(v);
                progress_sim_nei_list[v].push_back(u);


            }
        }
        t_simnei += (double)tt.elapsed() / CLOCKS_PER_SEC;


#ifdef _CheckInfo_
        cout<<endl<<"@ "<<u<<endl;
        cout<<"StructNei : "; for(auto e : StructNei) cout<<e<<","; cout<<endl;
        cout<<"SimNei : "; for(auto e : SimNei) cout<<e<<","; cout<<endl;
        for(ui j = i+1; j < n; ++j) {
            ui v = peels[j];
            cout<<"\t "<<v<<" progressive_sim_nei_list : "; for(auto e : progress_sim_nei_list[v]) cout<<e<<","; cout<<endl;
        }
#endif

        if(1 + StructNei.size() + SimNei.size() <= max_gc_size) {
            vis[u]=0;
            for(auto e : StructNei) vis[e]=0;
            for(auto e : SimNei) vis[e]=0;
            continue;
        }

        tt.restart();

        construct_egosg_and_core_pruning(u, StructNei, SimNei, vis, sg_vs, sg_ve, sg_e, sg_deg, progress_sim_nei_list);
        t_construct_subgraph += (double)tt.elapsed() / CLOCKS_PER_SEC;

        if(vis[u] == 0) {
            for(auto e : StructNei) vis[e]=0;
            for(auto e : SimNei) vis[e]=0;
            continue;
        }

        tt.restart();

        ui md = StructNei.size() + SimNei.size();
        Matrix = new char*[md+1];
        for(int i = 0; i < md+1; i++) Matrix[i] = new char[md+1];
        build_matrix(u, StructNei, SimNei, vis, progress_sim_nei_list);
        t_build_matrix += (double)tt.elapsed() / CLOCKS_PER_SEC;

        vector<ui> C;
        C.push_back(u);

        vector<ui> R;
        for(auto e : StructNei) R.push_back(e);
        for(auto e : SimNei) R.push_back(e);

        tt.restart();
        bnb_finding_maximum_gc(C,R,max_gc_size+1);
        t_bnb += (double)tt.elapsed() / CLOCKS_PER_SEC;

        tt.restart();
        vis[u]=0;
        for(auto e : StructNei) vis[e]=0;
        for(auto e : SimNei) vis[e]=0;
        for(int i = 0; i < md+1; i++) {
            delete [] Matrix[i];
            Matrix[i] = nullptr;
        }
        delete [] Matrix;
        t_clear += (double)tt.elapsed() / CLOCKS_PER_SEC;
    }
    delete [] peels;
    delete [] vis;
    delete [] core;
    delete [] rid;

    cout<<"Max GC: "<<max_gc_size<<", search space: "<<ss<<endl;
#ifdef _CollectRes_
    sort(res[0].begin(),res[0].end());
    cout<<"Res members: "; for(auto e : res[0]) cout<<e<<","; cout<<endl;
#endif
    cout << fixed << setprecision(2);
    double total_time = (double)t.elapsed()/CLOCKS_PER_SEC;
    cout << "Time: "<<total_time<<"s"<<endl;
    cout << "\theu solution t = " << t_heu << " s,  " <<(double)t_heu/total_time*100<<" %"<< endl;
    cout << "\tdegeneracy t   = " << t_degen << " s,  " <<(double)t_degen/total_time*100<<" %"<< endl;
    cout << "\tsim nei t      = " << t_simnei << " s,  " <<(double)t_simnei/total_time*100<<" %"<< endl;
    cout << "\tconstruct sg t = " << t_construct_subgraph << " s,  " <<(double)t_construct_subgraph/total_time*100<<" %"<< endl;
    cout << "\tbuild matrix t = " << t_build_matrix << " s,  " <<(double)t_build_matrix/total_time*100<<" %"<< endl;
    cout << "\tbnb t          = " << t_bnb << " s,  " <<(double)t_bnb/total_time*100<<" %"<< endl;
    cout << "\tcleanup t      = " << t_clear << " s,  " <<(double)t_clear/total_time*100<<" %"<< endl;
    cout<<"bingo="<<bingo<<endl;
}

void release_mem()
{
    if(pstart != nullptr) delete [] pstart;
    if(edges != nullptr) delete [] edges;
    if(f_edges != nullptr) delete [] f_edges;
    if(degree != nullptr) delete [] degree;
    if(oid_mapping != nullptr) delete [] oid_mapping;
    if(s_pstart != nullptr) delete [] s_pstart;
    if(s_pend != nullptr) delete [] s_pend;
    if(s_edges != nullptr) delete [] s_edges;
    if(s_degree != nullptr) delete [] s_degree;
    if(trs != nullptr) delete [] trs;
}

void check_correctness_of_res(string dir, string name, double epsi, int size)
{
    cout<<"check_correctness_of_res!"<<endl;
#ifndef _CollectRes_
    cout<<"NOT define _CollectRes_"<<endl;
    return;
#endif
    ui test_n, test_m;
    ui * test_pstart;
    ui * test_edges;
    ui * test_degree;


    FILE *f = Utility::open_file((dir + "/" + name + "/b_degree.bin").c_str(), "rb");

    ui tt;
    fread(&tt, sizeof(ui), 1, f);
    if(tt != sizeof(ui)) {
        printf("sizeof ui is different: edge.bin(%d), machine(%d)\n", tt, (ui)sizeof(ui));
        return ;
    }
    fread(&test_n, sizeof(ui), 1, f);
    fread(&test_m, sizeof(ui), 1, f);
    test_degree = new ui[test_n];
    fread(test_degree, sizeof(ui), test_n, f);
    fclose(f);

    f = Utility::open_file((dir + "/" + name + "/b_adj.bin").c_str(), "rb");

    test_pstart = new ui[test_n+1];
    test_edges = new ui[test_m];

    test_pstart[0] = 0;
    for(ui i = 0;i < test_n;i ++) {
        if(test_degree[i] > 0) fread(test_edges+test_pstart[i], sizeof(ui), test_degree[i], f);
        else exit(1);
        test_pstart[i+1] = test_pstart[i] + test_degree[i];
    }
    fclose(f);

    vector<unordered_set<ui> > original_G;
    original_G.resize(test_n);

    for(ui u = 0; u < test_n; ++u) {
        for(ui i = test_pstart[u]; i < test_pstart[u+1]; ++i) {
            ui v = test_edges[i];
            original_G[u].insert(v);
        }
    }

    for(auto &each_clique : res) {
        ui total_similar_edge_number = 0;

        for(ui i = 0; i < each_clique.size(); ++i) {
            ui u = each_clique[i];
            ui u_original_nei_cnt = 0;
            ui u_similar_nei_cnt = 0;

            for(ui j = i+1; j < each_clique.size(); ++j) {
                ui v = each_clique[j];
                if(original_G[u].find(v) != original_G[u].end()) {
                    ++ u_original_nei_cnt;
                }
                else {

                    vector<ui> unei, vnei;
                    for(ui k = test_pstart[u]; k < test_pstart[u+1]; ++k) unei.push_back(test_edges[k]);
                    for(ui k = test_pstart[v]; k < test_pstart[v+1]; ++k) vnei.push_back(test_edges[k]);
                    sort(unei.begin(), unei.end());
                    sort(vnei.begin(), vnei.end());
                    int cn_uv = 0;
                    ui a = 0, b = 0;
                    while (a < unei.size() && b < vnei.size()) {
                        if (unei[a] == vnei[b]) {
                            ++cn_uv;
                            ++a; ++b;
                        } else if (unei[a] < vnei[b]) {
                            ++a;
                        } else {
                            ++b;
                        }
                    }
                    double score = (double) cn_uv / (unei.size() + vnei.size() - cn_uv);
                    if(score < epsi) {
                        cout<<"score < epsi"<<endl;
                        exit(1);
                    }
                    ++ u_similar_nei_cnt;
                }
            }
            if((u_original_nei_cnt+u_similar_nei_cnt) != (each_clique.size() - i - 1) ) {
                cout<<"(u_original_nei_cnt+u_similar_nei_cnt) != (each_clique.size() - i - 1)"<<endl;
                exit(1);
            }
            total_similar_edge_number += u_similar_nei_cnt;
        }

        int this_clique_e_number = each_clique.size() * (each_clique.size() - 1) / 2;
        double similar_e_ratio = (double) total_similar_edge_number / this_clique_e_number;
    }

    delete [] test_edges;
    delete [] test_pstart;
    delete [] test_degree;
}

void write_res_to_disk(string dir, string name, double para_a, int para_b)
{
    cout<<"write_res_to_disk!"<<endl;
#ifndef _CollectRes_
    cout<<"NOT define _CollectRes_"<<endl;
    return;
#endif

    ui test_n, test_m;
    ui * test_pstart;
    ui * test_edges;
    ui * test_degree;


    FILE *f = Utility::open_file((dir + "/" + name + "/b_degree.bin").c_str(), "rb");

    ui tt;
    fread(&tt, sizeof(ui), 1, f);
    if(tt != sizeof(ui)) {
        printf("sizeof ui is different: edge.bin(%d), machine(%d)\n", tt, (ui)sizeof(ui));
        return ;
    }
    fread(&test_n, sizeof(ui), 1, f);
    fread(&test_m, sizeof(ui), 1, f);
    test_degree = new ui[test_n];
    fread(test_degree, sizeof(ui), test_n, f);
    fclose(f);

    f = Utility::open_file((dir + "/" + name + "/b_adj.bin").c_str(), "rb");

    test_pstart = new ui[test_n+1];
    test_edges = new ui[test_m];

    test_pstart[0] = 0;
    for(ui i = 0;i < test_n;i ++) {
        if(test_degree[i] > 0) fread(test_edges+test_pstart[i], sizeof(ui), test_degree[i], f);
        else exit(1);
        test_pstart[i+1] = test_pstart[i] + test_degree[i];
    }
    fclose(f);

    vector<unordered_set<ui> > original_G;
    original_G.resize(test_n);

    for(ui u = 0; u < test_n; ++u) {
        for(ui i = test_pstart[u]; i < test_pstart[u+1]; ++i) {
            ui v = test_edges[i];
            original_G[u].insert(v);
        }
    }


    long long total_clique_number = res.size();
    long long having_se_clique_number = 0;
    ui maximum_size = 0;
    ui minimum_size = test_n;
    double largest_se_ratio = 0;
    double smallest_se_ratio = 1;
    long long maximum_clique_number = 0;
    long long having_se_maximum_clique_number = 0;
    vector<int> having_se_flag;
    having_se_flag.resize(total_clique_number);

    string out_dir = "./outputfile";
    std::filesystem::create_directory(out_dir);

    ofstream outf;
    string res_file = ("./outputfile/" + name + "_" + to_string(para_a)+"_"+to_string(para_b)+"_detail.txt");
    outf.open(res_file);
    if(!outf) {cout<<"cannot open res_file!"; exit(1);}
    outf<<"Total : "<<res.size()<<endl;
    long long ccnt = 0;

    for(auto &each_clique : res) {
        vector<pair<ui,ui>> similar_edges_vec;
        sort(each_clique.begin(), each_clique.end());
        for(ui i = 0; i < each_clique.size(); ++i) {
            ui u = each_clique[i];
            for(ui j = i+1; j < each_clique.size(); ++j) {
                ui v = each_clique[j];
                if(original_G[u].find(v) == original_G[u].end()) {
                    similar_edges_vec.push_back(make_pair(u, v));
                }
            }
        }
        if(!similar_edges_vec.empty()) {
            ++having_se_clique_number;
            having_se_flag[ccnt] = 1;
        }
        else {
            having_se_flag[ccnt] = 0;
        }
        if(each_clique.size() > maximum_size) maximum_size = each_clique.size();
        if(each_clique.size() < minimum_size) minimum_size = each_clique.size();

        int total_e = each_clique.size() * (each_clique.size() - 1) / 2;
        double se_ratio = (double) similar_edges_vec.size() / total_e;

        if(se_ratio > largest_se_ratio) largest_se_ratio = se_ratio;
        if(se_ratio < smallest_se_ratio) smallest_se_ratio = se_ratio;

        outf<<endl<<"#Clique:"<<ccnt+1<<", #Size:"<<each_clique.size()<<", #SEratio:"<<se_ratio<<endl;

        outf<<"#Member:";
        for(auto e : each_clique) outf<<e<<", "; outf<<endl;
        outf<<"#SimEdge:";
        for(auto e : similar_edges_vec) outf<<"("<<e.first<<","<<e.second<<"), "; outf<<endl;
        ++ccnt;
    }
    outf.close();


    ccnt = 0;
    for(auto &each_clique : res) {
        if(each_clique.size() == maximum_size) {
            ++ maximum_clique_number;
            if(having_se_flag[ccnt] == 1) ++ having_se_maximum_clique_number;
        }
        ++ccnt;
    }
    assert(maximum_clique_number > 0 && having_se_maximum_clique_number <= maximum_clique_number);

    res_file = ("./outputfile/" + name + "_" + to_string(para_a)+ "_" + to_string(para_b)+"_abstract.txt");
    outf.open(res_file);
    if(!outf) {cout<<"cannot open res_file!"; exit(1);}
    outf<<"total_clique_number : "<<total_clique_number<<endl;
    outf<<"having_se_clique_number : "<<having_se_clique_number<<endl;
    outf<<"ratio : "<<(double)having_se_clique_number/total_clique_number<<endl;
    outf<<"size range : ["<<minimum_size<<", "<<maximum_size<<"]"<<endl;
    outf<<"se ratio range : ["<<smallest_se_ratio<<", "<<largest_se_ratio<<"]"<<endl;
    outf<<"maximum_clique_number : "<<maximum_clique_number<<endl;
    outf<<"having_se_maximum_clique_number : "<<having_se_maximum_clique_number<<endl;
    outf.close();

    delete [] test_edges;
    delete [] test_pstart;
    delete [] test_degree;
}

void show_abstract_res(string dir, string name)
{
#ifndef _CollectRes_
    cout<<"NOT define _CollectRes_"<<endl;
    return;
#endif

    ui test_n, test_m;
    ui * test_pstart;
    ui * test_edges;
    ui * test_degree;


    FILE *f = Utility::open_file((dir + "/" + name + "/b_degree.bin").c_str(), "rb");

    ui tt;
    fread(&tt, sizeof(ui), 1, f);
    if(tt != sizeof(ui)) {
        printf("sizeof ui is different: edge.bin(%d), machine(%d)\n", tt, (ui)sizeof(ui));
        return ;
    }
    fread(&test_n, sizeof(ui), 1, f);
    fread(&test_m, sizeof(ui), 1, f);
    test_degree = new ui[test_n];
    fread(test_degree, sizeof(ui), test_n, f);
    fclose(f);

    f = Utility::open_file((dir + "/" + name + "/b_adj.bin").c_str(), "rb");

    test_pstart = new ui[test_n+1];
    test_edges = new ui[test_m];

    test_pstart[0] = 0;
    for(ui i = 0;i < test_n;i ++) {
        if(test_degree[i] > 0) fread(test_edges+test_pstart[i], sizeof(ui), test_degree[i], f);
        else exit(1);
        test_pstart[i+1] = test_pstart[i] + test_degree[i];
    }
    fclose(f);

    vector<unordered_set<ui> > original_G;
    original_G.resize(test_n);

    for(ui u = 0; u < test_n; ++u) {
        for(ui i = test_pstart[u]; i < test_pstart[u+1]; ++i) {
            ui v = test_edges[i];
            original_G[u].insert(v);
        }
    }


    long long total_clique_number = res.size();
    long long having_se_clique_number = 0;
    ui maximum_size = 0;
    ui minimum_size = test_n;
    double largest_se_ratio = 0;
    double smallest_se_ratio = 1;
    long long maximum_clique_number = 0;
    long long having_se_maximum_clique_number = 0;
    vector<int> having_se_flag;
    having_se_flag.resize(total_clique_number);

    long long ccnt = 0;

    for(auto &each_clique : res) {
        vector<pair<ui,ui>> similar_edges_vec;
        sort(each_clique.begin(), each_clique.end());
        for(ui i = 0; i < each_clique.size(); ++i) {
            ui u = each_clique[i];
            for(ui j = i+1; j < each_clique.size(); ++j) {
                ui v = each_clique[j];
                if(original_G[u].find(v) == original_G[u].end()) {
                    similar_edges_vec.push_back(make_pair(u, v));
                }
            }
        }
        if(!similar_edges_vec.empty()) {
            ++having_se_clique_number;
            having_se_flag[ccnt] = 1;
        }
        else {
            having_se_flag[ccnt] = 0;
        }
        if(each_clique.size() > maximum_size) maximum_size = each_clique.size();
        if(each_clique.size() < minimum_size) minimum_size = each_clique.size();

        int total_e = each_clique.size() * (each_clique.size() - 1) / 2;
        double se_ratio = (double) similar_edges_vec.size() / total_e;

        if(se_ratio > largest_se_ratio) largest_se_ratio = se_ratio;
        if(se_ratio < smallest_se_ratio) smallest_se_ratio = se_ratio;

        ++ccnt;
    }

    ccnt = 0;
    for(auto &each_clique : res) {
        if(each_clique.size() == maximum_size) {
            ++ maximum_clique_number;
            if(having_se_flag[ccnt] == 1) ++ having_se_maximum_clique_number;
        }
        ++ccnt;
    }
    assert(maximum_clique_number > 0 && having_se_maximum_clique_number <= maximum_clique_number);

    cout<<"\t Pure GC NUM  : "<<total_clique_number<<",    ["<<minimum_size<<" ~ "<<maximum_size<<"]"<<endl;
    cout<<"\t SE GC NUM    : "<<having_se_clique_number<<",    ["<<smallest_se_ratio<<" ~ "<<largest_se_ratio<<"]"<<endl;
    cout<<"\t SE GC Ratio  : "<<(double)having_se_clique_number/total_clique_number<<endl;
    cout<<"\t MAX GC NUM   : "<<maximum_clique_number<<endl;
    cout<<"\t SE MAX GC NUM: "<<having_se_maximum_clique_number<<endl;

    delete [] test_edges;
    delete [] test_pstart;
    delete [] test_degree;
}

string format_double(double value, int precision = 6)
{
    ostringstream oss;
    oss << fixed << setprecision(precision) << value;

    string s = oss.str();


    while(!s.empty() && s.back() == '0') s.pop_back();


    if(!s.empty() && s.back() == '.') s.pop_back();


    replace(s.begin(), s.end(), '.', 'p');

    return s;
}

void load_index(string graph_name, string index_name, vector<vector<pair<double,ui>>> &residual_sim_nei, vector<vector<ui>> &z_list, ui &z_idx, vector<vector<pair<double,ui>>> &z_R, int cfg_tau, int cfg_maxr, ui cfg_k, ui cfg_bands, double cfg_threshold, double cfg_rho, ui cfg_min_cluster_size, ui cfg_min_gain)
{
    string config_name;

    config_name += "tau" + to_string(cfg_tau);
    config_name += "_maxr" + to_string(cfg_maxr);

    config_name += "_k" + to_string(cfg_k);
    config_name += "_b" + to_string(cfg_bands);

    config_name += "_th" + format_double(cfg_threshold);
    config_name += "_rho" + format_double(cfg_rho);

    config_name += "_mc" + to_string(cfg_min_cluster_size);
    config_name += "_mg" + to_string(cfg_min_gain);

    string file_a = "./index/" + graph_name + "_" + config_name + "_" + index_name + "a.bin";
    string file_b = "./index/" + graph_name + "_" + config_name + "_" + index_name + "b.bin";

    cout<<"load index file : "<<file_a<<endl;

    FILE * f = Utility::open_file(file_a.c_str(), "rb");

    residual_sim_nei.resize(n);
    z_list.resize(n);

    ui total_n;
    ui num;
    char score;
    ui nei, znei;
    fread(&total_n, sizeof(ui), 1, f);
    if(total_n != n ) {
        cout<<"total_n != n"<<endl;
        exit(1);
    }
    for(ui i = 0; i < total_n; ++i) {

        fread(&num, sizeof(ui), 1, f);
        for(ui j = 0; j < num; ++j) {
            fread(&score, sizeof(char), 1, f);
            fread(&nei, sizeof(ui), 1, f);
            residual_sim_nei[i].push_back(make_pair(((double)score)/100, nei));
        }

        fread(&num, sizeof(ui), 1, f);
        for(ui j = 0; j < num; ++j) {
            fread(&znei, sizeof(ui), 1, f);
            z_list[i].push_back(znei);
        }
    }
    fclose(f);

    f = Utility::open_file(file_b.c_str(), "rb");
    fread(&z_idx, sizeof(ui), 1, f);
    z_R.resize(z_idx);
    for(ui i = 0; i < z_idx; ++i) {
        fread(&num, sizeof(ui), 1, f);
        for(ui j = 0; j < num; ++j) {
            fread(&score, sizeof(char), 1, f);
            fread(&nei, sizeof(ui), 1, f);
            z_R[i].push_back(make_pair(((double)score)/100, nei));
        }
    }
}

void load_index_bc(string graph_name, string index_name, vector<vector<pair<double,ui>>> &residual_sim_nei, vector<vector<ui>> &z_list, ui &z_idx, vector<vector<pair<double,ui>>> &z_R, int cfg_tau, int cfg_maxr, ui cfg_min_cluster_size, ui cfg_min_gain)
{
    string config_name;

    config_name += "tau" + to_string(cfg_tau);
    config_name += "_maxr" + to_string(cfg_maxr);

    config_name += "_mc" + to_string(cfg_min_cluster_size);
    config_name += "_mg" + to_string(cfg_min_gain);

    string file_a = "./index/" + graph_name + "_" + config_name + "_" + index_name + "a.bin";
    string file_b = "./index/" + graph_name + "_" + config_name + "_" + index_name + "b.bin";

    cout<<"load index file : "<<file_a<<endl;

    FILE * f = Utility::open_file(file_a.c_str(), "rb");

    residual_sim_nei.resize(n);
    z_list.resize(n);

    ui total_n;
    ui num;
    char score;
    ui nei, znei;
    fread(&total_n, sizeof(ui), 1, f);
    if(total_n != n ) {
        cout<<"total_n != n"<<endl;
        exit(1);
    }
    for(ui i = 0; i < total_n; ++i) {

        fread(&num, sizeof(ui), 1, f);
        for(ui j = 0; j < num; ++j) {
            fread(&score, sizeof(char), 1, f);
            fread(&nei, sizeof(ui), 1, f);
            residual_sim_nei[i].push_back(make_pair(((double)score)/100, nei));
        }

        fread(&num, sizeof(ui), 1, f);
        for(ui j = 0; j < num; ++j) {
            fread(&znei, sizeof(ui), 1, f);
            z_list[i].push_back(znei);
        }
    }
    fclose(f);

    f = Utility::open_file(file_b.c_str(), "rb");
    fread(&z_idx, sizeof(ui), 1, f);
    z_R.resize(z_idx);
    for(ui i = 0; i < z_idx; ++i) {
        fread(&num, sizeof(ui), 1, f);
        for(ui j = 0; j < num; ++j) {
            fread(&score, sizeof(char), 1, f);
            fread(&nei, sizeof(ui), 1, f);
            z_R[i].push_back(make_pair(((double)score)/100, nei));
        }
    }
}

void load_index(string graph_name, string index_name, double alpha, vector<vector<pair<double,ui>>> &residual_sim_nei, vector<vector<ui>> &z_list, ui &z_idx, vector<vector<pair<double,ui>>> &z_R)
{
    string index_file = "./index/" + graph_name + "_" + to_string((int)(alpha*100)) + "_" + index_name + "a.bin";

    cout<<"load index file : "<<index_file<<endl;

    FILE * f = Utility::open_file(index_file.c_str(), "rb");

    residual_sim_nei.resize(n);
    z_list.resize(n);

    ui total_n;
    ui num;
    char score;
    ui nei, znei;
    fread(&total_n, sizeof(ui), 1, f);
    if(total_n != n ) {
        cout<<"total_n != n"<<endl;
        exit(1);
    }
    for(ui i = 0; i < total_n; ++i) {

        fread(&num, sizeof(ui), 1, f);

        for(ui j = 0; j < num; ++j) {
            fread(&score, sizeof(char), 1, f);
            fread(&nei, sizeof(ui), 1, f);


            residual_sim_nei[i].push_back(make_pair(((double)score)/100, nei));
        }

        fread(&num, sizeof(ui), 1, f);

        for(ui j = 0; j < num; ++j) {
            fread(&znei, sizeof(ui), 1, f);

            z_list[i].push_back(znei);
        }
    }
    fclose(f);

    index_file.erase(index_file.end() - 5, index_file.end());
    index_file.append("b.bin");
    f = Utility::open_file(index_file.c_str(), "rb");

    fread(&z_idx, sizeof(ui), 1, f);
    z_R.resize(z_idx);

    for(ui i = 0; i < z_idx; ++i) {
        fread(&num, sizeof(ui), 1, f);

        for(ui j = 0; j < num; ++j) {
            fread(&score, sizeof(char), 1, f);
            fread(&nei, sizeof(ui), 1, f);


            z_R[i].push_back(make_pair(((double)score)/100, nei));
        }
    }

    cout<<"finish loading index"<<endl;


}

void vertex_reduction_by_index(
    ui* tmp_pstart,
    ui* tmp_edges,
    ui* tmp_degree,
    vector<vector<pair<double,ui>>>& residual_sim_nei,
    vector<vector<ui>>& z_list,
    ui& z_idx,
    vector<vector<pair<double,ui>>>& z_R,
    ui* del)
{
    const ui original_n = n;
    const ui original_m = m;
    const ui thre = (ui)max_gc_size;

    if(original_n == 0 || thre < 1) return;

    memset(del, 0, sizeof(ui) * original_n);


    vector<ui> candidate_mark(original_n, 0);
    ui token = 0;

    auto obtain_new_token = [&]() -> ui {
        ++token;

        if(token == 0) {
            fill(candidate_mark.begin(), candidate_mark.end(), 0);
            token = 1;
        }

        return token;
    };


    auto can_be_similar_by_degree = [&](ui u, ui v) -> bool {
        if(u == v) return false;

        ui du = degree[u];
        ui dv = degree[v];

        if(du == 0 || dv == 0) return false;

        ui min_degree = min(du, dv);
        ui max_degree = max(du, dv);

        if(min_degree < (ui)ComNeiThre) return false;

        if((double)min_degree / (double)max_degree < epsi) {
            return false;
        }

        return true;
    };

    unsigned long long duplicate_candidate_cnt = 0;
    unsigned long long degree_filter_cnt = 0;


    for(ui u = 0; u < original_n; ++u) {
        ui current_token = obtain_new_token();
        ui degree_ub = 0;

        candidate_mark[u] = current_token;


        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];

            assert(v < original_n);

            if(v == u) continue;

            if(candidate_mark[v] != current_token) {
                candidate_mark[v] = current_token;
                ++degree_ub;
            }
        }


        for(const auto& simnei : residual_sim_nei[u]) {
            double score = simnei.first;
            ui v = simnei.second;

            if(score < epsi) break;

            assert(v < original_n);

            if(v == u) continue;

            if(candidate_mark[v] == current_token) {
                ++duplicate_candidate_cnt;
                continue;
            }

            candidate_mark[v] = current_token;
            ++degree_ub;
        }


        for(ui z : z_list[u]) {
            assert(z < z_idx);
            assert(z < z_R.size());

            for(const auto& nei : z_R[z]) {
                double upper_score = nei.first;
                ui v = nei.second;

                if(upper_score < epsi) break;

                assert(v < original_n);

                if(v == u) continue;


                if(candidate_mark[v] == current_token) {
                    ++duplicate_candidate_cnt;
                    continue;
                }

                candidate_mark[v] = current_token;

                if(!can_be_similar_by_degree(u, v)) {
                    ++degree_filter_cnt;
                    continue;
                }

                ++degree_ub;
            }
        }

        assert(degree_ub <= original_n - 1);
        tmp_degree[u] = degree_ub;
    }


    auto perform_peeling = [&](queue<ui>& Q) -> ui {
        ui deleted_cnt = 0;

        while(!Q.empty()) {
            ui u = Q.front();
            Q.pop();


            if(del[u] != 0) continue;

            assert(tmp_degree[u] < thre);

            del[u] = 1;
            ++deleted_cnt;

            for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
                ui v = tmp_edges[i];

                if(del[v] != 0) continue;


                if(tmp_degree[v] == 0) continue;


                if(tmp_degree[v] == thre) {
                    --tmp_degree[v];
                    Q.push(v);
                }
                else {
                    --tmp_degree[v];
                }
            }
        }

        return deleted_cnt;
    };


    queue<ui> Q;

    for(ui u = 0; u < original_n; ++u) {
        if(tmp_degree[u] < thre) {
            Q.push(u);
        }
    }

    ui initial_deleted_cnt = perform_peeling(Q);


    auto compute_exact_live_gc_degree = [&](ui u) -> ui {
        ui current_token = obtain_new_token();
        ui exact_degree = 0;

        candidate_mark[u] = current_token;


        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];

            if(v == u || del[v] != 0) continue;

            if(candidate_mark[v] != current_token) {
                candidate_mark[v] = current_token;
                ++exact_degree;
            }
        }


        for(const auto& simnei : residual_sim_nei[u]) {
            double score = simnei.first;
            ui v = simnei.second;

            if(score < epsi) break;

            if(v == u || del[v] != 0) continue;

            if(candidate_mark[v] == current_token) continue;

            candidate_mark[v] = current_token;
            ++exact_degree;
        }


        for(ui z : z_list[u]) {
            assert(z < z_idx);
            assert(z < z_R.size());

            for(const auto& nei : z_R[z]) {
                double upper_score = nei.first;
                ui v = nei.second;

                if(upper_score < epsi) break;

                if(v == u || del[v] != 0) continue;


                if(candidate_mark[v] == current_token) continue;

                candidate_mark[v] = current_token;

                if(!can_be_similar_by_degree(u, v)) continue;

                auto jsp = js(u, v);

                if(jsp.first >= epsi) {
                    ++exact_degree;
                }
            }
        }

        return exact_degree;
    };


    ui refine_gap = max(thre, (ui)128);

    unsigned long long refine_upper_64 =
        (unsigned long long)thre +
        (unsigned long long)refine_gap;

    ui refine_upper;

    if(refine_upper_64 >= original_n) {
        refine_upper = original_n - 1;
    }
    else {
        refine_upper = (ui)refine_upper_64;
    }


    const ui MAX_REFINE_ROUND = 2;

    unsigned long long refined_vertex_cnt = 0;
    ui refinement_deleted_cnt = 0;

    for(ui round = 0; round < MAX_REFINE_ROUND; ++round) {
        queue<ui> refine_Q;

        for(ui u = 0; u < original_n; ++u) {
            if(del[u] != 0) continue;


            if(tmp_degree[u] > refine_upper) continue;

            ++refined_vertex_cnt;

            ui exact_degree =
                compute_exact_live_gc_degree(u);


            tmp_degree[u] = exact_degree;

            if(exact_degree < thre) {
                refine_Q.push(u);
            }
        }

        if(refine_Q.empty()) break;

        ui round_deleted_cnt =
            perform_peeling(refine_Q);

        refinement_deleted_cnt +=
            round_deleted_cnt;

        if(round_deleted_cnt == 0) break;
    }


    ui new_n = 0;

    for(ui u = 0; u < original_n; ++u) {
        if(del[u] == 0) {
            oid_mapping[new_n] = u;
            newid_mapping[u] = new_n;
            ++new_n;
        }
    }

    ui* t_pstart = new ui[original_n + 1];
    ui* t_edges = new ui[original_m];

    ui edge_pos = 0;
    ui new_u = 0;

    t_pstart[0] = 0;

    for(ui original_u = 0;
        original_u < original_n;
        ++original_u) {

        if(del[original_u] != 0) continue;

        assert(oid_mapping[new_u] ==
               original_u);

        for(ui i = tmp_pstart[original_u];
            i < tmp_pstart[original_u+1];
            ++i) {

            ui original_v = tmp_edges[i];

            if(del[original_v] == 0) {
                t_edges[edge_pos++] =
                    newid_mapping[original_v];
            }
        }

        ++new_u;
        t_pstart[new_u] = edge_pos;
    }

    assert(new_u == new_n);
    assert(edge_pos % 2 == 0);


    memcpy(
        tmp_pstart,
        t_pstart,
        sizeof(ui) * (new_n + 1)
    );

    if(edge_pos > 0) {
        memcpy(
            tmp_edges,
            t_edges,
            sizeof(ui) * edge_pos
        );
    }

    delete [] t_pstart;
    delete [] t_edges;

    n = new_n;
    m = edge_pos;


    for(ui u = 0; u < n; ++u) {
        tmp_degree[u] =
            tmp_pstart[u+1] -
            tmp_pstart[u];
    }

    cout << "index VR details:"
         << " initial deleted = "
         << initial_deleted_cnt
         << ", refinement checks = "
         << refined_vertex_cnt
         << ", refinement deleted = "
         << refinement_deleted_cnt
         << ", duplicate candidates = "
         << duplicate_candidate_cnt
         << ", degree-filtered candidates = "
         << degree_filter_cnt
         << endl;
}

void vertex_reduction_by_zindex(ui* tmp_pstart, ui* tmp_edges, ui* tmp_degree, vector<vector<pair<double,ui>>> &residual_sim_nei, vector<vector<ui>> &z_list, ui &z_idx, vector<vector<pair<double,ui>>> &z_R, ui * del)
{
    int thre = max_gc_size;
    if(thre < 1) return;

    for(ui u = 0; u < n; ++u) {
        int extra_deg = 0;
        for(auto simnei : residual_sim_nei[u]) {
            if(simnei.first >= epsi) {
                ++ extra_deg;
            }
            else break;
        }
        for(ui z : z_list[u]) {
            for(auto nei : z_R[z]) {
                if(nei.first >= epsi) {
                    if(nei.second==u) continue;
                    if((double)min(degree[u], degree[nei.second]) / max(degree[u], degree[nei.second]) < epsi) continue;
                    ++ extra_deg;
                }
                else break;
            }
        }
        tmp_degree[u] += extra_deg;
    }

    queue<ui> Q;

    for(ui u = 0; u < n; ++u) if(tmp_degree[u]<thre) Q.push(u);

    memset(del, 0, sizeof(ui)*n);
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        assert(del[u]==0);
        del[u]=1;
        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];
            if(del[v]==1) continue;
            assert(tmp_degree[v]>0);
            if(tmp_degree[v]--==thre) Q.push(v);
        }
    }


    ui newid = 0;
    for(ui u = 0; u < n; ++u) if(del[u]==0) {
        oid_mapping[newid]=u;
        newid_mapping[u] = newid;
        ++newid;
    }


    ui * t_pstart = new ui[n+1];
    ui * t_edges = new ui[m];

    ui pos;
    ui id_idx=0;
    t_pstart[id_idx] = 0;
    for(ui u =0; u < n; ++u) if(del[u]==0) {
        assert(oid_mapping[id_idx]==u);
        pos = t_pstart[id_idx++];
        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) if(del[tmp_edges[i]]==0) {
            t_edges[pos++] = newid_mapping[tmp_edges[i]];
        }
        t_pstart[id_idx] = pos;
    }
    assert(id_idx==newid);


    memcpy(tmp_pstart, t_pstart, sizeof(ui)*(n+1));
    memcpy(tmp_edges, t_edges, sizeof(ui)*m);
    delete [] t_pstart;
    delete [] t_edges;

    n = id_idx;
    m = 0;
    for(ui i = 0; i < n; ++i) {
        tmp_degree[i] = tmp_pstart[i+1] - tmp_pstart[i];
        m += tmp_degree[i];
    }
    assert(m%2==0);
}

void build_egosg_and_vr(
    ui root,
    ui* tmp_pstart,
    ui* tmp_edges,
    ui* tmp_degree,
    vector<ui>& StructNei,
    ui* vis,
    vector<ui>& sg_vs,
    vector<ui>& sg_ve,
    vector<ui>& sg_e,
    vector<ui>& sg_deg,
    vector<vector<ui>>& progress_sim_nei)
{


    (void)tmp_degree;

    assert(vis[root] != 0);


    sg_e.clear();

    ui pos = 0;

    for(ui v : StructNei) {
        assert(vis[v] != 0);

        sg_vs[v] = pos;


        for(ui i = tmp_pstart[v]; i < tmp_pstart[v+1]; ++i) {
            ui w = tmp_edges[i];

            if(vis[w] != 0) {
                sg_e.push_back(w);
                ++pos;
            }
        }


        for(ui w : progress_sim_nei[v]) {
            if(vis[w] != 0) {
                sg_e.push_back(w);
                ++pos;
            }
        }

        sg_ve[v] = pos;

        assert(sg_ve[v] >= sg_vs[v]);

        sg_deg[v] =
            sg_ve[v] - sg_vs[v];
    }

    const ui threshold = (ui)max_gc_size;


    if(threshold == 0) return;


    if(sg_deg[root] < threshold) {
        vis[root] = 0;
        return;
    }


    vector<ui> peel_queue;
    peel_queue.reserve(StructNei.size());

    for(ui v : StructNei) {
        if(v != root && sg_deg[v] < threshold) {
            peel_queue.push_back(v);
        }
    }

    size_t queue_head = 0;


    while(queue_head < peel_queue.size()) {
        ui u = peel_queue[queue_head++];


        if(vis[u] == 0) continue;

        assert(sg_deg[u] < threshold);

        vis[u] = 0;


        for(ui i = sg_vs[u]; i < sg_ve[u]; ++i) {
            ui v = sg_e[i];

            if(vis[v] == 0) continue;

            assert(sg_deg[v] > 0);

            ui old_degree = sg_deg[v];
            --sg_deg[v];


            if(old_degree == threshold) {


                if(v == root) {
                    vis[root] = 0;
                    return;
                }

                peel_queue.push_back(v);
            }
        }
    }


    ui write_pos = 0;

    for(ui v : StructNei) {
        if(vis[v] != 0) {
            StructNei[write_pos++] = v;
        }
    }

    StructNei.resize(write_pos);

    assert(vis[root] != 0);
}

void build_egosg_and_vr(ui* tmp_pstart, ui* tmp_edges, ui* tmp_degree, vector<ui>&StructNei, ui*vis, vector<ui>&sg_vs, vector<ui>&sg_ve, vector<ui>&sg_e, vector<ui>&sg_deg, vector<vector<ui>>&progress_sim_nei)
{
    sg_e.clear();
    ui pos = 0;
    for(auto v : StructNei) {
        sg_vs[v] = pos;
        for(ui i = tmp_pstart[v]; i < tmp_pstart[v+1]; ++i) if(vis[tmp_edges[i]]!=0) {
            ui w = tmp_edges[i];
            sg_e.push_back(w);
            ++pos;
        }
        for(auto w : progress_sim_nei[v]) if(vis[w]!=0) {
            sg_e.push_back(w);
            ++pos;
        }
        sg_ve[v] = pos;
        assert(sg_ve[v] >= sg_vs[v]);
        sg_deg[v] = sg_ve[v] - sg_vs[v];
    }
    int thre = max_gc_size;
    queue<ui> Q;
    for(auto e : StructNei) if(sg_deg[e] < thre) Q.push(e);
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        assert(vis[u]!=0);
        vis[u]=0;
        for(ui i = sg_vs[u]; i < sg_ve[u]; ++i) {
            if(sg_deg[sg_e[i]]--==thre)Q.push(sg_e[i]);
        }
    }
    bool change = false;

    if(change) {
        assert(Q.empty());
        for(auto e : StructNei) if(sg_deg[e] < thre) Q.push(e);
        while (!Q.empty()) {
            ui u = Q.front();
            Q.pop();
            assert(vis[u]!=0);
            vis[u]=0;
            for(ui i = sg_vs[u]; i < sg_ve[u]; ++i) {
                if(sg_deg[sg_e[i]]--==thre)Q.push(sg_e[i]);
            }
        }
    }
    ui R_idx = 0;
    for(ui i = 0; i < StructNei.size(); ++i) if(vis[StructNei[i]]!=0) StructNei[R_idx++] = StructNei[i];
    StructNei.resize(R_idx);
}

bool find_a_heu_gc_in_ego(ui root, vector<ui>& R, const vector<ui>& sg_deg, ui target_gc_size)
{


    sort(R.begin(), R.end(), [&](ui u, ui v) {
        if(sg_deg[u] != sg_deg[v]) {
            return sg_deg[u] > sg_deg[v];
        }

        return u < v;
    });

    vector<ui> clique;
    clique.reserve(R.size() + 1);
    clique.push_back(root);


    for(ui v : R) {
        bool can_add = true;

        for(ui w : clique) {
            if(Matrix[trs[v]][trs[w]] == 0) {
                can_add = false;
                break;
            }
        }

        if(can_add) {
            clique.push_back(v);
        }
    }


    if(clique.size() > max_gc_size) {
        max_gc_size = (ui)clique.size();

#ifdef _CollectRes_
        res.clear();

        vector<ui> original_clique;
        original_clique.reserve(clique.size());

        for(ui v : clique) {
            original_clique.push_back(oid_mapping[v]);
        }

        res.push_back(original_clique);
#endif
    }

    return clique.size() >= target_gc_size;
}

bool find_a_heu_gc_in_sparse_ego(
    ui root,
    vector<ui>& R,
    ui* vis,
    const vector<ui>& sg_vs,
    const vector<ui>& sg_ve,
    const vector<ui>& sg_e,
    const vector<ui>& sg_deg,
    ui target_gc_size)
{


    sort(R.begin(), R.end(),
         [&](ui a, ui b) {
             if(sg_deg[a] != sg_deg[b]) {
                 return sg_deg[a] > sg_deg[b];
             }

             return a < b;
         });

    vector<ui> clique;
    clique.reserve(R.size() + 1);
    clique.push_back(root);

    vector<ui> candidates = R;
    vector<ui> next_candidates;
    next_candidates.reserve(R.size());


    static vector<ui> neighbor_mark;
    static ui mark_token = 0;

    if(neighbor_mark.size() != n) {
        neighbor_mark.assign(n, 0);
        mark_token = 0;
    }

    while(!candidates.empty()) {


        ui v = candidates[0];

        clique.push_back(v);

        ++mark_token;

        if(mark_token == 0) {
            fill(
                neighbor_mark.begin(),
                neighbor_mark.end(),
                0
            );

            mark_token = 1;
        }


        for(ui i = sg_vs[v]; i < sg_ve[v]; ++i) {
            ui w = sg_e[i];

            if(vis[w] != 0) {
                neighbor_mark[w] = mark_token;
            }
        }


        next_candidates.clear();

        for(ui i = 1; i < candidates.size(); ++i) {
            ui w = candidates[i];

            if(neighbor_mark[w] == mark_token) {
                next_candidates.push_back(w);
            }
        }

        candidates.swap(next_candidates);
    }


    if(clique.size() > max_gc_size) {
        max_gc_size = (ui)clique.size();

#ifdef _CollectRes_
        res.clear();

        vector<ui> original_clique;
        original_clique.reserve(clique.size());

        for(ui v : clique) {
            original_clique.push_back(
                oid_mapping[v]
            );
        }

        res.push_back(original_clique);
#endif
    }

    return clique.size() >= target_gc_size;
}

void build_matrix_from_egosg(
    ui root,
    const vector<ui>& R,
    ui* vis,
    const vector<ui>& sg_vs,
    const vector<ui>& sg_ve,
    const vector<ui>& sg_e)
{
    const ui md =
        (ui)R.size() + 1;

    assert(md > 0);
    assert(Matrix != nullptr);
    assert(Matrix[0] != nullptr);


    trs[root] = 0;

    for(ui i = 0; i < R.size(); ++i) {
        trs[R[i]] = i + 1;
    }


    size_t matrix_size =
        (size_t)md * (size_t)md;

    memset(
        Matrix[0],
        0,
        matrix_size * sizeof(char)
    );


    for(ui i = sg_vs[root]; i < sg_ve[root]; ++i) {
        ui w = sg_e[i];

        if(vis[w] == 0) continue;

        Matrix[0][trs[w]] = 1;
    }


    for(ui v : R) {
        ui local_v = trs[v];

        for(ui i = sg_vs[v]; i < sg_ve[v]; ++i) {
            ui w = sg_e[i];

            if(vis[w] == 0) continue;

            Matrix[local_v][trs[w]] = 1;
        }
    }
}


void restore_all_similar_edges_by_index(ui* tmp_pstart, ui* tmp_edges, ui* del,
                                        vector<vector<pair<double,ui>>>& residual_sim_nei,
                                        vector<vector<ui>>& z_list,
                                        vector<vector<pair<double,ui>>>& z_R,
                                        vector<vector<ui>>& progress_sim_nei)
{
    progress_sim_nei.clear();
    progress_sim_nei.resize(n);

    vector<ui> checked(n, 0);
    ui token = 0;

    for(ui u = 0; u < n; ++u) {
        ++token;
        if(token == 0) {
            fill(checked.begin(), checked.end(), 0);
            token = 1;
        }

        ui original_u = oid_mapping[u];
        checked[u] = token;


        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];
            checked[v] = token;
        }


        for(ui i = 0; i < residual_sim_nei[original_u].size(); ++i) {
            double score = residual_sim_nei[original_u][i].first;
            ui original_v = residual_sim_nei[original_u][i].second;

            if(score < epsi) break;
            if(original_v == original_u) continue;
            if(del[original_v] != 0) continue;

            ui v = newid_mapping[original_v];

            if(checked[v] == token) continue;
            checked[v] = token;


            if(u < v) {
                progress_sim_nei[u].push_back(v);
                progress_sim_nei[v].push_back(u);
            }
        }


        for(ui i = 0; i < z_list[original_u].size(); ++i) {
            ui z = z_list[original_u][i];
            assert(z < z_R.size());

            for(ui j = 0; j < z_R[z].size(); ++j) {
                double score_ub = z_R[z][j].first;
                ui original_v = z_R[z][j].second;

                if(score_ub < epsi) break;
                if(original_v == original_u) continue;
                if(del[original_v] != 0) continue;

                ui v = newid_mapping[original_v];

                if(u >= v) continue;


                if(checked[v] == token) continue;
                checked[v] = token;

                ui du = degree[original_u];
                ui dv = degree[original_v];

                if(du == 0 || dv == 0) continue;
                if(min(du, dv) < (ui)ComNeiThre) continue;
                if((double)min(du, dv) / (double)max(du, dv) < epsi) continue;

                pair<double,ui> jsp = js(original_u, original_v);

                if(jsp.first >= epsi) {
                    progress_sim_nei[u].push_back(v);
                    progress_sim_nei[v].push_back(u);
                }
            }
        }
    }
}

ui exact_generalized_core_reduction(ui* tmp_pstart, ui* tmp_edges, ui* tmp_degree,
                                    vector<vector<ui>>& progress_sim_nei, ui* del)
{
    if(n == 0 || max_gc_size < 1) return 0;

    ui old_n = n;
    ui threshold = (ui)max_gc_size;

    vector<ui> gc_degree(old_n, 0);
    vector<char> alive(old_n, 1);
    vector<ui> Q;
    Q.reserve(old_n);


    for(ui u = 0; u < old_n; ++u) {
        unsigned long long d = (unsigned long long)tmp_degree[u] +
                               (unsigned long long)progress_sim_nei[u].size();

        assert(d < old_n);

        gc_degree[u] = (ui)d;

        if(gc_degree[u] < threshold) Q.push_back(u);
    }

    size_t qhead = 0;
    ui deleted_cnt = 0;

    while(qhead < Q.size()) {
        ui u = Q[qhead++];

        if(alive[u] == 0) continue;

        alive[u] = 0;
        ++deleted_cnt;


        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];

            if(alive[v] == 0) continue;
            assert(gc_degree[v] > 0);

            if(gc_degree[v] == threshold) {
                --gc_degree[v];
                Q.push_back(v);
            }
            else {
                --gc_degree[v];
            }
        }


        for(ui i = 0; i < progress_sim_nei[u].size(); ++i) {
            ui v = progress_sim_nei[u][i];

            if(alive[v] == 0) continue;
            assert(gc_degree[v] > 0);

            if(gc_degree[v] == threshold) {
                --gc_degree[v];
                Q.push_back(v);
            }
            else {
                --gc_degree[v];
            }
        }
    }

    if(deleted_cnt == 0) return 0;


    vector<ui> old_oid(old_n);
    vector<ui> old_to_new(old_n, old_n);

    for(ui u = 0; u < old_n; ++u) old_oid[u] = oid_mapping[u];

    ui new_n = 0;

    for(ui old_u = 0; old_u < old_n; ++old_u) {
        if(alive[old_u] == 0) {
            del[old_oid[old_u]] = 1;
            continue;
        }

        old_to_new[old_u] = new_n;
        oid_mapping[new_n] = old_oid[old_u];
        newid_mapping[old_oid[old_u]] = new_n;
        ++new_n;
    }

    if(new_n == 0) {
        n = 0;
        m = 0;
        progress_sim_nei.clear();
        return deleted_cnt;
    }


    vector<ui> new_pstart(new_n + 1, 0);
    vector<ui> new_edges;
    new_edges.reserve(m);

    ui new_u = 0;

    for(ui old_u = 0; old_u < old_n; ++old_u) {
        if(alive[old_u] == 0) continue;

        for(ui i = tmp_pstart[old_u]; i < tmp_pstart[old_u+1]; ++i) {
            ui old_v = tmp_edges[i];

            if(alive[old_v] != 0) {
                new_edges.push_back(old_to_new[old_v]);
            }
        }

        ++new_u;
        new_pstart[new_u] = (ui)new_edges.size();
    }


    vector<vector<ui>> new_sim_nei(new_n);

    for(ui old_u = 0; old_u < old_n; ++old_u) {
        if(alive[old_u] == 0) continue;

        ui mapped_u = old_to_new[old_u];
        new_sim_nei[mapped_u].reserve(progress_sim_nei[old_u].size());

        for(ui i = 0; i < progress_sim_nei[old_u].size(); ++i) {
            ui old_v = progress_sim_nei[old_u][i];

            if(alive[old_v] != 0) {
                new_sim_nei[mapped_u].push_back(old_to_new[old_v]);
            }
        }
    }

    memcpy(tmp_pstart, new_pstart.data(), sizeof(ui) * (new_n + 1));

    if(!new_edges.empty()) {
        memcpy(tmp_edges, new_edges.data(), sizeof(ui) * new_edges.size());
    }

    n = new_n;
    m = (ui)new_edges.size();

    for(ui u = 0; u < n; ++u) {
        tmp_degree[u] = tmp_pstart[u+1] - tmp_pstart[u];
    }

    progress_sim_nei.swap(new_sim_nei);

    return deleted_cnt;
}

ui compute_degeneracy_ordering_of_tmp_generalized_graph(ui* peels, ui* vis, ui* core, ui* rid,
                                                         ui* forward_degree,
                                                         ui* tmp_pstart, ui* tmp_edges, ui* tmp_degree,
                                                         vector<vector<ui>>& progress_sim_nei)
{
    memset(vis, 0, sizeof(ui) * n);

    vector<ui> gc_degree(n);

    for(ui u = 0; u < n; ++u) {
        unsigned long long d = (unsigned long long)tmp_degree[u] +
                               (unsigned long long)progress_sim_nei[u].size();

        assert(d < n);

        gc_degree[u] = (ui)d;
        peels[u] = u;
    }

    ListLinearHeap* heap = new ListLinearHeap(n, n - 1);
    heap->init(n, n - 1, peels, gc_degree.data());

    ui max_core = 0;

    for(ui i = 0; i < n; ++i) {
        ui u, key;
        heap->pop_min(u, key);


        forward_degree[u] = key;

        if(key > max_core) max_core = key;

        core[u] = max_core;
        peels[i] = u;
        vis[u] = 1;

        for(ui j = tmp_pstart[u]; j < tmp_pstart[u+1]; ++j) {
            ui v = tmp_edges[j];

            if(vis[v] == 0) heap->decrement(v, 1);
        }

        for(ui j = 0; j < progress_sim_nei[u].size(); ++j) {
            ui v = progress_sim_nei[u][j];

            if(vis[v] == 0) heap->decrement(v, 1);
        }
    }

    for(ui i = 0; i < n; ++i) {
        rid[peels[i]] = i;
    }

    delete heap;

    cout << "generalized degeneracy: " << max_core << endl;

    return max_core;
}

ui update_best_clique_by_peeling_suffix(ui* peels, ui* forward_degree)
{
    if(n == 0) return 0;


    ui suffix_start = n - 1;


    for(long long i = (long long)n - 2; i >= 0; --i) {
        ui u = peels[i];
        ui later_vertex_cnt = n - (ui)i - 1;


        if(forward_degree[u] == later_vertex_cnt) {
            suffix_start = (ui)i;
        }
        else {
            break;
        }
    }

    ui suffix_size = n - suffix_start;

    if(suffix_size > (ui)max_gc_size) {
        max_gc_size = suffix_size;

        vector<ui> new_clique;
        new_clique.reserve(suffix_size);


        for(ui i = suffix_start; i < n; ++i) {
            ui u = peels[i];
            new_clique.push_back(oid_mapping[u]);
        }

        res.clear();
        res.push_back(new_clique);

        cout << "peeling suffix heuristic improvement, new size: "
             << max_gc_size << endl;
    }
    else {
        cout << "peeling suffix clique size: "
             << suffix_size << endl;
    }

    return suffix_size;
}

void compute_degeneracy_ordering_of_tmp_generalized_graph(ui* peels, ui* vis, ui* core, ui* rid,
                                                           ui* tmp_pstart, ui* tmp_edges, ui* tmp_degree,
                                                           vector<vector<ui>>& progress_sim_nei)
{
    memset(vis, 0, sizeof(ui) * n);

    vector<ui> gc_degree(n);

    for(ui u = 0; u < n; ++u) {
        unsigned long long d = (unsigned long long)tmp_degree[u] +
                               (unsigned long long)progress_sim_nei[u].size();

        assert(d < n);

        gc_degree[u] = (ui)d;
        peels[u] = u;
    }

    ListLinearHeap* heap = new ListLinearHeap(n, n - 1);
    heap->init(n, n - 1, peels, gc_degree.data());

    ui max_core = 0;

    for(ui i = 0; i < n; ++i) {
        ui u, key;
        heap->pop_min(u, key);

        if(key > max_core) max_core = key;

        core[u] = max_core;
        peels[i] = u;
        vis[u] = 1;

        for(ui j = tmp_pstart[u]; j < tmp_pstart[u+1]; ++j) {
            ui v = tmp_edges[j];

            if(vis[v] == 0) heap->decrement(v, 1);
        }

        for(ui j = 0; j < progress_sim_nei[u].size(); ++j) {
            ui v = progress_sim_nei[u][j];

            if(vis[v] == 0) heap->decrement(v, 1);
        }
    }

    for(ui i = 0; i < n; ++i) rid[peels[i]] = i;

    delete heap;

    cout << "generalized degeneracy: " << max_core << endl;
}

void vertex_reduction_by_index_query(
    ui* tmp_pstart,
    ui* tmp_edges,
    ui* tmp_degree,
    vector<vector<pair<double,ui>>>& residual_sim_nei,
    vector<vector<ui>>& z_list,
    ui& z_idx,
    vector<vector<pair<double,ui>>>& z_R,
    ui* del)
{


    const ui original_n = n;


    const ui original_m = m;

    const ui thre = (ui)max_gc_size;

    if(original_n == 0 || thre < 1)
        return;


    vector<ui> candidate_mark(
        original_n,
        0
    );

    ui token = 0;


    auto obtain_new_token =
        [&]() -> ui
    {
        ++token;

        if(token == 0) {

            fill(
                candidate_mark.begin(),
                candidate_mark.end(),
                0
            );

            token = 1;
        }

        return token;
    };


    auto can_be_similar_by_degree =
        [&](ui u, ui v) -> bool
    {
        if(u == v)
            return false;

        ui du = degree[u];
        ui dv = degree[v];

        if(du == 0 || dv == 0)
            return false;

        ui min_degree =
            min(du, dv);

        ui max_degree =
            max(du, dv);

        if(min_degree <
           (ui)ComNeiThre)
        {
            return false;
        }

        if((double)min_degree /
               (double)max_degree
           < epsi)
        {
            return false;
        }

        return true;
    };


    unsigned long long
        duplicate_candidate_cnt = 0;

    unsigned long long
        degree_filter_cnt = 0;


    for(ui u = 0;
        u < original_n;
        ++u)
    {


        if(del[u] != 0) {
            tmp_degree[u] = 0;
            continue;
        }


        ui current_token =
            obtain_new_token();

        ui degree_ub = 0;

        candidate_mark[u] =
            current_token;


        for(ui i = tmp_pstart[u];
            i < tmp_pstart[u + 1];
            ++i)
        {
            ui v = tmp_edges[i];

            assert(v < original_n);
            assert(del[v] == 0);

            if(v == u)
                continue;

            if(candidate_mark[v]
               != current_token)
            {
                candidate_mark[v] =
                    current_token;

                ++degree_ub;
            }
        }


        for(const auto& simnei :
            residual_sim_nei[u])
        {
            double score =
                simnei.first;

            ui v =
                simnei.second;

            if(score < epsi)
                break;

            assert(v < original_n);

            if(v == u)
                continue;


            if(del[v] != 0)
                continue;


            if(candidate_mark[v]
               == current_token)
            {
                ++duplicate_candidate_cnt;
                continue;
            }

            candidate_mark[v] =
                current_token;

            ++degree_ub;
        }


        for(ui z : z_list[u])
        {
            assert(z < z_idx);
            assert(z < z_R.size());


            for(const auto& nei :
                z_R[z])
            {
                double upper_score =
                    nei.first;

                ui v =
                    nei.second;

                if(upper_score < epsi)
                    break;

                assert(v < original_n);

                if(v == u)
                    continue;


                if(del[v] != 0)
                    continue;


                if(candidate_mark[v]
                   == current_token)
                {
                    ++duplicate_candidate_cnt;
                    continue;
                }

                candidate_mark[v] =
                    current_token;


                if(!can_be_similar_by_degree(
                       u,
                       v))
                {
                    ++degree_filter_cnt;
                    continue;
                }

                ++degree_ub;
            }
        }


        assert(
            degree_ub <=
            original_n - 1
        );

        tmp_degree[u] =
            degree_ub;
    }


    auto perform_peeling =
        [&](queue<ui>& Q) -> ui
    {
        ui deleted_cnt = 0;


        while(!Q.empty())
        {
            ui u = Q.front();
            Q.pop();


            if(del[u] != 0)
                continue;


            assert(
                tmp_degree[u] <
                thre
            );


            del[u] = 1;

            ++deleted_cnt;


            for(ui i = tmp_pstart[u];
                i < tmp_pstart[u + 1];
                ++i)
            {
                ui v =
                    tmp_edges[i];

                if(del[v] != 0)
                    continue;


                if(tmp_degree[v] == 0)
                    continue;


                if(tmp_degree[v] ==
                   thre)
                {
                    --tmp_degree[v];

                    Q.push(v);
                }
                else {
                    --tmp_degree[v];
                }
            }
        }


        return deleted_cnt;
    };


    queue<ui> Q;


    for(ui u = 0;
        u < original_n;
        ++u)
    {


        if(del[u] != 0)
            continue;


        if(tmp_degree[u] <
           thre)
        {
            Q.push(u);
        }
    }


    ui initial_deleted_cnt =
        perform_peeling(Q);


    auto compute_exact_live_gc_degree =
        [&](ui u) -> ui
    {
        ui current_token =
            obtain_new_token();

        ui exact_degree = 0;


        candidate_mark[u] =
            current_token;


        for(ui i = tmp_pstart[u];
            i < tmp_pstart[u + 1];
            ++i)
        {
            ui v =
                tmp_edges[i];


            if(v == u ||
               del[v] != 0)
            {
                continue;
            }


            if(candidate_mark[v]
               != current_token)
            {
                candidate_mark[v] =
                    current_token;

                ++exact_degree;
            }
        }


        for(const auto& simnei :
            residual_sim_nei[u])
        {
            double score =
                simnei.first;

            ui v =
                simnei.second;


            if(score < epsi)
                break;


            if(v == u ||
               del[v] != 0)
            {
                continue;
            }


            if(candidate_mark[v]
               == current_token)
            {
                continue;
            }


            candidate_mark[v] =
                current_token;

            ++exact_degree;
        }


        for(ui z :
            z_list[u])
        {
            assert(z < z_idx);
            assert(z < z_R.size());


            for(const auto& nei :
                z_R[z])
            {
                double upper_score =
                    nei.first;

                ui v =
                    nei.second;


                if(upper_score <
                   epsi)
                {
                    break;
                }


                if(v == u ||
                   del[v] != 0)
                {
                    continue;
                }


                if(candidate_mark[v]
                   == current_token)
                {
                    continue;
                }


                candidate_mark[v] =
                    current_token;


                if(!can_be_similar_by_degree(
                       u,
                       v))
                {
                    continue;
                }


                auto jsp =
                    js(u, v);


                if(jsp.first >= epsi)
                {
                    ++exact_degree;
                }
            }
        }


        return exact_degree;
    };


    ui refine_gap =
        max(
            thre,
            (ui)128
        );


    unsigned long long
        refine_upper_64 =
            (unsigned long long)thre
            +
            (unsigned long long)
                refine_gap;


    ui refine_upper;


    if(refine_upper_64 >=
       original_n)
    {
        refine_upper =
            original_n - 1;
    }
    else {
        refine_upper =
            (ui)refine_upper_64;
    }


    const ui MAX_REFINE_ROUND = 2;


    unsigned long long
        refined_vertex_cnt = 0;

    ui refinement_deleted_cnt = 0;


    for(ui round = 0;
        round < MAX_REFINE_ROUND;
        ++round)
    {
        queue<ui> refine_Q;


        for(ui u = 0;
            u < original_n;
            ++u)
        {
            if(del[u] != 0)
                continue;


            if(tmp_degree[u] >
               refine_upper)
            {
                continue;
            }


            ++refined_vertex_cnt;


            ui exact_degree =
                compute_exact_live_gc_degree(
                    u
                );


            tmp_degree[u] =
                exact_degree;


            if(exact_degree <
               thre)
            {
                refine_Q.push(u);
            }
        }


        if(refine_Q.empty())
            break;


        ui round_deleted_cnt =
            perform_peeling(
                refine_Q
            );


        refinement_deleted_cnt +=
            round_deleted_cnt;


        if(round_deleted_cnt == 0)
            break;
    }


    ui new_n = 0;


    for(ui u = 0;
        u < original_n;
        ++u)
    {
        if(del[u] == 0)
        {
            oid_mapping[new_n] =
                u;

            newid_mapping[u] =
                new_n;

            ++new_n;
        }
    }


    ui* t_pstart =
        new ui[original_n + 1];

    ui* t_edges =
        new ui[original_m];


    ui edge_pos = 0;
    ui new_u = 0;

    t_pstart[0] = 0;


    for(ui original_u = 0;
        original_u < original_n;
        ++original_u)
    {
        if(del[original_u] != 0)
            continue;


        assert(
            oid_mapping[new_u]
            ==
            original_u
        );


        for(ui i =
                tmp_pstart[original_u];
            i <
                tmp_pstart[original_u + 1];
            ++i)
        {
            ui original_v =
                tmp_edges[i];


            if(del[original_v] == 0)
            {
                t_edges[edge_pos++] =
                    newid_mapping[
                        original_v
                    ];
            }
        }


        ++new_u;

        t_pstart[new_u] =
            edge_pos;
    }


    assert(new_u == new_n);
    assert(edge_pos % 2 == 0);


    memcpy(
        tmp_pstart,
        t_pstart,
        sizeof(ui) *
            (new_n + 1)
    );


    if(edge_pos > 0)
    {
        memcpy(
            tmp_edges,
            t_edges,
            sizeof(ui) *
                edge_pos
        );
    }


    delete [] t_pstart;
    delete [] t_edges;


    n = new_n;
    m = edge_pos;


    for(ui u = 0;
        u < n;
        ++u)
    {
        tmp_degree[u] =
            tmp_pstart[u + 1]
            -
            tmp_pstart[u];
    }


    cout << "query index VR details:"
         << " initial deleted = "
         << initial_deleted_cnt

         << ", refinement checks = "
         << refined_vertex_cnt

         << ", refinement deleted = "
         << refinement_deleted_cnt

         << ", duplicate candidates = "
         << duplicate_candidate_cnt

         << ", degree-filtered candidates = "
         << degree_filter_cnt

         << endl;
}

int find_a_heu_gc_query(
    ui* tmp_pstart,
    ui* tmp_edges,
    ui* tmp_degree,
    const vector<ui>& query_vertices,
    ui original_n)
{
    ui query_n = (ui)query_vertices.size();

    if(query_n == 0) {
        res.clear();
        return 0;
    }


    vector<ui> local_to_original(query_n);
    vector<ui> original_to_local(original_n, UINT_MAX);

    for(ui i = 0; i < query_n; ++i) {
        ui u = query_vertices[i];

        local_to_original[i] = u;
        original_to_local[u] = i;
    }


    ui* local_degree = new ui[query_n];

    for(ui i = 0; i < query_n; ++i) {
        ui original_u = local_to_original[i];

        local_degree[i] = tmp_degree[original_u];

        assert(local_degree[i] <= query_n - 1);
    }


    int idx = -1;

    ui* peels = new ui[query_n];

    for(ui i = 0; i < query_n; ++i)
        peels[i] = i;


    ui* vis = new ui[query_n];

    memset(
        vis,
        0,
        sizeof(ui) * query_n
    );


    ListLinearHeap* heap =
        new ListLinearHeap(
            query_n,
            query_n - 1
        );


    heap->init(
        query_n,
        query_n - 1,
        peels,
        local_degree
    );


    for(ui i = 0; i < query_n; ++i) {

        ui local_u;
        ui key;

        heap->pop_min(
            local_u,
            key
        );


        int current_vnum =
            (int)(query_n - i);

        int min_deg =
            (int)key;


        if(idx == -1 &&
           min_deg == current_vnum - 1)
        {
            idx = (int)i;
        }


        peels[i] = local_u;

        vis[local_u] = 1;


        ui original_u =
            local_to_original[local_u];


        for(ui j = tmp_pstart[original_u];
            j < tmp_pstart[original_u + 1];
            ++j)
        {
            ui original_v =
                tmp_edges[j];

            ui local_v =
                original_to_local[original_v];


            assert(local_v != UINT_MAX);


            if(vis[local_v] == 0) {

                heap->decrement(
                    local_v,
                    1
                );
            }
        }
    }


    assert(idx >= 0);


    vector<ui> mcvec;

    mcvec.reserve(
        query_n - (ui)idx
    );


    for(int i = idx;
        i < (int)query_n;
        ++i)
    {
        ui local_u =
            peels[i];

        ui original_u =
            local_to_original[local_u];

        mcvec.push_back(
            original_u
        );
    }


    res.clear();
    res.push_back(mcvec);


    delete heap;

    delete [] local_degree;
    delete [] peels;
    delete [] vis;


#ifdef _CheckInfo_

    cout << "query heu structural clique size = "
         << mcvec.size()
         << ", members: ";

    for(auto u : mcvec)
        cout << u << ",";

    cout << endl;

#endif


    return (int)mcvec.size();
}

void obtain_query_region_containing_q_by_index(
    ui query_point,
    vector<vector<pair<double,ui>>>& residual_sim_nei,
    vector<vector<ui>>& z_list,
    vector<vector<pair<double,ui>>>& z_R,
    vector<char>& in_query,
    vector<ui>& query_vertices)
{
    const ui original_n = n;

    assert(query_point < original_n);

    in_query.assign(original_n, 0);
    query_vertices.clear();


    in_query[query_point] = 1;
    query_vertices.push_back(query_point);


    for(ui i = pstart[query_point];
        i < pstart[query_point + 1];
        ++i)
    {
        ui v = edges[i];

        if(in_query[v] == 0) {
            in_query[v] = 1;
            query_vertices.push_back(v);
        }
    }


    HeuGCWorkspace workspace(original_n);

    vector<ui> gc_neighbors;

    obtain_gc_neighbors_by_index(
        query_point,
        residual_sim_nei,
        z_list,
        z_R,
        gc_neighbors,
        workspace
    );


    for(ui v : gc_neighbors)
    {
        if(v == query_point)
            continue;

        if(in_query[v] == 0) {
            in_query[v] = 1;
            query_vertices.push_back(v);
        }
    }


    cout << "query point: "
         << query_point
         << endl;

    cout << "query compatible region |V|: "
         << query_vertices.size()
         << endl;
}

void maximum_generalized_clique_computation_by_index_adv_query(
    vector<vector<pair<double,ui>>>& residual_sim_nei,
    vector<vector<ui>>& z_list,
    ui& z_idx,
    vector<vector<pair<double,ui>>>& z_R,
    ui query_point)
{
    Timer t;
    Timer tt;

    ss = 0;
    resnum = 0;
    max_gc_size = 0;
    res.clear();

    double t_query = 0;
    double t_heu = 0;
    double t_vr = 0;
    double t_simnei = 0;
    double t_global_core = 0;
    double t_degen = 0;
    double t_construct_subgraph = 0;
    double t_build_matrix = 0;
    double t_color = 0;
    double t_bnb = 0;
    double t_clear = 0;

    const ui original_n = n;
    const ui original_m = m;

    assert(query_point < original_n);


    tt.restart();

    tt.restart();

    vector<char> in_query;
    vector<ui> query_vertices;

    obtain_query_region_containing_q_by_index(
        query_point,
        residual_sim_nei,
        z_list,
        z_R,
        in_query,
        query_vertices
    );

    t_query +=
        (double)tt.elapsed()
        / CLOCKS_PER_SEC;


    unsigned long long query_m64 = 0;

    for(ui u : query_vertices) {

        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            ui v = edges[i];

            if(in_query[v]) {
                ++query_m64;
            }
        }
    }

    assert(query_m64 <=
           (unsigned long long)original_m);

    ui query_m = (ui)query_m64;


    ui* tmp_pstart = new ui[original_n + 1];
    ui* tmp_edges = new ui[query_m];
    ui* tmp_degree = new ui[original_n];
    ui* del = new ui[original_n];

    memset(tmp_degree,
           0,
           sizeof(ui) * original_n);


    for(ui u = 0; u < original_n; ++u) {
        del[u] = in_query[u] ? 0 : 1;
    }


    ui pos = 0;

    for(ui u = 0; u < original_n; ++u) {

        tmp_pstart[u] = pos;

        if(in_query[u] == 0) {
            tmp_degree[u] = 0;
            continue;
        }

        for(ui i = pstart[u];
            i < pstart[u + 1];
            ++i)
        {
            ui v = edges[i];

            if(in_query[v] == 0)
                continue;

            tmp_edges[pos++] = v;
        }

        tmp_degree[u] =
            pos - tmp_pstart[u];
    }

    tmp_pstart[original_n] = pos;

    assert(pos == query_m);
    assert(query_m % 2 == 0);


    m = query_m;

    t_query +=
        (double)tt.elapsed() / CLOCKS_PER_SEC;

    cout << "query induced structural |E|: "
         << m / 2 << endl;


    tt.restart();

    max_gc_size =
        find_a_heu_gc_query(
            tmp_pstart,
            tmp_edges,
            tmp_degree,
            query_vertices,
            original_n
        );


    if(res.empty()) {

        res.clear();

        vector<ui> tmp_res;
        tmp_res.push_back(query_point);

        res.push_back(tmp_res);

        max_gc_size = 1;
    }
    else {

        bool contain_q = false;

        for(ui v : res[0]) {
            if(v == query_point) {
                contain_q = true;
                break;
            }
        }

        if(!contain_q) {
            res[0].push_back(query_point);
            ++max_gc_size;
        }
    }

    t_heu +=
        (double)tt.elapsed()
        / CLOCKS_PER_SEC;

    cout << "heu solu size    : "
         << max_gc_size
         << endl;


    tt.restart();

    vertex_reduction_by_index_query(
        tmp_pstart,
        tmp_edges,
        tmp_degree,
        residual_sim_nei,
        z_list,
        z_idx,
        z_R,
        del
    );


    if(del[query_point] != 0)
    {
        cout << "query point is removed by coarse VR; "
             << "current q-containing solution is optimal"
             << endl;

        delete [] tmp_pstart;
        delete [] tmp_edges;
        delete [] tmp_degree;
        delete [] del;

        cout << "Max GC containing q: "
             << max_gc_size
             << ", search space: "
             << ss
             << endl;

        n = original_n;
        m = original_m;

        return;
    }

    t_vr +=
        (double)tt.elapsed() / CLOCKS_PER_SEC;

    cout << "after query coarse VR, |V| = "
         << n
         << ", |E| = "
         << m / 2
         << endl;


    if(n == 0) {

        delete [] tmp_pstart;
        delete [] tmp_edges;
        delete [] tmp_degree;
        delete [] del;


        n = original_n;
        m = original_m;

        cout << "Max GC: "
             << max_gc_size
             << ", search space: "
             << ss << endl;

        cout << "Total Time: "
             << (double)t.elapsed()
                / CLOCKS_PER_SEC
             << "s" << endl;

        return;
    }


    vector<vector<ui>> progress_sim_nei;

    tt.restart();

    restore_all_similar_edges_by_index(
        tmp_pstart,
        tmp_edges,
        del,
        residual_sim_nei,
        z_list,
        z_R,
        progress_sim_nei
    );

    t_simnei +=
        (double)tt.elapsed()
        / CLOCKS_PER_SEC;


    unsigned long long similar_edge_cnt = 0;

    for(ui u = 0; u < n; ++u) {
        similar_edge_cnt +=
            progress_sim_nei[u].size();
    }

    cout << "exact query graph: |V| = "
         << n
         << ", structural |E| = "
         << m / 2
         << ", similar |E| = "
         << similar_edge_cnt / 2
         << endl;


    tt.restart();

    ui exact_deleted_cnt =
        exact_generalized_core_reduction(
            tmp_pstart,
            tmp_edges,
            tmp_degree,
            progress_sim_nei,
            del
        );

    t_global_core +=
        (double)tt.elapsed()
        / CLOCKS_PER_SEC;

    if(del[query_point] != 0)
    {
        cout << "query point is removed by exact generalized-core; "
             << "current q-containing solution is optimal"
             << endl;

        delete [] tmp_pstart;
        delete [] tmp_edges;
        delete [] tmp_degree;
        delete [] del;

        cout << "Max GC containing q: "
             << max_gc_size
             << ", search space: "
             << ss
             << endl;

        n = original_n;
        m = original_m;

        return;
    }

    cout << "exact generalized-core deleted = "
         << exact_deleted_cnt
         << ", remain |V| = "
         << n
         << ", structural |E| = "
         << m / 2
         << endl;


    if(n == 0) {

        delete [] tmp_pstart;
        delete [] tmp_edges;
        delete [] tmp_degree;
        delete [] del;

        cout << "the exact generalized core is empty"
             << endl;

        cout << "Max GC: "
             << max_gc_size
             << ", search space: "
             << ss << endl;

        cout << fixed << setprecision(2);

        double total_time =
            (double)t.elapsed()
            / CLOCKS_PER_SEC;

        cout << "Total Time: "
             << total_time << "s"
             << endl;

        cout << "\tquery build    = "
             << t_query << " s,  "
             << t_query / total_time * 100
             << " %" << endl;

        cout << "\theu solution t = "
             << t_heu << " s,  "
             << t_heu / total_time * 100
             << " %" << endl;

        cout << "\tindex-based vr = "
             << t_vr << " s,  "
             << t_vr / total_time * 100
             << " %" << endl;

        cout << "\tsim nei t      = "
             << t_simnei << " s,  "
             << t_simnei / total_time * 100
             << " %" << endl;

        cout << "\tglobal core t  = "
             << t_global_core << " s,  "
             << t_global_core / total_time * 100
             << " %" << endl;


        n = original_n;
        m = original_m;

        return;
    }


    ui ordering_capacity = n;

    ui* peels = new ui[ordering_capacity];
    ui* vis = new ui[ordering_capacity];
    ui* core = new ui[ordering_capacity];
    ui* rid = new ui[ordering_capacity];
    ui* forward_degree = new ui[ordering_capacity];

    ui max_generalized_core = 0;
    bool optimality_certified = false;

    while(true) {
        tt.restart();

        max_generalized_core =
            compute_degeneracy_ordering_of_tmp_generalized_graph(
                peels, vis, core, rid, forward_degree,
                tmp_pstart, tmp_edges, tmp_degree,
                progress_sim_nei
            );

        ui old_max_gc_size = max_gc_size;

        update_best_clique_by_peeling_suffix(peels, forward_degree);

        t_degen += (double)tt.elapsed() / CLOCKS_PER_SEC;


        assert((ui)max_gc_size <= max_generalized_core + 1);

        if((ui)max_gc_size == max_generalized_core + 1) {
            optimality_certified = true;

            cout << "optimality certified by peeling suffix and degeneracy bound"
                 << endl;

            break;
        }


        if((ui)max_gc_size == old_max_gc_size) {
            break;
        }


        tt.restart();

        ui suffix_vr_deleted =
            exact_generalized_core_reduction(
                tmp_pstart,
                tmp_edges,
                tmp_degree,
                progress_sim_nei,
                del
            );

        t_global_core +=
            (double)tt.elapsed() / CLOCKS_PER_SEC;

        cout << "peeling suffix VR deleted = "
             << suffix_vr_deleted
             << ", remain |V| = "
             << n
             << ", structural |E| = "
             << m / 2
             << endl;


        if(n == 0) {
            optimality_certified = true;

            cout << "exact generalized core becomes empty after suffix VR"
                 << endl;

            break;
        }


        if(suffix_vr_deleted == 0) {
            break;
        }


    }

    if(n > 0) {
        memset(vis, 0, sizeof(ui) * n);
    }

    if(optimality_certified) {
        delete [] forward_degree;
        delete [] peels;
        delete [] vis;
        delete [] core;
        delete [] rid;

        delete [] del;
        delete [] tmp_pstart;
        delete [] tmp_edges;
        delete [] tmp_degree;

        cout << "Max GC: " << max_gc_size
             << ", search space: " << ss << endl;

    #ifdef _CollectRes_
        if(!res.empty()) sort(res[0].begin(), res[0].end());
    #endif

        cout << fixed << setprecision(2);

        double total_time =
            (double)t.elapsed() / CLOCKS_PER_SEC;

        cout << "Total Time: "
             << total_time << "s" << endl;

        cout << "\theu solution t = "
             << t_heu << " s,  "
             << t_heu / total_time * 100 << " %" << endl;

        cout << "\tindex-based vr = "
             << t_vr << " s,  "
             << t_vr / total_time * 100 << " %" << endl;

        cout << "\tsim nei t      = "
             << t_simnei << " s,  "
             << t_simnei / total_time * 100 << " %" << endl;

        cout << "\tglobal core t  = "
             << t_global_core << " s,  "
             << t_global_core / total_time * 100 << " %" << endl;

        cout << "\tdegeneracy t   = "
             << t_degen << " s,  "
             << t_degen / total_time * 100 << " %" << endl;

        n = original_n;
        m = original_m;

        return;
    }


    vector<pair<ui,ui>> root_order;
    root_order.reserve(n);

    for(ui u = 0; u < n; ++u) {
        ui forward_degree = 0;

        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];

            if(rid[v] > rid[u]) ++forward_degree;
        }

        for(ui i = 0; i < progress_sim_nei[u].size(); ++i) {
            ui v = progress_sim_nei[u][i];

            if(rid[v] > rid[u]) ++forward_degree;
        }

        ui ub1 = forward_degree + 1;
        ui ub2 = core[u] + 1;
        ui root_ub = min(ub1, ub2);

        root_order.push_back(make_pair(root_ub, u));
    }

    sort(root_order.rbegin(), root_order.rend());


    trs = new ui[n];

    vector<ui> sg_vs(n);
    vector<ui> sg_ve(n);
    vector<ui> sg_e;
    vector<ui> sg_deg(n);

    for(ui task_idx = 0; task_idx < root_order.size(); ++task_idx) {
        ui root_ub = root_order[task_idx].first;
        ui u = root_order[task_idx].second;

        if(root_ub <= (ui)max_gc_size) continue;

        vector<ui> StructNei;


        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];

            if(rid[v] > rid[u]) {
                StructNei.push_back(v);
                vis[v] = 1;
            }
        }


        for(ui i = 0; i < progress_sim_nei[u].size(); ++i) {
            ui v = progress_sim_nei[u][i];

            if(rid[v] > rid[u]) {
                StructNei.push_back(v);
                vis[v] = 1;
            }
        }

        if(1 + StructNei.size() <= (ui)max_gc_size) {
            for(ui i = 0; i < StructNei.size(); ++i) vis[StructNei[i]] = 0;
            continue;
        }

        StructNei.push_back(u);
        vis[u] = 1;


        tt.restart();

        build_egosg_and_vr(tmp_pstart, tmp_edges, tmp_degree,
                           StructNei, vis, sg_vs, sg_ve,
                           sg_e, sg_deg, progress_sim_nei);

        t_construct_subgraph += (double)tt.elapsed() / CLOCKS_PER_SEC;

        if(vis[u] == 0) {
            for(ui i = 0; i < StructNei.size(); ++i) vis[StructNei[i]] = 0;
            continue;
        }


        tt.restart();

        ui md = (ui)StructNei.size();

        Matrix = new char*[md];

        size_t matrix_size = (size_t)md * (size_t)md;
        char* matrix_data = new char[matrix_size];

        for(ui i = 0; i < md; ++i) {
            Matrix[i] = matrix_data + (size_t)i * md;
        }

        vector<ui>::iterator it = find(StructNei.begin(), StructNei.end(), u);
        assert(it != StructNei.end());
        StructNei.erase(it);

        build_matrix(u, StructNei, vis, progress_sim_nei,
                     tmp_pstart, tmp_edges, tmp_degree);

        t_build_matrix += (double)tt.elapsed() / CLOCKS_PER_SEC;

        vector<ui> C;
        vector<ui> R;

        C.push_back(u);

        for(ui i = 0; i < StructNei.size(); ++i) {
            R.push_back(StructNei[i]);
        }

        ui target_gc_size = max_gc_size + 1;
        bool reach_target = false;

#ifdef _HeuEgo_
        reach_target = find_a_heu_gc_in_ego(u, R, sg_deg, target_gc_size);
#endif

        if(!reach_target) {
#ifdef _Coloring_
            tt.restart();
            coloring_before_bnb(R, md);
            t_color += (double)tt.elapsed() / CLOCKS_PER_SEC;
#endif

            tt.restart();
            bnb_finding_maximum_gc(C, R, target_gc_size);
            t_bnb += (double)tt.elapsed() / CLOCKS_PER_SEC;
        }


        tt.restart();

        vis[u] = 0;

        for(ui i = 0; i < StructNei.size(); ++i) {
            vis[StructNei[i]] = 0;
        }

        delete [] matrix_data;
        delete [] Matrix;
        Matrix = nullptr;

        t_clear += (double)tt.elapsed() / CLOCKS_PER_SEC;
    }

    delete [] trs;
    trs = nullptr;

    delete [] forward_degree;
    delete [] peels;
    delete [] vis;
    delete [] core;
    delete [] rid;

    delete [] del;
    delete [] tmp_pstart;
    delete [] tmp_edges;
    delete [] tmp_degree;

    cout << "Max GC: " << max_gc_size << ", search space: " << ss << endl;

#ifdef _CollectRes_
    if(!res.empty()) sort(res[0].begin(), res[0].end());
#endif

    cout << fixed << setprecision(4);

    double total_time = (double)t.elapsed() / CLOCKS_PER_SEC;

    cout << "Total Time: " << total_time << "s" << endl;
    cout << "\theu solution t = " << t_heu << " s,  " << t_heu / total_time * 100 << " %" << endl;
    cout << "\tindex-based vr = " << t_vr << " s,  " << t_vr / total_time * 100 << " %" << endl;
    cout << "\tsim nei t      = " << t_simnei << " s,  " << t_simnei / total_time * 100 << " %" << endl;
    cout << "\tglobal core t  = " << t_global_core << " s,  " << t_global_core / total_time * 100 << " %" << endl;
    cout << "\tdegeneracy t   = " << t_degen << " s,  " << t_degen / total_time * 100 << " %" << endl;
    cout << "\tconstruct sg t = " << t_construct_subgraph << " s,  " << t_construct_subgraph / total_time * 100 << " %" << endl;
    cout << "\tbuild matrix t = " << t_build_matrix << " s,  " << t_build_matrix / total_time * 100 << " %" << endl;
    cout << "\tcoloring t     = " << t_color << " s,  " << t_color / total_time * 100 << " %" << endl;
    cout << "\tbnb t          = " << t_bnb << " s,  " << t_bnb / total_time * 100 << " %" << endl;
    cout << "\tcleanup t      = " << t_clear << " s,  " << t_clear / total_time * 100 << " %" << endl;

    n = original_n;
    m = original_m;
}

void maximum_generalized_clique_computation_by_index_adv_query_batch(
    vector<vector<pair<double,ui>>>& residual_sim_nei,
    vector<vector<ui>>& z_list,
    ui& z_idx,
    vector<vector<pair<double,ui>>>& z_R,
    vector<ui>& query_points)
{
    if(query_points.empty()) {
        cout << "query_points is empty!" << endl;
        return;
    }

    double total_query_time = 0.0;
    double min_query_time = DBL_MAX;
    double max_query_time = 0.0;

    unsigned long long total_mgc_size = 0;
    ui min_mgc_size = UINT_MAX;
    ui max_mgc_size_batch = 0;

    ui valid_query_cnt = 0;

    cout << "========================================" << endl;
    cout << "Query-based MGC experiment" << endl;
    cout << "#queries = " << query_points.size() << endl;
    cout << "========================================" << endl;

    for(ui i = 0; i < query_points.size(); ++i) {

        ui query_point = query_points[i];

        if(query_point >= n) {
            cout << "invalid query point: "
                 << query_point << ", skipped." << endl;
            continue;
        }

        Timer query_timer;


        maximum_generalized_clique_computation_by_index_adv_query(
            residual_sim_nei,
            z_list,
            z_idx,
            z_R,
            query_point
        );

        double query_time =
            (double)query_timer.elapsed() / CLOCKS_PER_SEC;

        total_query_time += query_time;

        min_query_time =
            min(min_query_time, query_time);

        max_query_time =
            max(max_query_time, query_time);


        total_mgc_size += max_gc_size;

        min_mgc_size =
            min(min_mgc_size, (ui)max_gc_size);

        max_mgc_size_batch =
            max(max_mgc_size_batch, (ui)max_gc_size);

        ++valid_query_cnt;


        cout << "[Query "
             << valid_query_cnt
             << "/"
             << query_points.size()
             << "] q="
             << query_point
             << ", MGC="
             << max_gc_size
             << ", time="
             << fixed << setprecision(4)
             << query_time
             << " s"
             << endl <<endl;
    }


    if(valid_query_cnt == 0) {
        cout << "No valid query points!" << endl;
        return;
    }


    double avg_query_time =
        total_query_time / valid_query_cnt;

    double avg_mgc_size =
        (double)total_mgc_size / valid_query_cnt;


    cout << endl;
    cout << "========================================" << endl;
    cout << "QUERY-BASED MGC SUMMARY" << endl;
    cout << "========================================" << endl;

    cout << fixed << setprecision(4);

    cout << "#Queries        : "
         << valid_query_cnt << endl;

    cout << "Total Time      : "
         << total_query_time
         << " s" << endl;

    cout << "Avg Query Time  : "
         << avg_query_time
         << " s" << endl;

    cout << "Min Query Time  : "
         << min_query_time
         << " s" << endl;

    cout << "Max Query Time  : "
         << max_query_time
         << " s" << endl;

    cout << "Avg MGC Size    : "
         << avg_mgc_size << endl;

    cout << "Min MGC Size    : "
         << min_mgc_size << endl;

    cout << "Max MGC Size    : "
         << max_mgc_size_batch << endl;

    cout << "========================================" << endl;
}

void maximum_generalized_clique_computation_by_index_adv(vector<vector<pair<double,ui>>>& residual_sim_nei, vector<vector<ui>>& z_list, ui& z_idx, vector<vector<pair<double,ui>>>& z_R)
{
    Timer t;
    Timer tt;

    ss = 0;
    resnum = 0;
    max_gc_size = 0;
    res.clear();

    double t_heu = 0;
    double t_vr = 0;
    double t_simnei = 0;
    double t_global_core = 0;
    double t_degen = 0;
    double t_construct_subgraph = 0;
    double t_build_matrix = 0;
    double t_color = 0;
    double t_bnb = 0;
    double t_clear = 0;

    ui original_n = n;
    ui original_m = m;


    tt.restart();
    max_gc_size = find_a_heu_gc_by_index_quick(residual_sim_nei, z_list, z_R);
    t_heu += (double)tt.elapsed() / CLOCKS_PER_SEC;

    cout << "heu solu size    : " << max_gc_size << endl;


    ui* tmp_pstart = new ui[original_n + 1];
    ui* tmp_edges = new ui[original_m];
    ui* tmp_degree = new ui[original_n];
    ui* del = new ui[original_n];

    memcpy(tmp_pstart, pstart, sizeof(ui) * (original_n + 1));
    memcpy(tmp_edges, edges, sizeof(ui) * original_m);
    memcpy(tmp_degree, degree, sizeof(ui) * original_n);
    memset(del, 0, sizeof(ui) * original_n);

    tt.restart();
    vertex_reduction_by_index(tmp_pstart, tmp_edges, tmp_degree,
                               residual_sim_nei, z_list, z_idx, z_R, del);
    t_vr += (double)tt.elapsed() / CLOCKS_PER_SEC;

    cout << "after coarse VR, |V| = " << n << ", |E| = " << m / 2 << endl;

    if(n == 0) {
        delete [] tmp_pstart;
        delete [] tmp_edges;
        delete [] tmp_degree;
        delete [] del;

        cout << "Max GC: " << max_gc_size << ", search space: " << ss << endl;
        cout << "Total Time: " << (double)t.elapsed() / CLOCKS_PER_SEC << "s" << endl;
        return;
    }


    vector<vector<ui>> progress_sim_nei;

    tt.restart();
    restore_all_similar_edges_by_index(tmp_pstart, tmp_edges, del,
                                       residual_sim_nei, z_list, z_R,
                                       progress_sim_nei);
    t_simnei += (double)tt.elapsed() / CLOCKS_PER_SEC;

    unsigned long long similar_edge_cnt = 0;

    for(ui u = 0; u < n; ++u) {
        similar_edge_cnt += progress_sim_nei[u].size();
    }

    cout << "exact remaining graph: |V| = " << n
         << ", structural |E| = " << m / 2
         << ", similar |E| = " << similar_edge_cnt / 2 << endl;


    tt.restart();

    ui exact_deleted_cnt = exact_generalized_core_reduction(tmp_pstart, tmp_edges,
                                                             tmp_degree,
                                                             progress_sim_nei, del);

    t_global_core += (double)tt.elapsed() / CLOCKS_PER_SEC;

    cout << "exact generalized-core deleted = " << exact_deleted_cnt
         << ", remain |V| = " << n << ", structural |E| = " << m / 2 << endl;

    if(n == 0) {
        delete [] tmp_pstart;
        delete [] tmp_edges;
        delete [] tmp_degree;
        delete [] del;

        cout << "the exact generalized core is empty" << endl;
        cout << "Max GC: " << max_gc_size << ", search space: " << ss << endl;

        cout << fixed << setprecision(2);
        double total_time = (double)t.elapsed() / CLOCKS_PER_SEC;

        cout << "Total Time: " << total_time << "s" << endl;
        cout << "\theu solution t = " << t_heu << " s,  " << t_heu / total_time * 100 << " %" << endl;
        cout << "\tindex-based vr = " << t_vr << " s,  " << t_vr / total_time * 100 << " %" << endl;
        cout << "\tsim nei t      = " << t_simnei << " s,  " << t_simnei / total_time * 100 << " %" << endl;
        cout << "\tglobal core t  = " << t_global_core << " s,  " << t_global_core / total_time * 100 << " %" << endl;
        return;
    }


    ui ordering_capacity = n;

    ui* peels = new ui[ordering_capacity];
    ui* vis = new ui[ordering_capacity];
    ui* core = new ui[ordering_capacity];
    ui* rid = new ui[ordering_capacity];
    ui* forward_degree = new ui[ordering_capacity];

    ui max_generalized_core = 0;
    bool optimality_certified = false;

    while(true) {
        tt.restart();

        max_generalized_core =
            compute_degeneracy_ordering_of_tmp_generalized_graph(
                peels, vis, core, rid, forward_degree,
                tmp_pstart, tmp_edges, tmp_degree,
                progress_sim_nei
            );

        ui old_max_gc_size = max_gc_size;

        update_best_clique_by_peeling_suffix(peels, forward_degree);

        t_degen += (double)tt.elapsed() / CLOCKS_PER_SEC;


        assert((ui)max_gc_size <= max_generalized_core + 1);

        if((ui)max_gc_size == max_generalized_core + 1) {
            optimality_certified = true;

            cout << "optimality certified by peeling suffix and degeneracy bound"
                 << endl;

            break;
        }


        if((ui)max_gc_size == old_max_gc_size) {
            break;
        }


        tt.restart();

        ui suffix_vr_deleted =
            exact_generalized_core_reduction(
                tmp_pstart,
                tmp_edges,
                tmp_degree,
                progress_sim_nei,
                del
            );

        t_global_core +=
            (double)tt.elapsed() / CLOCKS_PER_SEC;

        cout << "peeling suffix VR deleted = "
             << suffix_vr_deleted
             << ", remain |V| = "
             << n
             << ", structural |E| = "
             << m / 2
             << endl;


        if(n == 0) {
            optimality_certified = true;

            cout << "exact generalized core becomes empty after suffix VR"
                 << endl;

            break;
        }


        if(suffix_vr_deleted == 0) {
            break;
        }


    }

    if(n > 0) {
        memset(vis, 0, sizeof(ui) * n);
    }

    if(optimality_certified) {
        delete [] forward_degree;
        delete [] peels;
        delete [] vis;
        delete [] core;
        delete [] rid;

        delete [] del;
        delete [] tmp_pstart;
        delete [] tmp_edges;
        delete [] tmp_degree;

        cout << "Max GC: " << max_gc_size
             << ", search space: " << ss << endl;

    #ifdef _CollectRes_
        if(!res.empty()) sort(res[0].begin(), res[0].end());
    #endif

        cout << fixed << setprecision(2);

        double total_time =
            (double)t.elapsed() / CLOCKS_PER_SEC;

        cout << "Total Time: "
             << total_time << "s" << endl;

        cout << "\theu solution t = "
             << t_heu << " s,  "
             << t_heu / total_time * 100 << " %" << endl;

        cout << "\tindex-based vr = "
             << t_vr << " s,  "
             << t_vr / total_time * 100 << " %" << endl;

        cout << "\tsim nei t      = "
             << t_simnei << " s,  "
             << t_simnei / total_time * 100 << " %" << endl;

        cout << "\tglobal core t  = "
             << t_global_core << " s,  "
             << t_global_core / total_time * 100 << " %" << endl;

        cout << "\tdegeneracy t   = "
             << t_degen << " s,  "
             << t_degen / total_time * 100 << " %" << endl;

        return;
    }


    vector<pair<ui,ui>> root_order;
    root_order.reserve(n);

    for(ui u = 0; u < n; ++u) {
        ui forward_degree = 0;

        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];

            if(rid[v] > rid[u]) ++forward_degree;
        }

        for(ui i = 0; i < progress_sim_nei[u].size(); ++i) {
            ui v = progress_sim_nei[u][i];

            if(rid[v] > rid[u]) ++forward_degree;
        }

        ui ub1 = forward_degree + 1;
        ui ub2 = core[u] + 1;
        ui root_ub = min(ub1, ub2);

        root_order.push_back(make_pair(root_ub, u));
    }

    sort(root_order.rbegin(), root_order.rend());


    trs = new ui[n];

    vector<ui> sg_vs(n);
    vector<ui> sg_ve(n);
    vector<ui> sg_e;
    vector<ui> sg_deg(n);

    for(ui task_idx = 0; task_idx < root_order.size(); ++task_idx) {
        ui root_ub = root_order[task_idx].first;
        ui u = root_order[task_idx].second;

        if(root_ub <= (ui)max_gc_size) continue;

        vector<ui> StructNei;


        for(ui i = tmp_pstart[u]; i < tmp_pstart[u+1]; ++i) {
            ui v = tmp_edges[i];

            if(rid[v] > rid[u]) {
                StructNei.push_back(v);
                vis[v] = 1;
            }
        }


        for(ui i = 0; i < progress_sim_nei[u].size(); ++i) {
            ui v = progress_sim_nei[u][i];

            if(rid[v] > rid[u]) {
                StructNei.push_back(v);
                vis[v] = 1;
            }
        }

        if(1 + StructNei.size() <= (ui)max_gc_size) {
            for(ui i = 0; i < StructNei.size(); ++i) vis[StructNei[i]] = 0;
            continue;
        }

        StructNei.push_back(u);
        vis[u] = 1;


        tt.restart();

        build_egosg_and_vr(tmp_pstart, tmp_edges, tmp_degree,
                           StructNei, vis, sg_vs, sg_ve,
                           sg_e, sg_deg, progress_sim_nei);

        t_construct_subgraph += (double)tt.elapsed() / CLOCKS_PER_SEC;

        if(vis[u] == 0) {
            for(ui i = 0; i < StructNei.size(); ++i) vis[StructNei[i]] = 0;
            continue;
        }


        tt.restart();

        ui md = (ui)StructNei.size();

        Matrix = new char*[md];

        size_t matrix_size = (size_t)md * (size_t)md;
        char* matrix_data = new char[matrix_size];

        for(ui i = 0; i < md; ++i) {
            Matrix[i] = matrix_data + (size_t)i * md;
        }

        vector<ui>::iterator it = find(StructNei.begin(), StructNei.end(), u);
        assert(it != StructNei.end());
        StructNei.erase(it);

        build_matrix(u, StructNei, vis, progress_sim_nei,
                     tmp_pstart, tmp_edges, tmp_degree);

        t_build_matrix += (double)tt.elapsed() / CLOCKS_PER_SEC;

        vector<ui> C;
        vector<ui> R;

        C.push_back(u);

        for(ui i = 0; i < StructNei.size(); ++i) {
            R.push_back(StructNei[i]);
        }

        ui target_gc_size = max_gc_size + 1;
        bool reach_target = false;

#ifdef _HeuEgo_
        reach_target = find_a_heu_gc_in_ego(u, R, sg_deg, target_gc_size);
#endif

        if(!reach_target) {
#ifdef _Coloring_
            tt.restart();
            coloring_before_bnb(R, md);
            t_color += (double)tt.elapsed() / CLOCKS_PER_SEC;
#endif

            tt.restart();
            bnb_finding_maximum_gc(C, R, target_gc_size);
            t_bnb += (double)tt.elapsed() / CLOCKS_PER_SEC;
        }


        tt.restart();

        vis[u] = 0;

        for(ui i = 0; i < StructNei.size(); ++i) {
            vis[StructNei[i]] = 0;
        }

        delete [] matrix_data;
        delete [] Matrix;
        Matrix = nullptr;

        t_clear += (double)tt.elapsed() / CLOCKS_PER_SEC;
    }

    delete [] trs;
    trs = nullptr;

    delete [] forward_degree;
    delete [] peels;
    delete [] vis;
    delete [] core;
    delete [] rid;

    delete [] del;
    delete [] tmp_pstart;
    delete [] tmp_edges;
    delete [] tmp_degree;

    cout << "Max GC: " << max_gc_size << ", search space: " << ss << endl;

#ifdef _CollectRes_
    if(!res.empty()) sort(res[0].begin(), res[0].end());
#endif

    cout << fixed << setprecision(2);

    double total_time = (double)t.elapsed() / CLOCKS_PER_SEC;

    cout << "Total Time: " << total_time << "s" << endl;
    cout << "\theu solution t = " << t_heu << " s,  " << t_heu / total_time * 100 << " %" << endl;
    cout << "\tindex-based vr = " << t_vr << " s,  " << t_vr / total_time * 100 << " %" << endl;
    cout << "\tsim nei t      = " << t_simnei << " s,  " << t_simnei / total_time * 100 << " %" << endl;
    cout << "\tglobal core t  = " << t_global_core << " s,  " << t_global_core / total_time * 100 << " %" << endl;
    cout << "\tdegeneracy t   = " << t_degen << " s,  " << t_degen / total_time * 100 << " %" << endl;
    cout << "\tconstruct sg t = " << t_construct_subgraph << " s,  " << t_construct_subgraph / total_time * 100 << " %" << endl;
    cout << "\tbuild matrix t = " << t_build_matrix << " s,  " << t_build_matrix / total_time * 100 << " %" << endl;
    cout << "\tcoloring t     = " << t_color << " s,  " << t_color / total_time * 100 << " %" << endl;
    cout << "\tbnb t          = " << t_bnb << " s,  " << t_bnb / total_time * 100 << " %" << endl;
    cout << "\tcleanup t      = " << t_clear << " s,  " << t_clear / total_time * 100 << " %" << endl;
}

void max_k_core(){
    vector<ui> resS;
    ui * peel_sequence = new ui[n];
    ui * core = new ui[n];
    ui * vis = new ui[n];
    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    memset(vis, 0, sizeof(ui)*n);
    for(ui i = 0; i < n; i++) peel_sequence[i] = i;

    heap->init(n, n-1, peel_sequence, degree);
    ui max_core = 0;

    for(ui i = 0;i < n; i ++) {
        ui u, key;
        heap->pop_min(u, key);


        if(key > max_core) max_core = key;
        core[u] = max_core;
        peel_sequence[i] = u;
        vis[u] = 1;
        for(ui j = pstart[u]; j < pstart[u+1]; j ++) if(vis[edges[j]] == 0) {
            heap->decrement(edges[j], 1);

        }
    }
    cout<<"largest k - core: "<<max_core<<endl;
    for(ui i = 0; i < n; ++i) if(core[i]==max_core) cout<<i<<",";
    cout<<endl;
}

void densest_subgraph() {
    vector<ui> resS;

    ui *peel_sequence = new ui[n];
    ui *vis = new ui[n];

    memset(vis, 0, sizeof(ui) * n);

    for(ui i = 0; i < n; i++)
        peel_sequence[i] = i;

    ListLinearHeap *heap = new ListLinearHeap(n, n - 1);
    heap->init(n, n - 1, peel_sequence, degree);


    uint64_t current_edges = 0;
    for(ui i = 0; i < n; i++)
        current_edges += degree[i];
    current_edges /= 2;

    ui current_vertices = n;

    double max_density = -1.0;
    double max_avg_degree = -1.0;


    ui best_start = 0;

    for(ui i = 0; i < n; i++) {


        if(current_vertices > 0) {
            double density =
                (double)current_edges / (double)current_vertices;

            double avg_degree =
                2.0 * (double)current_edges /
                (double)current_vertices;

            if(density > max_density) {
                max_density = density;
                max_avg_degree = avg_degree;
                best_start = i;
            }
        }


        ui u, key;
        heap->pop_min(u, key);

        peel_sequence[i] = u;
        vis[u] = 1;


        current_edges -= key;
        current_vertices--;


        for(ui j = pstart[u]; j < pstart[u + 1]; j++) {
            ui v = edges[j];

            if(vis[v] == 0) {
                heap->decrement(v, 1);
            }
        }
    }


    for(ui i = best_start; i < n; i++)
        resS.push_back(peel_sequence[i]);

    cout << "densest subgraph:" << endl;
    cout << "vertices = " << resS.size() << endl;
    cout << "edges/vertices density = " << max_density << endl;
    cout << "average degree = " << max_avg_degree << endl;

    cout << "vertex set: ";
    for(ui u : resS)
        cout << u << ",";
    cout << endl;

    delete[] peel_sequence;
    delete[] vis;
    delete heap;
}


class FastDinic {
public:
    struct Edge {
        int to;
        int next;
        i64 cap;
    };

    int N;
    vector<int> head, level, cur, que;
    vector<Edge> E;

    FastDinic(int n): N(n), head(n, -1), level(n), cur(n), que(n) {}

    void reserve_edges(size_t sz) {
        E.reserve(sz);
    }


    void addDirected(int u, int v, i64 cap) {
        E.push_back({v, head[u], cap});
        head[u] = (int)E.size() - 1;

        E.push_back({u, head[v], 0});
        head[v] = (int)E.size() - 1;
    }


    void addUndirected(int u, int v, i64 cap) {
        E.push_back({v, head[u], cap});
        head[u] = (int)E.size() - 1;

        E.push_back({u, head[v], cap});
        head[v] = (int)E.size() - 1;
    }

    bool bfs(int s, int t) {
        fill(level.begin(), level.end(), -1);

        int l = 0, r = 0;
        que[r++] = s;
        level[s] = 0;

        while(l < r) {
            int u = que[l++];

            for(int i = head[u]; i != -1; i = E[i].next) {
                if(E[i].cap > 0 && level[E[i].to] == -1) {
                    level[E[i].to] = level[u] + 1;
                    que[r++] = E[i].to;
                }
            }
        }

        return level[t] != -1;
    }

    i64 dfs(int u, int t, i64 f) {
        if(u == t)
            return f;

        for(int &i = cur[u]; i != -1; i = E[i].next) {
            Edge &e = E[i];

            if(e.cap > 0 && level[e.to] == level[u] + 1) {
                i64 ret = dfs(e.to, t, min(f, e.cap));

                if(ret > 0) {
                    e.cap -= ret;
                    E[i ^ 1].cap += ret;
                    return ret;
                }
            }
        }

        return 0;
    }

    i128 maxflow(int s, int t) {
        i128 flow = 0;

        while(bfs(s, t)) {
            cur = head;

            while(true) {
                i64 f = dfs(s, t, numeric_limits<i64>::max() / 4);

                if(f == 0)
                    break;

                flow += (i128)f;
            }
        }

        return flow;
    }


    vector<char> sourceSide(int s) {
        vector<char> vis(N, 0);

        int l = 0, r = 0;
        que[r++] = s;
        vis[s] = 1;

        while(l < r) {
            int u = que[l++];

            for(int i = head[u]; i != -1; i = E[i].next) {
                if(E[i].cap > 0 && !vis[E[i].to]) {
                    vis[E[i].to] = 1;
                    que[r++] = E[i].to;
                }
            }
        }

        return vis;
    }
};

void exact_densest_subgraph() {
    if(n == 0) return;


    vector<ui> peel_sequence(n);
    vector<ui> core(n);
    vector<ui> vis(n, 0);

    for(ui i = 0; i < n; i++)
        peel_sequence[i] = i;

    uint64_t m = 0;

    for(ui i = 0; i < n; i++)
        m += degree[i];

    m /= 2;

    ListLinearHeap *heap = new ListLinearHeap(n, n - 1);
    heap->init(n, n - 1, peel_sequence.data(), degree);

    uint64_t current_m = m;
    ui current_n = n;

    uint64_t best_edges = current_m;
    ui best_vertices = current_n;
    ui best_start = 0;

    ui max_core = 0;

    for(ui i = 0; i < n; i++) {


        if(current_n > 0 &&
           (i128)current_m * best_vertices >
           (i128)best_edges * current_n) {

            best_edges = current_m;
            best_vertices = current_n;
            best_start = i;
        }

        ui u, key;
        heap->pop_min(u, key);

        if(key > max_core)
            max_core = key;

        core[u] = max_core;
        peel_sequence[i] = u;
        vis[u] = 1;

        current_m -= key;
        current_n--;

        for(ui j = pstart[u]; j < pstart[u + 1]; j++) {
            ui v = edges[j];

            if(vis[v] == 0)
                heap->decrement(v, 1);
        }
    }

    delete heap;

    vector<ui> bestS;

    for(ui i = best_start; i < n; i++)
        bestS.push_back(peel_sequence[i]);


    uint64_t g = std::gcd(best_edges, (uint64_t)best_vertices);

    uint64_t p = best_edges / g;
    uint64_t q = best_vertices / g;

    cout << "Initial greedy lower bound: "
         << best_edges << "/" << best_vertices
         << " = " << (double)best_edges / best_vertices << endl;

    cout << "Initial size: " << best_vertices << endl;
    cout << "max core: " << max_core << endl;


    vector<int> lid(n);

    int iteration = 0;


    while(true) {
        iteration++;


        uint64_t k64 = p / q + 1;

        if(k64 > max_core) {
            cout << "No higher core exists. Optimality certified." << endl;
            break;
        }

        ui k = (ui)k64;

        vector<ui> gids;
        gids.reserve(n);

        for(ui u = 0; u < n; u++) {
            if(core[u] >= k) {
                lid[u] = (int)gids.size();
                gids.push_back(u);
            }
        }

        ui local_n = (ui)gids.size();

        if(local_n == 0) {
            cout << "Candidate core is empty. Optimality certified." << endl;
            break;
        }


        vector<ui> local_degree(local_n, 0);

        uint64_t degree_sum = 0;
        ui B = 0;

        for(ui i = 0; i < local_n; i++) {
            ui u = gids[i];
            ui d = 0;

            for(ui j = pstart[u]; j < pstart[u + 1]; j++) {
                ui v = edges[j];

                if(core[v] >= k)
                    d++;
            }

            local_degree[i] = d;
            degree_sum += d;

            if(d > B)
                B = d;
        }

        uint64_t local_m = degree_sum / 2;

        cout << "flow iteration " << iteration
             << ": density = " << (double)p / q
             << ", k = " << k
             << ", |V_core| = " << local_n
             << ", |E_core| = " << local_m << endl;


        int source = local_n;
        int sink = local_n + 1;

        FastDinic flow(local_n + 2);

        uint64_t required_arcs =
            4ULL * local_n +
            2ULL * local_m +
            16;

        flow.reserve_edges((size_t)required_arcs);

        i128 source_cap_128 = (i128)B * q;

        if(source_cap_128 > numeric_limits<i64>::max() / 4) {
            cerr << "ERROR: flow capacity overflow." << endl;
            exit(1);
        }

        i64 source_cap = (i64)source_cap_128;

        for(ui i = 0; i < local_n; i++) {

            i128 sink_cap_128 =
                (i128)(B - local_degree[i]) * q +
                (i128)2 * p;

            if(sink_cap_128 > numeric_limits<i64>::max() / 4) {
                cerr << "ERROR: flow capacity overflow." << endl;
                exit(1);
            }

            i64 sink_cap = (i64)sink_cap_128;

            flow.addDirected(source, i, source_cap);
            flow.addDirected(i, sink, sink_cap);
        }


        for(ui i = 0; i < local_n; i++) {
            ui u = gids[i];

            for(ui j = pstart[u]; j < pstart[u + 1]; j++) {
                ui v = edges[j];

                if(core[v] >= k && u < v) {
                    flow.addUndirected(
                        i,
                        lid[v],
                        (i64)q
                    );
                }
            }
        }


        i128 BASE =
            (i128)B *
            q *
            local_n;

        i128 F = flow.maxflow(source, sink);


        if(F == BASE) {
            cout << "Maximum-flow certificate obtained." << endl;
            cout << "No subgraph has density > "
                 << (double)p / q << endl;
            break;
        }


        vector<char> side = flow.sourceSide(source);

        vector<ui> newS;
        newS.reserve(local_n);

        for(ui i = 0; i < local_n; i++) {
            if(side[i])
                newS.push_back(gids[i]);
        }

        uint64_t new_vertices = newS.size();

        if(new_vertices == 0) {
            cerr << "ERROR: unexpected empty min-cut solution." << endl;
            break;
        }


        i128 objective = (BASE - F) / 2;

        i128 new_edges_128 =
            (objective +
             (i128)p * new_vertices) / q;

        uint64_t new_edges =
            (uint64_t)new_edges_128;


        if((i128)new_edges * q <=
           (i128)p * new_vertices) {

            cerr << "ERROR: density did not increase." << endl;
            break;
        }

        bestS.swap(newS);
        best_edges = new_edges;
        best_vertices = new_vertices;


        uint64_t gg =
            std::gcd(best_edges,
                     (uint64_t)best_vertices);

        p = best_edges / gg;
        q = best_vertices / gg;

        cout << "  improved -> |V| = "
             << best_vertices
             << ", |E| = "
             << best_edges
             << ", density = "
             << (double)best_edges / best_vertices
             << endl;
    }


    cout << endl;
    cout << "==========================================" << endl;
    cout << "Exact Densest Subgraph" << endl;
    cout << "==========================================" << endl;

    cout << "|V| = " << best_vertices << endl;
    cout << "|E| = " << best_edges << endl;

    cout << "density |E|/|V| = "
         << setprecision(12)
         << (double)best_edges / best_vertices
         << endl;

    cout << "average degree = "
         << setprecision(12)
         << 2.0 * best_edges / best_vertices
         << endl;

    cout << "vertices:" << endl;

    for(ui u : bestS)
        cout << u << ",";

    cout << endl;
}

void heuristic_max_kplex(ui k, double time_limit_sec = 10.0, int quality = 5, uint64_t random_seed = 1) {
    if(n == 0 || k == 0) return;

    if(quality < 1) quality = 1;
    if(quality > 20) quality = 20;

    using Clock = std::chrono::steady_clock;
    auto begin_time = Clock::now();
    auto expired = [&]() -> bool {
        return std::chrono::duration<double>(Clock::now() - begin_time).count() >= time_limit_sec;
    };

    std::mt19937_64 rng(random_seed);


    auto adjacent = [&](ui u, ui v) -> bool {
        if(u == v) return false;
        return std::binary_search(edges + pstart[u], edges + pstart[u + 1], v);
    };


    const size_t eval_cap = (size_t)256 * quality;
    const size_t swap_candidate_cap = (size_t)16 * quality;
    const size_t seed_sample_cap = (size_t)64 * quality;
    const int max_swap_rounds = 8 * quality;


    std::vector<int> cnt(n, 0);
    std::vector<int> cnt_stamp(n, 0);
    std::vector<int> cand_stamp(n, 0);
    std::vector<char> inS(n, 0);

    int epoch = 0;

    auto get_cnt = [&](ui v) -> int {
        if(cnt_stamp[v] != epoch) return 0;
        return cnt[v];
    };

    auto inc_cnt = [&](ui v) {
        if(cnt_stamp[v] != epoch) {
            cnt_stamp[v] = epoch;
            cnt[v] = 0;
        }
        ++cnt[v];
    };

    auto dec_cnt = [&](ui v) {
        if(cnt_stamp[v] != epoch) {
            cnt_stamp[v] = epoch;
            cnt[v] = 0;
        }
        --cnt[v];
    };


    ui max_degree_vertex = 0;

    for(ui u = 1; u < n; ++u) {
        if(degree[u] > degree[max_degree_vertex])
            max_degree_vertex = u;
    }

    std::vector<ui> bestS;
    bestS.push_back(max_degree_vertex);

    uint64_t restart_cnt = 0;
    uint64_t total_swap_cnt = 0;


    while(!expired()) {
        ++restart_cnt;
        ++epoch;


        if(epoch == std::numeric_limits<int>::max()) {
            std::fill(cnt_stamp.begin(), cnt_stamp.end(), 0);
            std::fill(cand_stamp.begin(), cand_stamp.end(), 0);
            epoch = 1;
        }

        std::vector<ui> S;
        std::vector<ui> candidates;

        S.reserve(bestS.size() + 64);
        candidates.reserve(1024);


        ui target_size = (ui)bestS.size() + 1;
        ui global_degree_lb = 0;

        if(target_size > k)
            global_degree_lb = target_size - k;


        auto add_candidate = [&](ui v) {
            if(inS[v]) return;

            if(cand_stamp[v] != epoch) {
                cand_stamp[v] = epoch;
                candidates.push_back(v);
            }
        };


        auto add_vertex = [&](ui u) {
            inS[u] = 1;
            S.push_back(u);

            for(ui j = pstart[u]; j < pstart[u + 1]; ++j) {
                ui v = edges[j];

                inc_cnt(v);

                if(!inS[v])
                    add_candidate(v);
            }
        };


        ui seed = max_degree_vertex;

        if(restart_cnt > 1) {
            ui best_seed = (ui)(rng() % n);
            bool found = false;

            size_t samples =
                std::min<size_t>((size_t)n, seed_sample_cap);

            for(size_t x = 0; x < samples; ++x) {
                ui u = (ui)(rng() % n);

                if(degree[u] < global_degree_lb)
                    continue;

                if(!found || degree[u] > degree[best_seed]) {
                    best_seed = u;
                    found = true;
                }
            }

            if(found)
                seed = best_seed;
        }

        add_vertex(seed);


        if(k > 1) {
            size_t inject = (size_t)32 * quality;

            for(size_t x = 0; x < inject; ++x) {
                ui v = (ui)(rng() % n);

                if(degree[v] >= global_degree_lb)
                    add_candidate(v);
            }
        }

        int swap_rounds = 0;


        while(!expired()) {
            const ui s = (ui)S.size();


            std::vector<ui> critical;
            critical.reserve(S.size());

            for(ui u : S) {
                int miss = (int)s - 1 - get_cnt(u);

                if(miss == (int)k - 1)
                    critical.push_back(u);
            }


            auto feasible_add = [&](ui v) -> bool {
                if(inS[v])
                    return false;

                if(degree[v] < global_degree_lb)
                    return false;

                int dv = get_cnt(v);


                if((int)s - dv > (int)k - 1)
                    return false;


                for(ui u : critical) {
                    if(!adjacent(u, v))
                        return false;
                }

                return true;
            };


            ui best_v = n;
            ui second_v = n;

            uint64_t best_score = 0;
            uint64_t second_score = 0;

            auto evaluate_vertex = [&](ui v) {
                if(!feasible_add(v))
                    return;

                uint64_t inside_degree =
                    (uint64_t)get_cnt(v);


                uint64_t score =
                    inside_degree * ((uint64_t)n + 1ULL)
                    + degree[v];

                if(best_v == n || score > best_score) {
                    second_v = best_v;
                    second_score = best_score;

                    best_v = v;
                    best_score = score;
                }
                else if(second_v == n || score > second_score) {
                    second_v = v;
                    second_score = score;
                }
            };

            if(candidates.size() <= eval_cap) {
                for(ui v : candidates)
                    evaluate_vertex(v);
            }
            else {

                for(size_t x = 0; x < eval_cap; ++x) {
                    ui v =
                        candidates[(size_t)(rng() % candidates.size())];

                    evaluate_vertex(v);
                }


                size_t recent =
                    std::min<size_t>(eval_cap / 4,
                                     candidates.size());

                for(size_t x = 0; x < recent; ++x) {
                    ui v =
                        candidates[candidates.size() - 1 - x];

                    evaluate_vertex(v);
                }
            }


            if(best_v != n) {


                ui chosen = best_v;

                if(restart_cnt > 1 &&
                   second_v != n &&
                   (rng() % 100) < 15) {
                    chosen = second_v;
                }

                add_vertex(chosen);


                if(S.size() < k) {
                    size_t inject = (size_t)8 * quality;

                    for(size_t x = 0; x < inject; ++x) {
                        ui v = (ui)(rng() % n);

                        if(degree[v] >= global_degree_lb)
                            add_candidate(v);
                    }
                }

                if(S.size() > bestS.size()) {
                    bestS = S;

                    target_size = (ui)bestS.size() + 1;

                    global_degree_lb =
                        target_size > k ?
                        target_size - k : 0;

                    cout << "[k-plex] improved: |S| = "
                         << bestS.size()
                         << ", restart = "
                         << restart_cnt
                         << endl;
                }

                continue;
            }


            if(swap_rounds >= max_swap_rounds)
                break;

            ui swap_in = n;
            ui swap_out = n;
            uint64_t best_gain = 0;

            size_t checked_swap_candidates = 0;

            auto try_swap_candidate = [&](ui v) {
                if(inS[v])
                    return;

                if(degree[v] < global_degree_lb)
                    return;

                int dv = get_cnt(v);


                int miss_v = (int)s - dv;

                if(miss_v > (int)k)
                    return;


                std::vector<ui> conflict;
                conflict.reserve(k);

                for(ui u : critical) {
                    if(!adjacent(u, v))
                        conflict.push_back(u);
                }


                for(ui r : S) {
                    bool vr_adj = adjacent(v, r);


                    if(miss_v == (int)k && vr_adj)
                        continue;

                    bool ok = true;


                    for(ui u : conflict) {
                        if(r == u)
                            continue;

                        if(adjacent(r, u)) {
                            ok = false;
                            break;
                        }
                    }

                    if(!ok)
                        continue;

                    int gain =
                        dv
                        - (vr_adj ? 1 : 0)
                        - get_cnt(r);


                    if(gain <= 0)
                        continue;

                    if(swap_in == n ||
                       (uint64_t)gain > best_gain) {
                        swap_in = v;
                        swap_out = r;
                        best_gain = (uint64_t)gain;
                    }
                }
            };

            if(candidates.size() <= swap_candidate_cap) {
                for(ui v : candidates) {
                    try_swap_candidate(v);

                    if(++checked_swap_candidates >=
                       swap_candidate_cap)
                        break;
                }
            }
            else {
                for(size_t x = 0;
                    x < swap_candidate_cap;
                    ++x) {

                    ui v =
                        candidates[(size_t)(rng() %
                                            candidates.size())];

                    try_swap_candidate(v);
                }
            }

            if(swap_in == n)
                break;


            size_t remove_pos = 0;

            for(size_t i = 0; i < S.size(); ++i) {
                if(S[i] == swap_out) {
                    remove_pos = i;
                    break;
                }
            }


            inS[swap_out] = 0;

            for(ui j = pstart[swap_out];
                j < pstart[swap_out + 1];
                ++j) {
                dec_cnt(edges[j]);
            }

            add_candidate(swap_out);


            S[remove_pos] = swap_in;
            inS[swap_in] = 1;

            for(ui j = pstart[swap_in];
                j < pstart[swap_in + 1];
                ++j) {

                ui v = edges[j];

                inc_cnt(v);

                if(!inS[v])
                    add_candidate(v);
            }

            ++swap_rounds;
            ++total_swap_cnt;
        }


        for(ui u : S)
            inS[u] = 0;
    }


    std::vector<char> best_mark(n, 0);

    for(ui u : bestS)
        best_mark[u] = 1;

    uint64_t degree_sum = 0;
    ui max_missing = 0;
    bool valid = true;

    for(ui u : bestS) {
        ui din = 0;

        for(ui j = pstart[u];
            j < pstart[u + 1];
            ++j) {

            if(best_mark[edges[j]])
                ++din;
        }

        ui missing =
            (ui)bestS.size() - 1 - din;

        degree_sum += din;

        if(missing > max_missing)
            max_missing = missing;

        if(missing > k - 1)
            valid = false;
    }

    uint64_t internal_edges = degree_sum / 2;

    double elapsed =
        std::chrono::duration<double>(
            Clock::now() - begin_time).count();

    cout << endl;
    cout << "==========================================" << endl;
    cout << "Heuristic Maximum " << k << "-Plex" << endl;
    cout << "==========================================" << endl;
    cout << "|V| = " << bestS.size() << endl;
    cout << "|E| = " << internal_edges << endl;

    if(bestS.size() > 1) {
        double density =
            2.0 * internal_edges /
            ((double)bestS.size() *
             (bestS.size() - 1));

        cout << "edge density = "
             << density << endl;
    }

    cout << "max missing neighbors = "
         << max_missing
         << " (allowed <= "
         << k - 1 << ")" << endl;

    cout << "valid k-plex = "
         << (valid ? "YES" : "NO") << endl;

    cout << "restarts = "
         << restart_cnt << endl;

    cout << "accepted swaps = "
         << total_swap_cnt << endl;

    cout << "time = "
         << elapsed << " sec" << endl;

    cout << "vertices:" << endl;

    for(ui u : bestS)
        cout << u << ",";

    cout << endl;
}

static void print_usage() {
    cout << "Usage:\n"
         << "  query <data_dir> <graph> <epsilon> <size_threshold> <mode> <method> [parameters]\n\n"
         << "Global computation:\n"
         << "  global MGC-Mat\n"
         << "  global Mat-Prog\n"
         << "  global MGC-DB  <index_build> <tau> <max_round> <k> <bands> <threshold> <rho> <min_cluster> <min_gain>\n"
         << "  global MGC-BC  <tau> <max_round> <min_cluster> <min_gain>\n"
         << "\n"
         << "Vertex query:\n"
         << "  vertex MGC-Mat <query_vertex>\n"
         << "  vertex MGC-DB  <query_vertex> <index_build> <tau> <max_round> <k> <bands> <threshold> <rho> <min_cluster> <min_gain>\n"
         << "\n"
         << "For MGC-DB, <index_build> is standard or batch.\n"
         << "Index files are loaded from ./index/.\n";
}

static string db_index_tag(const string& build_mode) {
    if(build_mode == "standard") return "DB";
    if(build_mode == "batch") return "DBBatch";
    return "";
}

int main(int argc, const char * argv[]) {
    if(argc < 7) {
        print_usage();
        return 1;
    }

    const string data_dir = argv[1];
    const string graph_name = argv[2];
    epsi = stod(argv[3]);
    sz = stoi(argv[4]);
    const string mode = argv[5];
    const string method = argv[6];

    if(epsi < 0.0 || epsi > 1.0) {
        cerr << "Error: epsilon must be in [0,1].\n";
        return 1;
    }

    read_graph_binary(data_dir, graph_name);

    cout << "graph: " << graph_name << " (n=" << n << ", m=" << m << ")\n"
         << "epsilon: " << epsi << "\n"
         << "size threshold: " << sz << "\n"
         << "mode: " << mode << ", method: " << method << endl;

    if(mode == "global") {
        if(method == "MGC-Mat") {
            if(argc != 7) {
                print_usage();
                release_mem();
                return 1;
            }
            maximum_generalized_clique_computation_by_materialization();
        }
        else if(method == "Mat-Prog") {
            if(argc != 7) {
                print_usage();
                release_mem();
                return 1;
            }
            maximum_generalized_clique_computation_Prog();
        }
        else if(method == "MGC-DB") {
            if(argc != 16) {
                print_usage();
                release_mem();
                return 1;
            }

            const string index_tag = db_index_tag(argv[7]);
            if(index_tag.empty()) {
                cerr << "Error: MGC-DB index_build must be standard or batch.\n";
                release_mem();
                return 1;
            }

            vector<vector<pair<double,ui>>> residual_sim_nei;
            vector<vector<ui>> z_list;
            ui z_idx = 0;
            vector<vector<pair<double,ui>>> z_R;

            const int tau = atoi(argv[8]);
            const int max_round = atoi(argv[9]);
            const ui k = (ui)atoi(argv[10]);
            const ui bands = (ui)atoi(argv[11]);
            const double threshold = atof(argv[12]);
            const double rho = atof(argv[13]);
            const ui min_cluster = (ui)atoi(argv[14]);
            const ui min_gain = (ui)atoi(argv[15]);

            load_index(graph_name, index_tag,
                       residual_sim_nei, z_list, z_idx, z_R,
                       tau, max_round, k, bands,
                       threshold, rho, min_cluster, min_gain);

            maximum_generalized_clique_computation_by_index_adv(
                residual_sim_nei, z_list, z_idx, z_R);
        }
        else if(method == "MGC-BC") {
            if(argc != 11) {
                print_usage();
                release_mem();
                return 1;
            }

            vector<vector<pair<double,ui>>> residual_sim_nei;
            vector<vector<ui>> z_list;
            ui z_idx = 0;
            vector<vector<pair<double,ui>>> z_R;

            const int tau = atoi(argv[7]);
            const int max_round = atoi(argv[8]);
            const ui min_cluster = (ui)atoi(argv[9]);
            const ui min_gain = (ui)atoi(argv[10]);

            load_index_bc(graph_name, "BC",
                          residual_sim_nei, z_list, z_idx, z_R,
                          tau, max_round, min_cluster, min_gain);

            maximum_generalized_clique_computation_by_index_adv(
                residual_sim_nei, z_list, z_idx, z_R);
        }
else {
            cerr << "Error: unknown method '" << method << "'.\n";
            print_usage();
            release_mem();
            return 1;
        }
    }
    else if(mode == "vertex") {
        if(argc < 8) {
            print_usage();
            release_mem();
            return 1;
        }

        const ui query_vertex = (ui)stoul(argv[7]);
        if(query_vertex >= n) {
            cerr << "Error: query vertex " << query_vertex
                 << " is outside [0," << (n == 0 ? 0 : n - 1) << "].\n";
            release_mem();
            return 1;
        }

        if(method == "MGC-Mat") {
            if(argc != 8) {
                print_usage();
                release_mem();
                return 1;
            }
            maximum_generalized_clique_computation_query(query_vertex);
        }
        else if(method == "MGC-DB") {
            if(argc != 17) {
                print_usage();
                release_mem();
                return 1;
            }

            const string index_tag = db_index_tag(argv[8]);
            if(index_tag.empty()) {
                cerr << "Error: MGC-DB index_build must be standard or batch.\n";
                release_mem();
                return 1;
            }

            vector<vector<pair<double,ui>>> residual_sim_nei;
            vector<vector<ui>> z_list;
            ui z_idx = 0;
            vector<vector<pair<double,ui>>> z_R;

            const int tau = atoi(argv[9]);
            const int max_round = atoi(argv[10]);
            const ui k = (ui)atoi(argv[11]);
            const ui bands = (ui)atoi(argv[12]);
            const double threshold = atof(argv[13]);
            const double rho = atof(argv[14]);
            const ui min_cluster = (ui)atoi(argv[15]);
            const ui min_gain = (ui)atoi(argv[16]);

            load_index(graph_name, index_tag,
                       residual_sim_nei, z_list, z_idx, z_R,
                       tau, max_round, k, bands,
                       threshold, rho, min_cluster, min_gain);

            maximum_generalized_clique_computation_by_index_adv_query(
                residual_sim_nei, z_list, z_idx, z_R, query_vertex);
        }
        else {
            cerr << "Error: vertex mode supports MGC-Mat and MGC-DB.\n";
            print_usage();
            release_mem();
            return 1;
        }
    }
    else {
        cerr << "Error: mode must be global or vertex.\n";
        print_usage();
        release_mem();
        return 1;
    }

    release_mem();
    return 0;
}
