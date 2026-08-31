

#include "Timer.h"
#include "Utility.h"
#include "LinearHeap.h"

ui n, m;
ui * pstart;
ui * edges;
ui * degree;

class Itval
{
public:
        ui s_idx;
        ui e_idx;
        double min_score;
        double max_score;
        int c;
    Itval() {
        s_idx = 0;
        e_idx = 0;
        min_score = 0;
        max_score = 0;
        c = 0;
    }
    Itval(ui _s, ui _e, double _mins, double _maxs, int _c){
        s_idx = _s;
        e_idx = _e;
        min_score = _mins;
        max_score = _maxs;
        c = _c;
    }
};

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
    cout<<"graph: "<<name<<", n: "<<n<<", m: "<<m<<endl;
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


#endif
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

void build_vsn_index(string dir, string name, double omit_score_lb, int thre_make_seg, double seg_num_times )
{
    cout<<"*** build index large gap ***"<<endl;
    cout<<"*** omit_score_lb: "<<omit_score_lb<<", thre_make_seg: "<<thre_make_seg<<", seg_num_times: "<<seg_num_times<<" ***"<<endl;

    vector<int> INDEX_vid;
    vector<ui> INDEX_flag;
    vector<vector<Itval>> INDEX_list;

    Timer tt;
    long long T_find_2hopneis = 0;
    long long T_cal_sim_and_sort_for_each = 0;
    long long T_build_ranges = 0;

    long long make_seg_total_number = 0;
    long long make_idvidual = 0;
    long long make_seg = 0;


    ui * c = new ui[n];
    memset(c, 0, sizeof(ui)*n);
    for(ui u = 0; u < n; u++){

        if(u%1000000==0) cout<<"v"<<u/1000000<<"m "; cout.flush();
#ifdef _CheckInfo_
        cout<<"processing vertex "<<u<<endl;
#endif
        tt.restart();

#ifdef _CostlyDebug_
        for(ui i = 0; i < n; ++i) assert(c[i]==0);
#endif

        vector<ui> two_hop_nei;

        for(ui i = pstart[u]; i < pstart[u+1]; i++) c[edges[i]] = 1;
        for(ui i = pstart[u]; i < pstart[u+1]; i++) {
            ui v = edges[i];
            for(ui j = pstart[v]; j < pstart[v+1]; ++j) {
                ui w = edges[j];
                if(w==u) continue;
                if(c[w]==0) two_hop_nei.push_back(w);
                ++c[w];
            }
        }
        for(ui i = pstart[u]; i < pstart[u+1]; i++) {
            assert(c[edges[i]]>0);
            c[edges[i]] = 0;
        }

        T_find_2hopneis += tt.elapsed();
        tt.restart();

        vector<pair<ui, double>> ordered_2hop_neis;
        for(auto e : two_hop_nei){
            assert(c[e]>0);
            assert(degree[u] >= c[e]);
            assert(degree[e] >= c[e]);
            double simscore = (double) c[e] / (degree[u] + degree[e] - c[e]);
            if(simscore >= omit_score_lb && c[e]>=ComNeiThre)
                ordered_2hop_neis.push_back(make_pair(e, simscore));
            c[e] = 0;
        }

        if(ordered_2hop_neis.empty()) continue;

        ++ make_seg_total_number;

        sort(ordered_2hop_neis.begin(), ordered_2hop_neis.end(), less<>());

#ifdef _CheckInfo_
        cout<<"ordered_2hop_neis: "<<endl;
        for(auto e : ordered_2hop_neis)
            cout<<"\t id:"<<e.first<<", score:"<<e.second<<endl;
#endif

        T_cal_sim_and_sort_for_each += tt.elapsed();
        tt.restart();


        assert(ordered_2hop_neis.size() >= 1);

        INDEX_vid.push_back(u);

        if(ordered_2hop_neis.size() < thre_make_seg){
#ifdef _CheckInfo_
        cout<<"Do no Make Segment !"<<endl;
#endif
            vector<Itval> tmpV;
            for(auto e : ordered_2hop_neis){
                tmpV.push_back(Itval(e.first, e.first, e.second, e.second, 1));
            }
            INDEX_list.push_back(tmpV);
            INDEX_flag.push_back(1);
            ++ make_idvidual;
        }
        else{
#ifdef _CheckInfo_
        cout<<"Make Segment !"<<endl;
#endif
            vector<Itval> tmpV;
            assert(ordered_2hop_neis.size() >= thre_make_seg);
            assert(ordered_2hop_neis.size() >= 2);
            int gc = (int)log2(ordered_2hop_neis.size());
            assert(gc < ordered_2hop_neis.size());
            gc = gc * seg_num_times;
            if(gc < 1) gc = 1;
            if(gc > ordered_2hop_neis.size()-1) gc = ordered_2hop_neis.size()-1;
            priority_queue<pair<int, ui>, vector<pair<int, ui>>, greater<pair<int, ui>>> kset;


            for(ui i = 0; i < gc; i++){
                int gap_value = ordered_2hop_neis[i+1].first - ordered_2hop_neis[i].first;
                assert(gap_value >= 1);
                kset.push(make_pair(gap_value, i));
            }
            for(ui i = gc; i < ordered_2hop_neis.size() - 1; i++){
                int gap_value = ordered_2hop_neis[i+1].first - ordered_2hop_neis[i].first;
                assert(gap_value >= 1);
                if(gap_value > kset.top().first){
                    kset.pop();
                    kset.push(make_pair(gap_value, i));
                }
            }
            assert(kset.size() == gc);


            vector<ui> positions;
            while (!kset.empty()) {
                ui idx = kset.top().second;
                positions.push_back(idx);
                kset.pop();
            }
            assert(positions.size() == gc);
            sort(positions.begin(), positions.end(), less<>());

#ifdef _CheckInfo_
        cout<<"positions: "<<endl;
        for(auto e : positions) cout<<e<<", "; cout<<endl;
#endif

            double minS, maxS;
            ui start_idx = 0;
            for(ui i = 0; i < positions.size(); i++){
                ui end_idx = positions[i];
                assert(end_idx >= start_idx);

                minS = INF;
                maxS = 0;
                for(ui j = start_idx; j <= end_idx; j++){
                    if(ordered_2hop_neis[j].second < minS) minS = ordered_2hop_neis[j].second;
                    if(ordered_2hop_neis[j].second > maxS) maxS = ordered_2hop_neis[j].second;
                }

                tmpV.push_back(Itval(ordered_2hop_neis[start_idx].first, ordered_2hop_neis[end_idx].first, minS, maxS, end_idx-start_idx+1));
                start_idx = end_idx + 1;
            }
            minS = INF;
            maxS = 0;
            for(ui i = start_idx; i < ordered_2hop_neis.size(); i ++){
                if(ordered_2hop_neis[i].second < minS) minS = ordered_2hop_neis[i].second;
                if(ordered_2hop_neis[i].second > maxS) maxS = ordered_2hop_neis[i].second;
            }

            tmpV.push_back(Itval(ordered_2hop_neis[start_idx].first, ordered_2hop_neis[ordered_2hop_neis.size()-1].first, minS, maxS, ordered_2hop_neis.size() - start_idx));
            INDEX_list.push_back(tmpV);
            INDEX_flag.push_back(2);
            ++ make_seg;
        }

        T_build_ranges += tt.elapsed();
        tt.restart();

    }

#ifdef _CheckInfo_
    cout<<"INDEX_list:"<<endl;
    for(ui i = 0; i < INDEX_vid.size(); i++) {
        cout<<endl<<"\tvertex : "<<INDEX_vid[i]<<endl;
        cout<<"\t\tnum : "<<INDEX_list[i].size()<<endl;
        if(INDEX_flag[i] == 1) {
            for(auto &e : INDEX_list[i]) {
                cout<<"\t\t\ts_idx:"<<e.s_idx<<endl;
                cout<<"\t\t\te_idx:"<<e.e_idx<<endl;

                cout<<"\t\t\tmin_score:"<<e.min_score<<endl;
                cout<<"\t\t\tmax_score:"<<e.max_score<<endl;
                cout<<"\t\t\tc:"<<e.c<<endl;
            }
        }
        else {
            for(auto &e : INDEX_list[i]) {
                cout<<"\t\t\ts_idx:"<<e.s_idx<<endl;
                cout<<"\t\t\te_idx:"<<e.e_idx<<endl;

                cout<<"\t\t\tmin_score:"<<e.min_score<<endl;
                cout<<"\t\t\tmax_score:"<<e.max_score<<endl;
                cout<<"\t\t\tc:"<<e.c<<endl;
            }
        }
    }
#endif

    long long totalT = T_find_2hopneis + T_cal_sim_and_sort_for_each + T_build_ranges;

    cout<<fixed<<setprecision(2)<<endl;
    cout<<"\tT_find_2hopneis  = "<<(T_find_2hopneis)<<" ( "<<((double)T_find_2hopneis/(totalT) )*100<<"% )"<<endl;
    cout<<"\tT_cal_sim_&_sort = "<<(T_cal_sim_and_sort_for_each)<<" ( "<<((double)T_cal_sim_and_sort_for_each/(totalT) )*100<<"% )"<<endl;
    cout<<"\tT_build_segments = "<<(T_build_ranges)<<" ( "<<((double)T_build_ranges/(totalT) )*100<<"% )"<<endl;
    cout<<"\t\t### omit score lb ratio     : "<<omit_score_lb<<endl;
    cout<<"\t\t### vertex having seg       : "<<(double)make_seg_total_number/n<<endl;
    cout<<"\t\t### make indi v.s. make seg : "<<(double)make_idvidual/make_seg_total_number<<" / "<<(double)make_seg/make_seg_total_number<<endl;

    assert(INDEX_vid.size() == INDEX_list.size());
    assert(INDEX_vid.size() == INDEX_flag.size());


    string out_dir = "./index";
    std::filesystem::create_directory(out_dir);
    out_dir.append("/" + name + "_" + to_string((int)(omit_score_lb*100)) + "_" + to_string((int)(thre_make_seg)) + "_" + to_string((int)(seg_num_times*100)) + "_VSN.bin");

    FILE * f = Utility::open_file(out_dir.c_str(), "wb");

    for(ui i = 0; i < INDEX_vid.size(); i++) {
        fwrite(&INDEX_vid[i], sizeof(int), 1, f);
        int num = INDEX_list[i].size();
        assert(num > 0);
        if(INDEX_flag[i] == 1) {
            num = -num;
            fwrite(&num, sizeof(int), 1, f);
            for(auto &e : INDEX_list[i]) {
                assert(e.e_idx == e.s_idx);
                assert(e.min_score == e.max_score);
                assert(e.c == 1);
                fwrite(&e.s_idx, sizeof(ui), 1, f);
                char aaa = (char)(e.min_score*100);
                fwrite(&aaa, sizeof(char), 1, f);
            }
        }
        else {
            fwrite(&num, sizeof(int), 1, f);

            for(auto &e : INDEX_list[i]) {
                char a = (char)(e.min_score*100);
                char b = (char)(e.max_score*100);
                fwrite(&e.s_idx, sizeof(ui), 1, f);
                fwrite(&e.e_idx, sizeof(ui), 1, f);
                fwrite(&a, sizeof(char), 1, f);
                fwrite(&b, sizeof(char), 1, f);
                fwrite(&e.c, sizeof(int), 1, f);
            }
        }
    }
    fclose(f);
    delete [] c;
    cout<<"finish writing VSN index to disk."<<endl;
}

eid obtain_ver_sim_neis(vector<unordered_map<ui, char>> &ver_sim_neis)
{
    ui * vis = new ui[n];
    memset(vis, 0, sizeof(ui)*n);
    ui * comnei_cnt = new ui[n];
    memset(comnei_cnt, 0, sizeof(ui)*n);

    eid similar_edges_cnt = 0;
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
            char char_s = sim_score * 100;
            if(comnei_cnt[e] >= ComNeiThre && e>u) ver_sim_neis[u][e] = char_s;
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
    }
    delete [] vis;
    delete [] comnei_cnt;
    #ifdef _CheckInfo_
    vector<unordered_map<ui, char>> simnei_all(n);
    for(ui u = 0; u < n; ++u) {
        for(auto e : ver_sim_neis[u]) {
            char simscore = e.second;
            simnei_all[u][e.first] = simscore;
            simnei_all[e.first][u] = simscore;
        }
    }
    cout<<"similar neighbors: "<<endl;
    for(ui u = 0; u < n; ++u) {
        cout<<u<<": "; for(auto e : simnei_all[u]) cout<<e.first<<"("<<(int)e.second<<"), "; cout<<endl;
    }
    #endif
    return similar_edges_cnt;
}

void construct_bipartite_graph(vector<unordered_map<ui, char>> & ver_sim_neis, eid * b_pstart, eid * b_pend, ui * b_edges, ui * b_degree)
{

    for(ui i = 0; i < n; ++i) b_degree[i] = 0;
    for(ui i = 0; i < n; ++i) {
        for(auto e : ver_sim_neis[i]) {
            b_degree[i]++;
            b_degree[e.first]++;
        }
    }

    eid pos=0;

    for(ui u = 0; u < n; ++u) {
        b_pstart[u]=b_pend[u]=pos;
        pos += b_degree[u];
    }
    for(ui u = 0; u < n; ++u) {
        for(auto e : ver_sim_neis[u]) {
            b_edges[b_pend[u]++] = e.first;
            b_edges[b_pend[e.first]++] = u;
        }
    }
    for(ui u = 0; u < n; ++u) {

        assert(b_pend[u]>=b_pstart[u] && b_degree[u]==b_pend[u]-b_pstart[u]);
    }
#ifdef _CheckInfo_
    cout<<"The bipartite graph B: "<<endl;
    for(ui u = 0; u < n; ++u) {
        cout<<u<<" (deg="<<b_degree[u]<<"): ";
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) cout<<b_edges[i]<<", ";
        cout<<endl;
    }
#endif
}

void construct_bipartite_graph(vector<unordered_map<ui, char>> & ver_sim_neis, eid * b_pstart, eid * b_pend, ui * b_edges, ui * b_degree, ui l_n, ui r_n)
{

    ui b_n = l_n + r_n;
    for(ui i = 0; i < b_n; ++i) b_degree[i] = 0;

    for(ui u = 0; u < l_n; ++u) {
        for(auto &e : ver_sim_neis[u]) {
            ui v = e.first;
            assert(v > u && v < l_n);
            ++b_degree[u]; ++b_degree[l_n + v];
            ++b_degree[v]; ++b_degree[l_n + u];
        }
    }
    eid pos = 0;
    for(ui u = 0; u < b_n; ++u) {
        b_pstart[u] = b_pend[u] = pos;
        pos += b_degree[u];
    }
    for(ui u = 0; u < l_n; ++u) {
        for(auto &e : ver_sim_neis[u]) {
            ui v = e.first;
            assert(v > u && v < l_n);
            b_edges[b_pend[u]++] = l_n + v; b_edges[b_pend[l_n + v]++] = u;
            b_edges[b_pend[v]++] = l_n + u; b_edges[b_pend[l_n + u]++] = v;
        }
    }
    for(ui u = 0; u < b_n; ++u) assert(b_pend[u] - b_pstart[u] == b_degree[u]);

#ifdef _CheckInfo_
    cout << "The bipartite graph B:" << endl;
    for(ui u = 0; u < b_n; ++u) {
        cout << u << " (deg=" << b_degree[u] << "): ";
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) cout << b_edges[i] << ", ";
        cout << endl;
    }
#endif
}

void construct_bipartite_graph_UVdiff(vector<unordered_map<ui, double>> & ver_sim_neis, eid * b_pstart, eid * b_pend, ui * b_edges, ui * b_degree)
{
    eid pos=0;

    for(ui u = 0; u < n; ++u) {
        b_pstart[u]=pos;
        b_degree[u]=ver_sim_neis[u].size();
        pos += b_degree[u];
        b_pend[u]=pos;
    }
    for(ui u = n; u < 2*n; ++u) {
        b_pstart[u]=pos;
        b_degree[u]=ver_sim_neis[u-n].size();
        pos += b_degree[u];
        b_pend[u]=pos;
    }
    for(ui u = 0; u < n; ++u) {
        assert(b_degree[u]==(b_pend[u]-b_pstart[u]));
        eid idx = b_pstart[u];
        for(auto e : ver_sim_neis[u]) b_edges[idx++]=e.first+n;
    }
    for(ui u = n; u < 2*n; ++u) {
        assert(b_degree[u]==(b_pend[u]-b_pstart[u]));
        eid idx = b_pstart[u];
        for(auto e : ver_sim_neis[u-n]) b_edges[idx++]=e.first;
    }


}


void bnb_core(vector<unordered_set<ui>>&P_CR_hash, vector<ui>CL, vector<ui>CR, vector<ui>P, pair<vector<ui>, vector<ui>>&good_biclique, long long & cur_best_value, int tau)
{
    long long a = CL.size() + P.size();
    long long b = CR.size();
    if(a < tau || b < tau) return;
    if( (a*b-a-b) < cur_best_value ) return;
    a=CL.size();
    if( (a*b-a-b) > cur_best_value && a >= tau && b >= tau) {
        good_biclique=make_pair(CL, CR);
        cur_best_value=(a*b-a-b);
    }
    for(ui i = 0; i < P.size(); ++i ) {
        ui u = P[i];
        CL.push_back(u);
        vector<ui> newCR, newP;
        for(auto v : CR) if(P_CR_hash[u].find(v)!=P_CR_hash[u].end()) newCR.push_back(v);
        for(ui j = i+1; j < P.size(); ++j) {
            ui w = P[j];
            bool f = false;
            for(auto v : newCR) if(P_CR_hash[w].find(v)!=P_CR_hash[w].end()) {
                f=true; break;
            }
            if(f) newP.push_back(w);
        }
        bnb_core(P_CR_hash, CL, newCR, newP, good_biclique, cur_best_value, tau);
        assert(CL.back()==u);
        CL.pop_back();
    }
}


void get_good_biclique_heu(pair<vector<ui>, vector<ui>>&good_biclique, eid *b_pstart, eid *b_pend, ui *b_edges, ui *b_degree, ui *del, int tau)
{
    assert(good_biclique.first.empty() && good_biclique.second.empty());

    double cur_best_ratio = 0;
    ui * inP = new ui[n];
    memset(inP, 0, sizeof(ui)*n);
    vector<unordered_set<ui> > P_CR_hash(n);

    for(ui u = 0; u < n; ++u) if(del[u]==0) {


        vector<ui> CL = {u};
        vector<ui> P;
        vector<ui> CR;
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) if(del[b_edges[i]]==0) CR.push_back(b_edges[i]);
        for(auto v : CR) {
            for(eid i = b_pstart[v]; i < b_pend[v]; ++i) if(del[b_edges[i]]==0 && inP[b_edges[i]]==0 && b_edges[i]!=u) {
                P.push_back(b_edges[i]);
                inP[b_edges[i]]=1;
            }
        }
        for(auto v : CR) {
            for(eid i = b_pstart[v]; i < b_pend[v]; ++i) if(del[b_edges[i]]==0 && inP[b_edges[i]]==1) {
                P_CR_hash[b_edges[i]].insert(v);
            }
        }
        for(auto v : P) inP[v]=0;

        #ifdef _CheckInfo_


        #endif


        vector<ui> CL_copy = CL;
        vector<ui> CR_copy = CR;
        int round = 10;
        while (round) {

            CL=CL_copy;
            CR=CR_copy;
            std::shuffle(P.begin(), P.end(), rng);
            for(auto v : P) {

                CL.push_back(v);
                for(ui i = 0; i < CR.size(); ){
                    if(P_CR_hash[v].find(CR[i])==P_CR_hash[v].end()) {
                        CR[i]=CR.back();
                        CR.pop_back();
                    }
                    else ++i;
                }


                if(CR.size() < tau ) break;
                long long a = CL.size();
                long long b = CR.size();
                if( a >= tau && b >= tau && (double)(a*b)/(a+b)  > cur_best_ratio) {
                    good_biclique = make_pair(CL, CR);
                    cur_best_ratio = (double)(a*b)/(a+b);
                }
            }
            --round;
        }


        for(auto v : P) P_CR_hash[v].clear();
    }
    delete [] inP;
    cout<<"heu:<"<<good_biclique.first.size()<<","<<good_biclique.second.size()<<"> "<<endl;
#ifdef _CheckInfo_
    cout<<"heu: "<<endl;
    cout<<"\t\t * CL: "; for(auto e : good_biclique.first) cout<<e<<","; cout<<endl;
    cout<<"\t\t * CR: "; for(auto e : good_biclique.second) cout<<e<<","; cout<<endl;
#endif
}

long long remove_edges_in_sg(vector<ui>&sg_v, eid *b_pstart, eid *b_pend, ui *b_edges, ui *b_degree, ui *mark)
{
    long long removed_edges = 0;
    for(auto u : sg_v) mark[u] = 1;
    for(auto u : sg_v) {
        for(eid i = b_pstart[u]; i < b_pend[u]; ) {
            if(mark[b_edges[i]]==1) {

                b_edges[i]=b_edges[--b_pend[u]];
                ++ removed_edges;
            }
            else ++i;
        }
        assert(b_pend[u]>=b_pstart[u]);
        b_degree[u]=b_pend[u]-b_pstart[u];
    }
    for(auto u : sg_v) mark[u] = 0;
    return removed_edges;
}

void remove_edges_in_good_biclique(pair<vector<ui>, vector<ui>>&good_biclique, eid *b_pstart, eid *b_pend, ui *b_edges, ui *b_degree, ui *mark)
{
    eid removed_edges = 0;
    for(auto u : good_biclique.second) mark[u]=1;
    for(auto u : good_biclique.first) {

        assert(mark[u]==0);
        eid tc=0;
        for(eid i = b_pstart[u]; i < b_pend[u]; ) {
            if(mark[b_edges[i]]==1) {
                #ifdef _CheckInfo_

                #endif
                b_edges[i]=b_edges[--b_pend[u]];
                ++tc;
            }
            else ++i;
        }
        assert(tc==good_biclique.second.size());
        assert(b_pend[u]>=b_pstart[u]);
        b_degree[u]=b_pend[u]-b_pstart[u];
    }
    for(auto u : good_biclique.second) mark[u]=0;

    for(auto u : good_biclique.first) mark[u]=1;
    for(auto u : good_biclique.second) {

        assert(mark[u]==0);
        eid tc=0;
        for(eid i = b_pstart[u]; i < b_pend[u]; ) {
            if(mark[b_edges[i]]==1) {
                #ifdef _CheckInfo_

                #endif
                b_edges[i]=b_edges[--b_pend[u]];
                ++tc;
            }
            else ++i;
        }
        assert(tc==good_biclique.first.size());
        assert(b_pend[u]>=b_pstart[u]);
        b_degree[u]=b_pend[u]-b_pstart[u];
    }
    for(auto u : good_biclique.first) mark[u]=0;
}

void reorganize_remaining_graph(eid *&b_pstart, eid *&b_pend, ui *&b_edges, ui *&b_degree, ui*&del, ui* out_mapping)
{
    unordered_map<ui, ui> new_id;
    ui idx = 0;
    eid edges_number = 0;
    for(ui i = 0; i < n; ++i) if(del[i]==0) {
        new_id[i]=idx;
        out_mapping[idx]=i;
        ++idx;
        edges_number += b_degree[i];
    }
    assert(edges_number%2==0);

    eid * new_b_pstart = new eid[idx];
    eid * new_b_pend = new eid[idx];
    ui * new_b_edges = new ui[edges_number];
    ui * new_b_degree = new ui[idx];

    eid pos=0;
    for(ui u = 0; u < n; ++u) if(del[u]==0) {
        ui v = new_id[u];
        new_b_pstart[v] = pos;
        new_b_degree[v] = b_degree[u];
        pos += new_b_degree[v];
        new_b_pend[v] = pos;
    }
    assert(pos==edges_number);
    for(ui u = 0; u < n; ++u) if(del[u]==0) {
        ui v = new_id[u];
        pos = new_b_pstart[v];
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) if(del[b_edges[i]]==0) {
            new_b_edges[pos] = new_id[b_edges[i]];
            ++ pos;
        }
    }
    n=idx;
    delete [] b_pstart;
    delete [] b_pend;
    delete [] b_edges;
    delete [] b_degree;
    b_pstart = new_b_pstart;
    b_pend = new_b_pend;
    b_edges = new_b_edges;
    b_degree = new_b_degree;

    ui*new_del = new ui[n];
    delete [] del;
    del = new_del;
    memset(del, 0, sizeof(ui)*n);
#ifdef _CheckInfo_
    cout<<"mapping newid: "<<endl;
    for(ui i=0; i<n;++i) cout<<i<<" <--- "<<out_mapping[i]<<endl;
    cout<<"new bipartite graph: "<<endl;
    for(ui u = 0; u < n; ++u) {
        cout<<u<<", neighbors: ";
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) cout<<b_edges[i]<<", ";
        cout<<endl;
    }
#endif
}

void peel_residual_and_build_index(vector<unordered_map<ui, double>>& ver_sim_neis, eid *b_pstart, eid *b_pend, ui *b_edges, ui *b_degree, ui* del, vector<vector<pair<double,ui>>>&residual_sim_nei, int tau)
{
    queue<ui> Q;
    for(ui u = 0; u < n; ++u) if(b_degree[u]<tau) Q.push(u);
    vector<ui> del_vec;
    while (!Q.empty()) {
        ui u = Q.front();
        del[u]=1;
        del_vec.push_back(u);
        Q.pop();
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            assert(b_degree[b_edges[i]]>0);
            if(b_degree[b_edges[i]]--==tau)
                Q.push(b_edges[i]);
        }
    }
#ifdef _CheckInfo_


#endif

    for(ui u = 0; u < n; ++u) if(del[u]==1) {
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];

            assert(ver_sim_neis[u].find(v)!=ver_sim_neis[u].end() && ver_sim_neis[v].find(u)!=ver_sim_neis[v].end());
            double s = ver_sim_neis[u][v];

            residual_sim_nei[u].push_back(make_pair(s, v));

            residual_sim_nei[v].push_back(make_pair(s, u));

            bool f=false;
            for(eid j = b_pstart[v]; j < b_pend[v]; ++j) if(b_edges[j]==u) {
                b_edges[j] = b_edges[--b_pend[v]];
                f=true;
                break;
            }
            if(!f) {cout<<"did not find u in v's adj-array, something wrong!"<<endl;exit(1);}
        }

        b_pend[u] = b_pstart[u];
        b_degree[u] = 0;
    }

    for(ui u = 0; u < n; ++u) if(del[u]==0) {
        assert(b_pend[u] > b_pstart[u] && (b_pend[u] - b_pstart[u])>= tau);
        b_degree[u] = b_pend[u] - b_pstart[u];
    }
#ifdef _CheckInfo_


#endif
}

void build_index(vector<ui>&L, vector<ui>&R, vector<vector<ui>>&z_list, vector<unordered_map<ui, char>>&ver_sim_neis, vector<vector<pair<char,ui>>>&z_R, ui&z_idx)
{
    for(auto u : L) z_list[u].push_back(z_idx);
    vector<pair<char,ui>> tmp_z_R;
    for(auto u : R) {
        char maxscore = 0;
        for(auto v : L) {
            if(u==v) continue;
            if(u<v) {
                if(ver_sim_neis[u].find(v)==ver_sim_neis[u].end()) continue;
                char t_score = ver_sim_neis[u][v];
                if(t_score > maxscore) maxscore = t_score;
            }
            else {
                if(ver_sim_neis[v].find(u)==ver_sim_neis[v].end()) continue;
                char t_score = ver_sim_neis[v][u];
                if(t_score > maxscore) maxscore = t_score;
            }
        }

        tmp_z_R.push_back(make_pair(maxscore,u));
    }
    sort(tmp_z_R.begin(), tmp_z_R.end(), [](const pair<char, ui>& a, const pair<char, ui>& b) {
        return a.first > b.first;
    });

    z_R.push_back(tmp_z_R);
    assert(z_R.size()==(z_idx+1));
    ++z_idx;
}

void bnb_enum_core(vector<ui>QL, vector<ui>CL, vector<ui>P, vector<ui>CR, char**Matrix, ui*Ptrans, ui*CRtrans, int tau, ui * out_mapping, ui * pivot_nei_mark)
{
    ++ search_space;

    bool maximality = true;
    for(auto u : QL) {
        int tmpd = 0;
        for(auto v : CR) {
            if(Matrix[Ptrans[u]][CRtrans[v]]==1) ++ tmpd;
        }
        if(tmpd == (int)CR.size()) {
            maximality = false;
            break;
        }
    }
    if(maximality == false) return;

    vector<ui> CL_exp;
    vector<ui> tmpP;
    for(ui i = 0; i < P.size(); ++i) {
        ui u = P[i];
        int td = 0;
        for(auto v : CR) if(Matrix[Ptrans[u]][CRtrans[v]]==1) ++ td;
        if (td == (int)CR.size()) CL_exp.push_back(u);
        else tmpP.push_back(u);
    }

    for(auto e : CL_exp) CL.push_back(e);
    P=tmpP;

    if(CL.size() >= CR.size()) return;

    if((int)CL.size()>=tau && (int)CR.size()>=tau) {
        vector<ui> L, R;


        for(auto e : CL) L.push_back(e);
        for(auto e : CR) R.push_back(e);


        mbc_res.push_back(make_pair(L, R));


    }

    if(P.empty()) return;
    if((int)CL.size()+(int)P.size()<tau || (int)CR.size()<tau) return;

    vector<ui> be_dominated_set;
#ifdef _Pivot_
    int tdeg = -1;
    ui pivot = 0;
    for(auto u : QL) {
        int d = 0;
        for(auto v : CR) if(Matrix[Ptrans[u]][CRtrans[v]]==1) ++d;
        if(d>=tdeg) {
            pivot = u; tdeg = d;
        }
    }
    for(auto u : P) {
        int d = 0;
        for(auto v : CR) if(Matrix[Ptrans[u]][CRtrans[v]]==1) ++d;
        if(d>=tdeg) {
            pivot = u; tdeg = d;
        }
    }
    vector<ui> pivot_neighbors;
    for(auto u : CR) if(Matrix[Ptrans[pivot]][CRtrans[u]]==1) {
        pivot_neighbors.push_back(u);
        pivot_nei_mark[u] = 1;
    }
    assert(tdeg!=-1);
    if(tdeg==-1) {cout<<"tdeg==-1"<<endl; exit(1);}

    for(auto u : P) {
        if(u==pivot) continue;
        bool isdom = true;
        for(auto v : CR) if(Matrix[Ptrans[u]][CRtrans[v]]==1 && pivot_nei_mark[v]==0){
            isdom = false; break;
        }
        if(isdom == true) be_dominated_set.push_back(u);
    }
    for(auto u : pivot_neighbors) pivot_nei_mark[u] = 0;

    assert(P.size() >= be_dominated_set.size());
    for(auto u : be_dominated_set) pivot_nei_mark[u] = 1;

    vector<ui> P_copy = P;
    ui idx1 = 0;
    ui idx2 = (P.size() - be_dominated_set.size());
    for(auto u : P_copy) {
        if(pivot_nei_mark[u] == 1) P[idx2++] = u;
        else P[idx1++] = u;
    }
    assert(idx2 == P_copy.size());
    for(auto u : be_dominated_set) pivot_nei_mark[u] = 0;
#endif

    assert(P.size() >= be_dominated_set.size());

    for(ui i = 0; i < P.size() - be_dominated_set.size(); ++i) {
        ui u = P[i];
        CL.push_back(u);
        vector<ui> newQL, newP, newCR;
        for(auto v : CR) if(Matrix[Ptrans[u]][CRtrans[v]]==1) newCR.push_back(v);
        for(ui j = i+1; j < P.size(); ++j) {
            ui w = P[j];
            bool f = false;
            for(auto v : newCR) {
                if(Matrix[Ptrans[w]][CRtrans[v]]==1) {
                    f = true; break;
                }
            }
            if(f==true) newP.push_back(w);
        }
        for(auto w : QL) {
            bool f = false;
            for(auto v : newCR) {
                if(Matrix[Ptrans[w]][CRtrans[v]]==1) {
                    f = true; break;
                }
            }
            if(f==true) newQL.push_back(w);
        }
        bnb_enum_core(newQL, CL, newP, newCR, Matrix, Ptrans, CRtrans, tau, out_mapping, pivot_nei_mark);
        assert(CL.back()==u);
        CL.pop_back();
        QL.push_back(u);
    }


}

void get_good_biclique_bnb_enum(eid *b_pstart, eid *b_pend, ui *b_edges, ui *b_degree, int tau, ui * out_mapping)
{
    Timer t;

    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    ui *peel_sequence = new ui[n];
    ui maxcore=0;
    for(ui i = 0; i < n; ++i) peel_sequence[i]=i;
    heap->init(n, n-1, peel_sequence, b_degree);
    for(ui i = 0;i < n; i ++) {
        ui u, key;
        heap->pop_min(u, key);
        if(key > maxcore) maxcore=key;
        peel_sequence[i] = u;
        b_degree[u]=0;
        for(eid j = b_pstart[u]; j < b_pend[u]; j ++) {
            if(b_degree[b_edges[j]] > 0) {
                heap->decrement(b_edges[j], 1);
            }
        }
    }
    ui * rid = new ui[n];
    for(ui i = 0; i < n; ++i) rid[peel_sequence[i]] = i;
    cout<<"maxcore: "<<maxcore<<endl;


    ui * vis = new ui[n];
    memset(vis, 0, sizeof(ui)*n);
    ui Matrix_CR_idx = 0;
    ui Matrix_P_idx = 0;
    for(ui u = 0; u < n; ++u) {
        vector<ui> tmpP;
        vector<ui> tmpCR;
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];
            tmpCR.push_back(v);
            for(eid j = b_pstart[v]; j < b_pend[v]; ++j) {
                ui w = b_edges[j];
                if(w!=u && vis[w]==0) {
                    tmpP.push_back(w);
                    vis[w]=1;
                }
            }
        }
        if(tmpP.size()>Matrix_P_idx) Matrix_P_idx=(ui)tmpP.size();
        if(tmpCR.size()>Matrix_CR_idx) Matrix_CR_idx=(ui)tmpCR.size();
        for(auto e : tmpP) vis[e] = 0;
    }
    cout<<"Matrix_CR_idx: "<<Matrix_CR_idx<<", Matrix_P_idx: "<<Matrix_P_idx<<endl;

    char** Matrix;
    Matrix = new char*[Matrix_P_idx];
    for(ui i = 0; i < Matrix_P_idx; i++) Matrix[i] = new char[Matrix_CR_idx];
    ui * Ptrans = new ui[n];
    ui * CRtrans = new ui[n];
    ui * pivot_nei_mark = new ui[n];
    memset(pivot_nei_mark, 0, sizeof(ui)*n);
    ui gap = 10;

    for (ui i = 0; i < n; ++i) {
        if(i%gap==0) cout<<"@"<<i<<"(res="<<mbc_res.size()<<"), ";
        ui u = peel_sequence[i];
        vector<ui> CL = {u};
        vector<ui> CR;
        for(eid j = b_pstart[u]; j < b_pend[u]; ++j) {
            ui v = b_edges[j];
            CR.push_back(v);
        }
        vector<ui> QL, P;
        for(auto v : CR) {
            for(eid j = b_pstart[v]; j < b_pend[v]; ++j) {
                ui w = b_edges[j];
                if(rid[w] > rid[u] && vis[w] == 0) {
                    P.push_back(w); vis[w] = 1;
                }
                else if (rid[w] < rid[u] && vis[w] == 0) {
                    QL.push_back(w); vis[w] = 1;
                }
            }
        }


        if(P.size()+1<tau || CR.size()<tau) {
            for(auto e : P) vis[e] = 0;
            for(auto e : QL) vis[e] = 0;
            continue;
        }

        ui idxa = 0;
        for(auto e : P) Ptrans[e]=idxa++;
        for(auto e : QL) Ptrans[e]=idxa++;
        assert(idxa<=Matrix_P_idx);
        ui idxb=0;
        for(auto e : CR) CRtrans[e]=idxb++;
        assert(idxb<=Matrix_CR_idx);
        for(ui j = 0; j < idxa; ++j) for(ui k = 0; k < idxb; ++k) Matrix[j][k] = 0;


        for(auto v : CR) {
            for(eid j = b_pstart[v]; j < b_pend[v]; ++j) {
                ui w = b_edges[j];
                if(vis[w]==1) Matrix[Ptrans[w]][CRtrans[v]] = 1;
            }
        }
        for(auto e : P) vis[e] = 0;
        for(auto e : QL) vis[e] = 0;

        bnb_enum_core(QL, CL, P, CR, Matrix, Ptrans, CRtrans, tau, out_mapping, pivot_nei_mark);

    }
    cout<<endl;
    int maxsize = -1;
    int maxsize_a, maxsize_b;
    double best_ratio = 0;
    int best_ratio_a, best_ratio_b;
    for(auto e : mbc_res) {
        long long a = (long long) e.first.size();
        long long b = (long long) e.second.size();
        if(a+b > maxsize) {
            maxsize=a+b;
            maxsize_a=a;
            maxsize_b=b;
        }
        if((double)a*b/(a+b) > best_ratio) {
            best_ratio_a=a;
            best_ratio_b=b;
            best_ratio = (double)a*b/(a+b);
        }
    }
    cout<<"number of mbc: "<<mbc_res.size()<<endl;
    cout<<"maxsize: "<<maxsize<<" ("<<maxsize_a<<" | "<<maxsize_b<<")"<<endl;
    cout<<"best_ratio: "<<best_ratio<<" ("<<best_ratio_a<<" | "<<best_ratio_b<<")"<<endl;
    cout<<"search space: "<<search_space<<endl;
    cout<<"time cost: "<<t.elapsed()/CLOCKS_PER_SEC<<" s"<<endl;

    long long bc_cnt = 0;


    exit(1);

}

void peel_get_dense_subgraph(ListLinearHeap *heap, ui*peel_sequence, eid *b_pstart, eid *b_pend, ui *b_edges, ui *b_degree, int tau, ui * out_mapping)
{


}

int compute_its_maxcore(eid * b_pstart, eid * b_pend, ui * b_edges, ui * b_degree)
{
    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    ui *peel_sequence = new ui[n];
    ui *processed = new ui[n];
    memset(processed, 0, sizeof(ui)*n);
    int maxcore=0;

    for(ui i = 0; i < n; ++i) peel_sequence[i]=i;
    heap->init(n, n-1, peel_sequence, b_degree);
    for(ui i = 0;i < n; i ++) {
        ui u, key;
        heap->pop_min(u, key);
        if(key > maxcore) maxcore=key;
        peel_sequence[i] = u;
        processed[u]=1;
        for(eid j = b_pstart[u]; j < b_pend[u]; j ++) if(processed[b_edges[j]]==0) {
            heap->decrement(b_edges[j], 1);
        }
    }
    delete [] peel_sequence;
    delete [] processed;
    delete heap;

    return maxcore;
}


pair<vector<ui>,int> dense_sg_by_peeling_den3(eid * b_pstart, eid * b_pend, ui * b_edges, ui * b_degree, double alpha, int sg_size_lb)
{
    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    ui *peel_sequence = new ui[n];
    ui *processed = new ui[n];
    memset(processed, 0, sizeof(ui)*n);
    int maxcore=0;
    long long remain_e = 0;
    for(ui i = 0; i < n; ++i) remain_e += b_degree[i];

    double best_den = -1;
    ui best_idx = 0;
    for(ui i = 0; i < n; ++i) peel_sequence[i]=i;
    heap->init(n, n-1, peel_sequence, b_degree);
    for(ui i = 0;i < n; i ++) {
        int remain_n = 2*(n-i);
        assert(remain_n%2==0);
        remain_n /= 2;
        double den = (double)remain_e - (double)alpha*remain_n*remain_n/2;
        if(den > best_den && remain_n >= sg_size_lb) {
            best_idx = i;
            best_den = den;
        }
        ui u, key;
        heap->pop_min(u, key);
        if(key > maxcore) maxcore=key;
        peel_sequence[i] = u;
        processed[u]=1;
        long long desc_e = 0;
        for(eid j = b_pstart[u]; j < b_pend[u]; j ++) if(processed[b_edges[j]]==0) {
            heap->decrement(b_edges[j], 1);
            ++ desc_e;
        }
        desc_e = desc_e * 2;
        assert(remain_e >= desc_e);
        remain_e -= desc_e;
    }

    vector<ui> sg_v;
    if(best_den == -1) {
        cout<<"best_den = -1, did not find sg!!!"<<endl;
        return make_pair(sg_v, -1);
    }
    for(ui i = best_idx; i < n; ++i) sg_v.push_back(peel_sequence[i]);
    double density = (double)(best_den+alpha*sg_v.size()*sg_v.size())/(sg_v.size()*sg_v.size());
    int int_density = density*100;
    PeelSG_core_sum += maxcore;
    PeelSG_den_sum += density;
    PeelSG_size_sum += sg_v.size();

    delete [] peel_sequence;
    delete [] processed;
    delete heap;

    return make_pair(sg_v,maxcore);
}

vector<ui> peel_sg(eid * sg_pstart, eid * sg_pend, ui * sg_edges, ui * sg_degree, ListLinearHeap *sg_heap, vector<ui>sgv, double alpha, int Z_size_lb)
{
    ui sgn = sgv.size();
    assert(sgn>0);

    ui *processed = new ui[n];
    memset(processed, 0, sizeof(ui)*n);
    ui *peel_sequence = new ui[sgn];

    int maxcore=0;
    long long remain_e = 0;

    for(ui i = 0; i < sgn; ++i) remain_e += sg_degree[sgv[i]];


    ui best_idx = sgn;
    bool f = false;
    for(ui i = 0; i < sgn; ++i) peel_sequence[i]=sgv[i];
    sg_heap->init(sgn, sgn-1, peel_sequence, sg_degree);
    for(ui i = 0;i < sgn; i ++) {
        if(f) {
            ui u, key;
            sg_heap->pop_min(u, key);
            peel_sequence[i] = u;
            continue;
        }
        long long remain_n = sgn-i;
        double den = (double)remain_e/(remain_n*remain_n);
        if(den >= alpha && remain_e > 0 && remain_n >= Z_size_lb) {
            best_idx = i;
            f = true;
        }
        ui u, key;
        sg_heap->pop_min(u, key);

        if(key > maxcore) maxcore=key;
        peel_sequence[i] = u;
        processed[u]=1;
        long long desc_e = 0;
        for(eid j = sg_pstart[u]; j < sg_pend[u]; j ++) if(processed[sg_edges[j]]==0) {
            sg_heap->decrement(sg_edges[j], 1);
            ++ desc_e;
        }
        desc_e = desc_e * 2;
        assert(remain_e >= desc_e);
        remain_e -= desc_e;
    }


    vector<ui> finalsg;
    for(ui i = best_idx; i < sgn; ++i) finalsg.push_back(peel_sequence[i]);

    delete [] processed;
    delete [] peel_sequence;
    return finalsg;
}


pair<vector<ui>,int> dense_sg_by_peeling_den4(eid * b_pstart, eid * b_pend, ui * b_edges, ui * b_degree, double alpha, int sg_size_lb)
{
    ui maxdeg = 0;
    for(ui i = 0; i < n; ++i) if(b_degree[i] > maxdeg) maxdeg = b_degree[i];


    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    ui *peel_sequence = new ui[n];
    ui *processed = new ui[n];
    memset(processed, 0, sizeof(ui)*n);
    int maxcore=0;
    long long remain_e = 0;
    for(ui i = 0; i < n; ++i) remain_e += b_degree[i];

    double best_den = -1;
    ui best_idx = 0;
    for(ui i = 0; i < n; ++i) peel_sequence[i]=i;
    heap->init(n, n-1, peel_sequence, b_degree);
    for(ui i = 0;i < n; i ++) {
        int remain_n = 2*(n-i);
        assert(remain_n%2==0);
        remain_n /= 2;
        double den = (double)remain_e - (double)alpha*remain_n*remain_n/2;
        if(den > best_den && remain_n >= sg_size_lb) {
            best_idx = i;
            best_den = den;
        }
        ui u, key;
        heap->pop_min(u, key);
        if(key > maxcore) maxcore=key;
        peel_sequence[i] = u;
        processed[u]=1;
        long long desc_e = 0;
        for(eid j = b_pstart[u]; j < b_pend[u]; j ++) if(processed[b_edges[j]]==0) {
            heap->decrement(b_edges[j], 1);
            ++ desc_e;
        }
        desc_e = desc_e * 2;
        assert(remain_e >= desc_e);
        remain_e -= desc_e;
    }

    vector<ui> sg_v;
    if(best_den == -1) {
        cout<<"best_den = -1, did not find sg!!!"<<endl;
        return make_pair(sg_v, -1);
    }
    for(ui i = best_idx; i < n; ++i) sg_v.push_back(peel_sequence[i]);
    double density = (double)(best_den+alpha*sg_v.size()*sg_v.size())/(sg_v.size()*sg_v.size());
    int int_density = density*100;
    PeelSG_core_sum += maxcore;
    PeelSG_den_sum += density;
    PeelSG_size_sum += sg_v.size();

    delete [] peel_sequence;
    delete [] processed;
    delete heap;

    return make_pair(sg_v,maxcore);
}

struct RemovalResult {
    vector<ui> centers;
    vector<vector<ui>> removed_sets;
};


vector<vector<ui>> obtain_multi_sg(eid * b_pstart, eid * b_pend, ui * b_edges, ui * b_degree)
{

    assert(n >= 1);
    ui parT;
    if (n <= 10000)            parT = 2;
    else if (n <= 50000)       parT = 2;
    else if (n <= 100000)      parT = 4;
    else if (n <= 500000)      parT = 8;
    else if (n <= 1000000)     parT = 16;
    else if (n <= 5000000)     parT = 32;
    else                       parT = 64;

    cout<<"parT="<<parT<<endl;

    vector<vector<ui>> partition_list;

    std::vector<ui> vertices(n);
    std::iota(vertices.begin(), vertices.end(), 0);

    static std::mt19937 rng(std::random_device{}());
    std::shuffle(vertices.begin(), vertices.end(), rng);

    ui cnt = n/parT;
    assert(cnt>=1);
    ui startid, endid;
    vector<ui> tmpvec;
    for(ui i = 1; i <= parT; ++i) {
        tmpvec.clear();
        startid = (i-1)*cnt;
        endid = i * cnt;
        for(ui j = startid; j < endid; ++j) tmpvec.push_back(vertices[j]);
        partition_list.push_back(tmpvec);
    }

    startid = cnt * parT;
    assert(startid <= n);

    if(startid < n) {
        tmpvec.clear();
        for(ui i = startid; i < n; ++i) tmpvec.push_back(vertices[i]);
        partition_list.push_back(tmpvec);
    }

    ui checkn = 0;
    for(auto e : partition_list) checkn += e.size();
    assert(checkn == n);

#ifdef _CheckInfo_
    cout<<"partitioned list: "<<endl;
    int lst = 1;
    for(auto e : partition_list) {
        cout<<"List"<<lst++<<": "; for(auto x : e) cout<<x<<","; cout<<endl;
    }
#endif

    return partition_list;
}


pair<vector<ui>,double> dense_sg_by_peeling_den2(eid * b_pstart, eid * b_pend, ui * b_edges, ui * b_degree)
{
    int size_constraint = 20;
    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    ui *peel_sequence = new ui[n];
    ui *processed = new ui[n];
    memset(processed, 0, sizeof(ui)*n);
    ui maxcore=0;
    long long remain_e = 0;
    for(ui i = 0; i < n; ++i) remain_e += b_degree[i];

    cout<<"\tremain_e: "<<remain_e<<", original den: "<<(double)remain_e/(n*n)<<endl;

    double best_den = -1;
    ui best_idx = 0;
    for(ui i = 0; i < n; ++i) peel_sequence[i]=i;
    heap->init(n, n-1, peel_sequence, b_degree);
    for(ui i = 0;i < n; i ++) {
        int remain_n = 2*(n-i);
        assert(remain_n%2==0);
        remain_n /= 2;
        double den = (double)remain_e/(remain_n*remain_n);


        if(den > best_den && remain_n > size_constraint) {


            best_idx = i;
            best_den = den;


        }
        ui u, key;
        heap->pop_min(u, key);
        if(key > maxcore) maxcore=key;

        peel_sequence[i] = u;
        processed[u]=1;
        long long desc_e = 0;
        for(eid j = b_pstart[u]; j < b_pend[u]; j ++) if(processed[b_edges[j]]==0) {
            heap->decrement(b_edges[j], 1);

            ++ desc_e;
        }
        desc_e = desc_e * 2;
        assert(remain_e >= desc_e);
        remain_e -= desc_e;

    }

    cout<<"\tmaxcore: "<<maxcore<<endl;
    cout<<"\tbest_den: "<<best_den<<endl;


    vector<ui> sg_v;
    for(ui i = best_idx; i < n; ++i) sg_v.push_back(peel_sequence[i]);
    cout<<"\tsg_v size: "<<sg_v.size()<<endl;
    cout<<"\t\t(counterpart den: "<<(double)(best_den*sg_v.size())/2<<")"<<endl;


    delete [] peel_sequence;
    delete heap;

    return make_pair(sg_v,best_den);
}


pair<vector<ui>,double> dense_sg_by_peeling_den1(eid * b_pstart, eid * b_pend, ui * b_edges, ui * b_degree)
{
    ListLinearHeap *heap = new ListLinearHeap(n, n-1);
    ui *peel_sequence = new ui[n];
    ui *processed = new ui[n];
    memset(processed, 0, sizeof(ui)*n);
    ui maxcore=0;
    long long remain_e = 0;
    for(ui i = 0; i < n; ++i) remain_e += b_degree[i];

    cout<<"\tremain_e: "<<remain_e<<", original den: "<<(double)remain_e/(2*n)<<endl;

    double best_den = -1;
    ui best_idx = 0;
    for(ui i = 0; i < n; ++i) peel_sequence[i]=i;
    heap->init(n, n-1, peel_sequence, b_degree);
    for(ui i = 0;i < n; i ++) {
        int remain_n = 2*(n-i);
        double den = (double)remain_e/remain_n;


        if(den > best_den ) {


            best_idx = i;
            best_den = den;


        }
        ui u, key;
        heap->pop_min(u, key);
        if(key > maxcore) maxcore=key;

        peel_sequence[i] = u;
        processed[u]=1;
        long long desc_e = 0;
        for(eid j = b_pstart[u]; j < b_pend[u]; j ++) if(processed[b_edges[j]]==0) {
            heap->decrement(b_edges[j], 1);

            ++ desc_e;
        }
        desc_e = desc_e * 2;
        assert(remain_e >= desc_e);
        remain_e -= desc_e;

    }

    cout<<"\tmaxcore: "<<maxcore<<endl;
    cout<<"\tbest_den: "<<best_den<<endl;


    vector<ui> sg_v;
    for(ui i = best_idx; i < n; ++i) sg_v.push_back(peel_sequence[i]);
    cout<<"\tsg_v size: "<<sg_v.size()<<endl;
    cout<<"\t\t(counterpart den: "<<(double)(best_den*2)/sg_v.size()<<")"<<endl;


    delete [] peel_sequence;
    delete heap;

    return make_pair(sg_v,best_den);
}

void peel_residual_and_build_index(vector<unordered_map<ui, double>>& ver_sim_neis, eid *b_pstart, eid *b_pend, ui *b_edges, ui *b_degree, vector<vector<pair<double,ui>>>&residual_sim_nei)
{
    for(ui u = 0; u < n; ++u) if(b_degree[u]>0) {
        vector<pair<double,ui>> tmpvec;
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];
            assert(ver_sim_neis[u].find(v)!=ver_sim_neis[u].end());
            double s = ver_sim_neis[u][v];

            tmpvec.push_back(make_pair(s, v));
        }
        sort(tmpvec.begin(), tmpvec.end(), [](const pair<double, ui>& a, const pair<double, ui>& b) {
            return a.first > b.first;
        });
        residual_sim_nei[u] = tmpvec;
    }
}

void peel_residual_and_build_index_final(vector<unordered_map<ui, char>>& ver_sim_neis, eid *b_pstart, eid *b_pend, ui *b_edges, ui *b_degree, vector<vector<pair<char,ui>>>&residual_sim_nei, ui*out_mapping)
{

    for(ui u = 0; u < n; ++u) if(b_degree[u]>0) {
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];
            char s;
            if(out_mapping[u] < out_mapping[v]) s = ver_sim_neis[out_mapping[u]][out_mapping[v]];
            else s = ver_sim_neis[out_mapping[v]][out_mapping[u]];
            residual_sim_nei[out_mapping[u]].push_back(make_pair(s, out_mapping[v]));
        }
    }
}

long long peel_reorg(vector<unordered_map<ui, char>>& ver_sim_neis, eid *&b_pstart, eid *&b_pend, ui *&b_edges, ui *&b_degree, vector<vector<pair<char,ui>>>&residual_sim_nei, int tau, ui*out_mapping, long long &reamin_edges_number)
{

    ui * del = new ui[n];
    memset(del, 0, sizeof(ui)*n);
    queue<ui> Q;
    for(ui u = 0; u < n; ++u) if(b_degree[u]<tau) Q.push(u);
    while (!Q.empty()) {
        ui u = Q.front();
        del[u]=1;
        Q.pop();
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            assert(b_degree[b_edges[i]]>0);
            if(b_degree[b_edges[i]]--==tau)
                Q.push(b_edges[i]);
        }
    }


    for(ui u = 0; u < n; ++u) if(del[u]==1) {
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];

            char s;
            if(out_mapping[u] < out_mapping[v]) s = ver_sim_neis[out_mapping[u]][out_mapping[v]];
            else s = ver_sim_neis[out_mapping[v]][out_mapping[u]];


            residual_sim_nei[out_mapping[u]].push_back(make_pair(s, out_mapping[v]));

            residual_sim_nei[out_mapping[v]].push_back(make_pair(s, out_mapping[u]));

            bool f=false;
            for(eid j = b_pstart[v]; j < b_pend[v]; ++j) if(b_edges[j]==u) {
                b_edges[j] = b_edges[--b_pend[v]];
                f=true;
                break;
            }
            if(!f) {cout<<"did not find u in v's adj-array, something wrong!"<<endl;exit(1);}
        }

        b_pend[u] = b_pstart[u];
        b_degree[u] = 0;
    }
    for(ui u = 0; u < n; ++u) if(del[u]==0) {
        b_degree[u] = b_pend[u] - b_pstart[u];
        assert(b_degree[u]>=tau);
    }


    unordered_map<ui, ui> new_id;
    ui idx = 0;
    eid edges_number = 0;
    for(ui i = 0; i < n; ++i) if(del[i]==0) {
        new_id[i]=idx;
        out_mapping[idx]=out_mapping[i];
        ++idx;
        edges_number += b_degree[i];

    }
    assert(edges_number%2==0);

    eid * new_b_pstart = new eid[idx];
    eid * new_b_pend = new eid[idx];
    ui * new_b_edges = new ui[edges_number];
    ui * new_b_degree = new ui[idx];

    eid pos=0;
    for(ui u = 0; u < n; ++u) if(del[u]==0) {
        ui v = new_id[u];
        new_b_pstart[v] = pos;
        new_b_degree[v] = b_degree[u];
        pos += new_b_degree[v];
        new_b_pend[v] = pos;
    }
    assert(pos==edges_number);
    for(ui u = 0; u < n; ++u) if(del[u]==0) {
        ui v = new_id[u];
        pos = new_b_pstart[v];
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) if(del[b_edges[i]]==0) {
            new_b_edges[pos] = new_id[b_edges[i]];
            ++ pos;
        }
    }

    n=idx;
    assert(reamin_edges_number >= edges_number);
    long long del_edgecnt_by_residual = (reamin_edges_number - edges_number);
    reamin_edges_number = edges_number;

    delete [] b_pstart;
    delete [] b_pend;
    delete [] b_edges;
    delete [] b_degree;
    b_pstart = new_b_pstart;
    b_pend = new_b_pend;
    b_edges = new_b_edges;
    b_degree = new_b_degree;

    delete [] del;


#ifdef _CheckInfo_
    cout<<"The bipartite graph B: "<<endl;
    for(ui u = 0; u < n; ++u) {
        cout<<u<<"(deg="<<b_degree[u]<<"): ";
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) cout<<b_edges[i]<<", ";
        cout<<endl;
    }
    cout<<"outmapping: "<<endl;
    for(ui u = 0; u < n; ++u) cout<<"\t"<<out_mapping[u]<<" -> "<<u<<endl;

#endif

    return del_edgecnt_by_residual;
}

vector<vector<ui>> minhash_cluster(ui n, eid* b_pstart, eid* b_pend, ui* b_edges, ui k, ui prefix_len, ui min_cluster_size)
{
    const unsigned long long PRIME = 1000000007ULL;
    const unsigned long long INF = ULLONG_MAX;
    cout<<"INF="<<INF<<endl;

    vector<unsigned long long> a(k);
    vector<unsigned long long> b(k);
    mt19937_64 rng(123456);
    for (ui i = 0; i < k; ++i) {
        a[i] = rng() % (PRIME - 1) + 1;
        b[i] = rng() % PRIME;
    }


    vector<vector<unsigned long long>> signature(n, vector<unsigned long long>(k, INF));

    for (ui v = 0; v < n; ++v) {

        for (eid p = b_pstart[v]; p < b_pend[v]; ++p) {
            ui u = b_edges[p];

            for (ui i = 0; i < k; ++i) {
                unsigned long long hash_value = (a[i] * u + b[i]) % PRIME;
                signature[v][i] = min(signature[v][i], hash_value);
            }
        }
    }


    map<vector<unsigned long long>, vector<ui>> groups;

    for (ui v = 0; v < n; ++v) {
        if (signature[v][0] == INF) continue;
        vector<unsigned long long> key;
        for (ui i = 0; i < prefix_len; ++i) key.push_back(signature[v][i]);

        groups[key].push_back(v);
    }


    vector<vector<ui>> clusters;
    for (auto& item : groups) {
        vector<ui>& cluster = item.second;
        if (cluster.size() >= min_cluster_size) clusters.push_back(cluster);
    }


    sort(clusters.begin(),clusters.end(),[](const vector<ui>& x, const vector<ui>& y) {return x.size() > y.size();} );

    return clusters;
}

double js(ui u, ui v, eid* b_pstart, eid* b_pend, ui* b_edges)
{
    vector<ui> unei;
    for(eid i = b_pstart[u]; i < b_pend[u]; ++i) unei.push_back(b_edges[i]);
    vector<ui> vnei;
    for(eid i = b_pstart[v]; i < b_pend[v]; ++i) vnei.push_back(b_edges[i]);
    sort(unei.begin(),unei.end());
    sort(vnei.begin(),vnei.end());

    ui intersection_size = 0;
    ui i = 0;
    ui j = 0;

    while(i < unei.size() && j < vnei.size()) {
        if(unei[i] == vnei[j]) {
            intersection_size++;
            i++; j++;
        }
        else if(unei[i] < vnei[j]) i++;
        else j++;
    }
    ui union_size = static_cast<ui>(unei.size() + vnei.size()) - intersection_size;
    double similarity = 0.0;
    if(union_size > 0) {
        similarity = static_cast<double>(intersection_size) / static_cast<double>(union_size);
    }
    return similarity;
}

double average_jaccard_in_cluster( const vector<ui>& cluster, eid* b_pstart, eid* b_pend, ui* b_edges)
{
    unsigned long long cluster_size = cluster.size();
    if (cluster_size < 2) return 0.0;
    unsigned long long total_pairs = cluster_size * (cluster_size - 1) / 2;
    double sum = 0.0;
    unsigned long long checked_pairs = 0;
    for (ui i = 0; i < cluster.size(); ++i) {
        for (ui j = i + 1; j < cluster.size(); ++j) {
            sum += js( cluster[i], cluster[j], b_pstart, b_pend, b_edges );
            checked_pairs++;
        }
    }
    return sum / checked_pairs;
}


ull hash64(ull x)
{
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;

    return x ^ (x >> 31);
}


vector<vector<ull>> compute_minhash(ui n, eid* b_pstart, eid* b_pend, ui* b_edges, ui k)
{
    vector<vector<ull>> signature(n, vector<ull>(k, ULLONG_MAX));


    mt19937_64 random_generator(123456);
    vector<ull> seeds(k);
    for (ui i = 0; i < k; ++i) seeds[i] = random_generator();

    for (ui v = 0; v < n; ++v) {

        for (eid p = b_pstart[v]; p < b_pend[v]; ++p) {
            ui neighbor = b_edges[p];

            for (ui i = 0; i < k; ++i) {
                ull hash_value = hash64( static_cast<ull>(neighbor) ^ seeds[i] );
                if (hash_value < signature[v][i]) signature[v][i] = hash_value;
            }
        }
    }
    return signature;
}


ull get_band_key(const vector<ull>& signature, ui band_id, ui rows_per_band)
{
    ui start = band_id * rows_per_band;
    ui end = start + rows_per_band;
    ull key = 0;
    for (ui i = start; i < end; ++i) {
        key = hash64(key ^ signature[i]);
    }
    return key;
}


double estimate_jaccard(const vector<ull>& signature1, const vector<ull>& signature2)
{
    ui k = signature1.size();
    ui same_count = 0;
    for (ui i = 0; i < k; ++i) {
        if (signature1[i] == signature2[i]) {
            same_count++;
        }
    }
    return static_cast<double>(same_count) / k;
}


vector<vector<ui>> minhash_lsh_cluster(ui n, eid* b_pstart, eid* b_pend, ui* b_edges, ui k, ui band_count, double similarity_threshold, ui min_cluster_size)
{
    if (k == 0 || band_count == 0 || k % band_count != 0) {
        cout << "Error: k must be divisible by band_count." << endl;
        return {};
    }
    ui rows_per_band = k / band_count;

    vector<vector<ull>> signature = compute_minhash(n, b_pstart, b_pend, b_edges, k);


    vector<unordered_map<ull, vector<ui>>> band_table(band_count);

    for (ui v = 0; v < n; ++v) {
        if (signature[v][0] == ULLONG_MAX) continue;
        for (ui band = 0; band < band_count; ++band) {
            ull key = get_band_key( signature[v], band, rows_per_band );
            band_table[band][key].push_back(v);
        }
    }


    vector<bool> assigned(n, false);
    vector<vector<ui>> clusters;


    for (ui center = 0; center < n; ++center) {
        if (assigned[center]) continue;
        if (signature[center][0] == ULLONG_MAX) continue;


        set<ui> candidates;
        for (ui band = 0; band < band_count; ++band) {
            ull key = get_band_key(signature[center], band, rows_per_band );
            auto it = band_table[band].find(key);
            if (it == band_table[band].end()) continue;
            for (ui v : it->second) candidates.insert(v);
        }


        vector<ui> cluster;
        cluster.push_back(center);
        for (ui v : candidates) {
            if (v == center) continue;
            if (assigned[v]) continue;

            double estimated_similarity = estimate_jaccard(signature[center], signature[v]);
            if (estimated_similarity >= similarity_threshold) cluster.push_back(v);
        }


        if (cluster.size() >= min_cluster_size) {
            for (ui v : cluster) assigned[v] = true;
            clusters.push_back(cluster);
        }
    }
    return clusters;
}

struct BiCluster
{
    vector<ui> left;
    vector<ui> right;
    eid edge_count;
    double density;
};


vector<BiCluster> build_disjoint_biclusters(const vector<vector<ui>>& left_clusters, ui nR, eid* b_pstart, eid* b_pend, ui* b_edges, double rho, ui min_left_size, ui min_right_size)
{
    ui cluster_count = left_clusters.size();


    vector<int> best_cluster(nR, -1);


    vector<double> best_support(nR, 0.0);


    vector<ui> best_edge_count(nR, 0);


    vector<ui> count(nR, 0);
    vector<ui> tag(nR, 0);
    ui current_tag = 0;
    vector<ui> touched_right;

    for (ui cid = 0; cid < cluster_count; ++cid) {
        const vector<ui>& left = left_clusters[cid];
        if (left.size() < min_left_size) continue;
        current_tag++;
        touched_right.clear();

        for (ui l : left) {
            for (eid p = b_pstart[l]; p < b_pend[l]; ++p) {
                ui r = b_edges[p];
                if (tag[r] != current_tag) {
                    tag[r] = current_tag;
                    count[r] = 0;
                    touched_right.push_back(r);
                }
                count[r]++;
            }
        }

        for (ui r : touched_right) {
            double support = static_cast<double>(count[r]) / static_cast<double>(left.size());
            if (support > best_support[r]) {
                best_support[r] = support;
                best_cluster[r] = cid;
                best_edge_count[r] = count[r];
            }

            else if (support == best_support[r] && count[r] > best_edge_count[r]) {
                best_cluster[r] = cid;
                best_edge_count[r] = count[r];
            }
        }
    }


    vector<vector<ui>> right_clusters(cluster_count);


    vector<eid> cluster_edges(cluster_count, 0);


    for (ui r = 0; r < nR; ++r) {
        int cid = best_cluster[r];
        if (cid == -1) continue;
        if (best_support[r] < rho) continue;
        right_clusters[cid].push_back(r);
        cluster_edges[cid] += best_edge_count[r];
    }


    vector<BiCluster> result;

    for (ui cid = 0; cid < cluster_count; ++cid) {
        const vector<ui>& left = left_clusters[cid];
        const vector<ui>& right = right_clusters[cid];
        if (left.size() < min_left_size) continue;
        if (right.size() < min_right_size) continue;
        double density = static_cast<double>(cluster_edges[cid]) / (static_cast<double>(left.size()) * static_cast<double>(right.size()));
        BiCluster cluster;
        cluster.left = left;
        cluster.right = right;
        cluster.edge_count = cluster_edges[cid];
        cluster.density = density;
        result.push_back(cluster);
    }
    return result;
}

void build_index_simnei_compress_hash(string name, double alpha)
{
    int tau = 3;


    vector<unordered_map<ui, char>> ver_sim_neis(n);
    eid similar_edges_cnt = obtain_ver_sim_neis(ver_sim_neis);
    similar_edges_cnt *= 2;
    cout<<"n: "<<n<<", sim_e: "<<similar_edges_cnt<<endl;

    eid * b_pstart = new eid[n];
    eid * b_pend = new eid[n];
    ui * b_edges = new ui[similar_edges_cnt];
    ui * b_degree = new ui[n];
    construct_bipartite_graph(ver_sim_neis, b_pstart, b_pend, b_edges, b_degree);


    ui original_n = n;
    vector<vector<pair<char,ui>>> residual_sim_nei;
    residual_sim_nei.resize(n);
    vector<vector<ui>> z_list;
    z_list.resize(n);
    vector<vector<pair<char,ui>>> z_R;
    ui z_idx = 0;


    long long remain_e = similar_edges_cnt;
    long long Residual_e = 0, Z_e = 0;

    ui * mark = new ui[n];
    memset(mark, 0, sizeof(ui)*n);
    ui * out_mapping = new ui[n];
    for(ui i = 0; i < n; ++i) out_mapping[i] = i;

    long long del_e = peel_reorg(ver_sim_neis, b_pstart, b_pend, b_edges, b_degree, residual_sim_nei, tau, out_mapping, remain_e);
    Residual_e += del_e;

    cout<<"1st vr, n: "<<n<<", sim_e: "<<remain_e<<endl;

    ui k = 4;
    ui bands = 2;

    double threshold = 0.1;
    ui min_cluster_size = 10;

    vector<vector<ui>> clusters = minhash_lsh_cluster(n, b_pstart, b_pend, b_edges, k, bands, threshold, min_cluster_size);

    cout<<"k = "<<k<<", bands = "<<bands<<", threshold = "<<threshold<<", min_cluster_size = "<<min_cluster_size<<endl;
    cout << "cluster number: " << clusters.size() << endl;
    ui clustered_nodes = 0;
    for (ui i = 0; i < clusters.size(); ++i) {
        clustered_nodes += clusters[i].size();
        cout << "cluster " << i << ", size = " << clusters[i].size();
        cout <<", AVE. js = "<<average_jaccard_in_cluster(clusters[i], b_pstart, b_pend, b_edges);
        cout << endl;
    }
    cout << "clustered nodes: " << clustered_nodes << " / " << n << endl;

    double rho = 0.1;
    ui min_left_size = 5;
    ui min_right_size = 5;

    vector<BiCluster> biclusters = build_disjoint_biclusters(clusters, n, b_pstart, b_pend, b_edges, rho, min_left_size, min_right_size);

    cout << "bicluster number: " << biclusters.size() << endl;

    for (ui i = 0; i < biclusters.size(); ++i) {
        cout << "bicluster " << i
             << ", left size = "
             << biclusters[i].left.size()
             << ", right size = "
             << biclusters[i].right.size()
             << ", edge count = "
             << biclusters[i].edge_count
             << ", density = "
             << biclusters[i].density
             << endl;
    }
}

struct LSHClusterConfig
{

    ui k = 64;
    ui band_count = 16;


    double min_estimated_js = 0.40;

    ui min_cluster_size = 10;


    ui min_left_size = 8;
    ui min_right_size = 8;


    ui max_left_size = 2000;
    ui max_right_size = 5000;


    double right_support_ratio = 0.10;
    ui min_right_support = 2;


    double left_support_ratio = 0.10;
    ui min_left_support = 2;


    double min_density = 0.10;


    int refine_rounds = 1;


    ui max_lsh_bucket_size = 10000;


    ui max_clusters_per_round = 100;


    long long min_gain = 10;


    bool sort_by_similarity = true;


    bool global_node_disjoint = true;
};


struct BuildLoopConfig
{
    int tau = 2;
    int max_round = 100;


    double residual_edge_ratio = 0.01;


    double sparse_avg_degree_stop = 4.0;


    double min_progress_ratio = 0.002;


    int max_stall_rounds = 2;


    bool adaptive_relax = true;
};

vector<BiCluster> obtain_multi_biclusters_lsh(ui n, eid* b_pstart, eid* b_pend, ui* b_edges, ui* b_degree, const LSHClusterConfig& cfg, double alpha)
{
    vector<vector<ui>> clusters = minhash_lsh_cluster(n, b_pstart, b_pend, b_edges, cfg.k, cfg.band_count, cfg.min_estimated_js, cfg.min_cluster_size);

    cout << "cluster number: " << clusters.size() << endl;
    ui clustered_nodes = 0;
    for (ui i = 0; i < clusters.size(); ++i) {
        clustered_nodes += clusters[i].size();
        cout << "cluster " << i << ", size = " << clusters[i].size();
        cout <<", AVE. js = "<<average_jaccard_in_cluster(clusters[i], b_pstart, b_pend, b_edges);
        cout << endl;
    }
    cout << "clustered nodes: " << clustered_nodes << " / " << n << endl;

    vector<BiCluster> biclusters = build_disjoint_biclusters(clusters, n, b_pstart, b_pend, b_edges, cfg.min_density, cfg.min_left_size, cfg.min_right_size);

    cout << "bicluster number: " << biclusters.size() << endl;

    for (ui i = 0; i < biclusters.size(); ++i) {
        cout << "bicluster " << i
             << ", left size = "
             << biclusters[i].left.size()
             << ", right size = "
             << biclusters[i].right.size()
             << ", edge count = "
             << biclusters[i].edge_count
             << ", density = "
             << biclusters[i].density
             << endl;
    }

    return biclusters;
}

long long peel_reorg(vector<unordered_map<ui,char>>& ver_sim_neis, eid *&b_pstart, eid *&b_pend, ui *&b_edges, ui *&b_degree, vector<vector<pair<char,ui>>>& residual_sim_nei, int tau, ui *l_out_mapping, ui *r_out_mapping, ui &l_n, ui &r_n)
{
    ui old_l_n = l_n;
    ui old_r_n = r_n;
    ui old_b_n = old_l_n + old_r_n;

    eid old_adj_cnt = 0;
    for(ui u = 0; u < old_b_n; ++u) {
        assert(b_degree[u] == b_pend[u] - b_pstart[u]);
        old_adj_cnt += b_pend[u] - b_pstart[u];
    }


    vector<char> del(old_b_n, 0);
    queue<ui> Q;

    for(ui u = 0; u < old_b_n; ++u) {
        if(b_degree[u] < (ui)tau) {
            del[u] = 1;
            Q.push(u);
        }
    }


    while(!Q.empty()) {
        ui u = Q.front();
        Q.pop();

        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];

            if(del[v]) continue;

            assert(b_degree[v] > 0);
            --b_degree[v];

            if(b_degree[v] < (ui)tau) {
                del[v] = 1;
                Q.push(v);
            }
        }
    }


    long long residual_logical_edge_cnt = 0;

    for(ui u = 0; u < old_l_n; ++u) {
        ui original_u = l_out_mapping[u];

        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];

            assert(v >= old_l_n && v < old_b_n);

            if(!del[u] && !del[v]) continue;

            ui right_local_id = v - old_l_n;
            ui original_v = r_out_mapping[right_local_id];

            assert(original_u != original_v);

            ui small_id = min(original_u, original_v);
            ui large_id = max(original_u, original_v);

            auto iter = ver_sim_neis[small_id].find(large_id);

            if(iter == ver_sim_neis[small_id].end()) {
                cout << "Cannot find similarity score: " << original_u << ", " << original_v << endl;
                exit(1);
            }

            char similarity = iter->second;

            residual_sim_nei[original_u].push_back(make_pair(similarity, original_v));
            ++residual_logical_edge_cnt;
        }
    }


    vector<ui> new_id(old_b_n, UINT_MAX);

    ui new_l_n = 0;

    for(ui u = 0; u < old_l_n; ++u) {
        if(del[u]) continue;

        new_id[u] = new_l_n;
        l_out_mapping[new_l_n] = l_out_mapping[u];
        ++new_l_n;
    }

    ui new_r_n = 0;

    for(ui right_local_id = 0; right_local_id < old_r_n; ++right_local_id) {
        ui old_global_id = old_l_n + right_local_id;

        if(del[old_global_id]) continue;

        new_id[old_global_id] = new_l_n + new_r_n;
        r_out_mapping[new_r_n] = r_out_mapping[right_local_id];
        ++new_r_n;
    }

    ui new_b_n = new_l_n + new_r_n;


    ui *new_b_degree = new ui[new_b_n];
    memset(new_b_degree, 0, sizeof(ui) * new_b_n);

    for(ui u = 0; u < old_b_n; ++u) {
        if(del[u]) continue;

        ui new_u = new_id[u];
        assert(new_u != UINT_MAX);

        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];

            if(del[v]) continue;

            assert(new_id[v] != UINT_MAX);
            ++new_b_degree[new_u];
        }
    }

    eid new_adj_cnt = 0;
    for(ui u = 0; u < new_b_n; ++u) new_adj_cnt += new_b_degree[u];

    eid *new_b_pstart = new eid[new_b_n];
    eid *new_b_pend = new eid[new_b_n];
    ui *new_b_edges = new ui[new_adj_cnt];

    eid pos = 0;

    for(ui u = 0; u < new_b_n; ++u) {
        new_b_pstart[u] = pos;
        new_b_pend[u] = pos;
        pos += new_b_degree[u];
    }

    assert(pos == new_adj_cnt);


    for(ui u = 0; u < old_b_n; ++u) {
        if(del[u]) continue;

        ui new_u = new_id[u];

        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];

            if(del[v]) continue;

            ui new_v = new_id[v];
            new_b_edges[new_b_pend[new_u]++] = new_v;
        }
    }

    for(ui u = 0; u < new_b_n; ++u) {
        assert(new_b_pend[u] - new_b_pstart[u] == new_b_degree[u]);
    }


    l_n = new_l_n;
    r_n = new_r_n;


    delete [] b_pstart;
    delete [] b_pend;
    delete [] b_edges;
    delete [] b_degree;

    b_pstart = new_b_pstart;
    b_pend = new_b_pend;
    b_edges = new_b_edges;
    b_degree = new_b_degree;

    assert(old_adj_cnt >= new_adj_cnt);

    long long deleted_adj_cnt = (long long)(old_adj_cnt - new_adj_cnt);


    assert(deleted_adj_cnt % 2 == 0);
    assert(deleted_adj_cnt / 2 == residual_logical_edge_cnt);

#ifdef _CheckInfo_
    cout << "******** after shrink_bigraph() ********" << endl;
    cout << "l_n: " << l_n << ", r_n: " << r_n << ", b_n: " << l_n + r_n << endl;
    cout << "remaining adjacency entries: " << new_adj_cnt << endl;
    cout << "deleted adjacency entries: " << deleted_adj_cnt << endl;
    cout << "residual logical edges: " << residual_logical_edge_cnt << endl;

    cout << "left mapping:" << endl;
    for(ui u = 0; u < l_n; ++u) {
        cout << "\tcurrent left " << u << " -> original " << l_out_mapping[u] << endl;
    }

    cout << "right mapping:" << endl;
    for(ui u = 0; u < r_n; ++u) {
        cout << "\tcurrent right " << l_n + u << " -> original " << r_out_mapping[u] << endl;
    }

    cout << "remaining bipartite graph:" << endl;

    for(ui u = 0; u < l_n + r_n; ++u) {
        cout << u << "(deg=" << b_degree[u] << "): ";

        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];
            cout << v << ", ";

            if(u < l_n) {
                assert(v >= l_n && v < l_n + r_n);
            }
            else {
                assert(v < l_n);
            }
        }

        cout << endl;
    }

#endif

    return deleted_adj_cnt;
}

vector<vector<ull>> compute_minhash_left(ui l_n, ui r_n, eid* b_pstart, eid* b_pend, ui* b_edges, ui k)
{
    vector<vector<ull>> signature(l_n, vector<ull>(k, ULLONG_MAX));

    mt19937_64 rng(123456);
    vector<ull> seeds(k);

    for(ui i = 0; i < k; ++i) seeds[i] = rng();

    for(ui u = 0; u < l_n; ++u) {
        for(eid p = b_pstart[u]; p < b_pend[u]; ++p) {
            ui right_global_id = b_edges[p];

            assert(right_global_id >= l_n);
            assert(right_global_id < l_n + r_n);

            ui right_local_id = right_global_id - l_n;

            for(ui i = 0; i < k; ++i) {
                ull value = hash64((ull)right_local_id ^ seeds[i]);
                if(value < signature[u][i]) signature[u][i] = value;
            }
        }
    }

    return signature;
}

vector<vector<ui>> minhash_lsh_cluster_left(ui l_n, ui r_n, eid* b_pstart, eid* b_pend, ui* b_edges, ui k, ui band_count, double similarity_threshold, ui min_cluster_size)
{
    if(k == 0 || band_count == 0 || k % band_count != 0) {
        cout << "Error: k must be divisible by band_count." << endl;
        return {};
    }

    ui rows_per_band = k / band_count;


    vector<vector<ull>> signature = compute_minhash_left(l_n, r_n, b_pstart, b_pend, b_edges, k);


    vector<unordered_map<ull, vector<ui>>> band_table(band_count);

    for(ui v = 0; v < l_n; ++v) {
        if(signature[v][0] == ULLONG_MAX) continue;

        for(ui band = 0; band < band_count; ++band) {
            ull key = get_band_key(signature[v], band, rows_per_band);
            band_table[band][key].push_back(v);
        }
    }


    vector<bool> assigned(l_n, false);
    vector<vector<ui>> clusters;

    for(ui center = 0; center < l_n; ++center) {
        if(assigned[center]) continue;
        if(signature[center][0] == ULLONG_MAX) continue;


        set<ui> candidates;

        for(ui band = 0; band < band_count; ++band) {
            ull key = get_band_key(signature[center], band, rows_per_band);
            auto it = band_table[band].find(key);

            if(it == band_table[band].end()) continue;

            for(ui v : it->second) candidates.insert(v);
        }

        vector<ui> cluster;
        cluster.push_back(center);

        for(ui v : candidates) {
            if(v == center) continue;
            if(assigned[v]) continue;

            double estimated_similarity = estimate_jaccard(signature[center], signature[v]);

            if(estimated_similarity >= similarity_threshold) {
                cluster.push_back(v);
            }
        }

        if(cluster.size() >= min_cluster_size) {
            for(ui v : cluster) assigned[v] = true;
            clusters.push_back(cluster);
        }
    }
    return clusters;
}

vector<BiCluster> build_disjoint_biclusters(const vector<vector<ui>>& left_clusters, ui l_n, ui r_n, eid* b_pstart, eid* b_pend, ui* b_edges, double rho, ui min_left_size, ui min_right_size)
{
    ui cluster_count = left_clusters.size();


    vector<int> best_cluster(r_n, -1);
    vector<ui> best_edge_count(r_n, 0);
    vector<ui> best_left_size(r_n, 0);

    vector<ui> count(r_n, 0);
    vector<ui> tag(r_n, 0);

    ui current_tag = 0;
    vector<ui> touched_right;


    for(ui cid = 0; cid < cluster_count; ++cid) {
        const vector<ui>& left = left_clusters[cid];

        if(left.size() < min_left_size) continue;

        ++current_tag;
        touched_right.clear();


        for(ui l : left) {
            assert(l < l_n);

            for(eid p = b_pstart[l]; p < b_pend[l]; ++p) {
                ui right_global_id = b_edges[p];

                assert(right_global_id >= l_n);
                assert(right_global_id < l_n + r_n);

                ui right_local_id = right_global_id - l_n;

                if(tag[right_local_id] != current_tag) {
                    tag[right_local_id] = current_tag;
                    count[right_local_id] = 0;
                    touched_right.push_back(right_local_id);
                }

                ++count[right_local_id];
            }
        }


        for(ui right_local_id : touched_right) {
            bool better = false;

            if(best_cluster[right_local_id] == -1) {
                better = true;
            }
            else {
                ull current_value = (ull)count[right_local_id] * best_left_size[right_local_id];
                ull previous_value = (ull)best_edge_count[right_local_id] * left.size();

                if(current_value > previous_value) {
                    better = true;
                }
                else if(current_value == previous_value && count[right_local_id] > best_edge_count[right_local_id]) {
                    better = true;
                }
            }

            if(better) {
                best_cluster[right_local_id] = cid;
                best_edge_count[right_local_id] = count[right_local_id];
                best_left_size[right_local_id] = left.size();
            }
        }
    }


    vector<vector<ui>> right_clusters(cluster_count);
    vector<eid> cluster_edges(cluster_count, 0);


    for(ui right_local_id = 0; right_local_id < r_n; ++right_local_id) {
        int cid = best_cluster[right_local_id];

        if(cid == -1) continue;

        double support = (double)best_edge_count[right_local_id] / (double)best_left_size[right_local_id];

        if(support < rho) continue;

        ui right_global_id = l_n + right_local_id;

        right_clusters[cid].push_back(right_global_id);
        cluster_edges[cid] += best_edge_count[right_local_id];
    }


    vector<BiCluster> result;

    for(ui cid = 0; cid < cluster_count; ++cid) {
        const vector<ui>& left = left_clusters[cid];
        const vector<ui>& right = right_clusters[cid];

        if(left.size() < min_left_size) continue;
        if(right.size() < min_right_size) continue;

        double density = (double)cluster_edges[cid] / ((double)left.size() * (double)right.size());


        assert(density + 1e-12 >= rho);

        BiCluster cluster;
        cluster.left = left;
        cluster.right = right;
        cluster.edge_count = cluster_edges[cid];
        cluster.density = density;

        result.push_back(cluster);
    }

    return result;
}

void check_bigraph_correct(eid *&b_pstart, eid *&b_pend, ui *&b_edges, ui *&b_degree, ui l_n, ui r_n)
{
    for(ui u = 0; u < l_n + r_n; ++u) {
        assert(b_degree[u] == b_pend[u] - b_pstart[u]);
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];
            if(u < l_n) assert(v >= l_n && v < l_n + r_n);
            else assert(v < l_n);
        }
    }
    for(ui u = 0; u < l_n + r_n; ++u) {
        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i]; bool found = false;
            for(eid j = b_pstart[v]; j < b_pend[v]; ++j) { if(b_edges[j] == u) { found = true; break; } }
            if(!found) { cout << "missing reverse CSR entry: " << u << " -- " << v << endl; exit(1); }
        }
    }
}

void check_biclusters_disjoint(const vector<BiCluster>& biclusters, ui l_n, ui r_n)
{
    vector<int> left_owner(l_n, -1);
    vector<int> right_owner(r_n, -1);

    for(ui cid = 0; cid < biclusters.size(); ++cid) {
        for(ui u : biclusters[cid].left) {
            assert(u < l_n);
            assert(left_owner[u] == -1);
            left_owner[u] = cid;
        }

        for(ui r : biclusters[cid].right) {
            assert(r >= l_n && r < l_n + r_n);

            ui rid = r - l_n;

            assert(right_owner[rid] == -1);
            right_owner[rid] = cid;
        }
    }
}

struct CompressLoopConfig
{
    int tau = 3;
    int max_round = 100;

    ui k = 32;
    ui bands = 8;

    double threshold = 0.20;
    double rho = 0.10;

    ui min_cluster_size = 10;
    ui min_left_size = min_cluster_size;
    ui min_right_size = min_cluster_size;


    double stop_remain_ratio = 0.01;

    double sparse_avg_degree_stop = 3.5;

    double min_progress_ratio = 0.002;

    int max_stall_rounds = 2;

    bool require_positive_gain = true;
    long long min_gain = 1;

    bool adaptive_relax = true;
    double min_threshold = threshold/10;
    double min_rho = rho/10;
};

long long remove_edges_in_bicluster(const BiCluster& cluster, eid* b_pstart, eid* b_pend, ui* b_edges, ui* b_degree, vector<char>& mark_L, vector<char>& mark_R)
{
    for(ui u : cluster.left) mark_L[u] = 1;
    for(ui r : cluster.right) mark_R[r] = 1;
    long long removed_adj_cnt = 0;

    for(ui u : cluster.left) {
        eid write_pos = b_pstart[u];
        for(eid p = b_pstart[u]; p < b_pend[u]; ++p) {
            ui v = b_edges[p];
            if(mark_R[v]) ++removed_adj_cnt;
            else b_edges[write_pos++] = v;
        }
        b_pend[u] = write_pos;
        b_degree[u] = b_pend[u] - b_pstart[u];
    }

    for(ui r : cluster.right) {
        eid write_pos = b_pstart[r];
        for(eid p = b_pstart[r]; p < b_pend[r]; ++p) {
            ui v = b_edges[p];
            if(mark_L[v]) ++removed_adj_cnt;
            else b_edges[write_pos++] = v;
        }
        b_pend[r] = write_pos;
        b_degree[r] = b_pend[r] - b_pstart[r];
    }
    for(ui u : cluster.left) mark_L[u] = 0;
    for(ui r : cluster.right) mark_R[r] = 0;
    assert(removed_adj_cnt % 2 == 0);
#ifdef _CheckInfo_

    if(removed_adj_cnt != 2LL * cluster.edge_count) {
        cout << "removed_adj_cnt = " << removed_adj_cnt << ", expected = " << 2LL * cluster.edge_count << endl;
        exit(1);
    }
#endif

    return removed_adj_cnt;
}

void final_bigraph_to_residual(vector<unordered_map<ui,char>>& ver_sim_neis, eid* b_pstart, eid* b_pend, ui* b_edges, vector<vector<pair<char,ui>>>& residual_sim_nei, ui* l_out_mapping, ui* r_out_mapping, ui l_n, ui r_n)
{
    long long residual_edge_cnt = 0;


    for(ui u = 0; u < l_n; ++u) {
        ui original_u = l_out_mapping[u];

        for(eid i = b_pstart[u]; i < b_pend[u]; ++i) {
            ui v = b_edges[i];

            assert(v >= l_n && v < l_n + r_n);

            ui right_local_id = v - l_n;
            ui original_v = r_out_mapping[right_local_id];

            assert(original_u != original_v);

            char similarity;

            if(original_u < original_v) {
                auto iter = ver_sim_neis[original_u].find(original_v);

                if(iter == ver_sim_neis[original_u].end()) {
                    cout << "Cannot find similarity score: " << original_u << ", " << original_v << endl;
                    exit(1);
                }

                similarity = iter->second;
            }
            else {
                auto iter = ver_sim_neis[original_v].find(original_u);

                if(iter == ver_sim_neis[original_v].end()) {
                    cout << "Cannot find similarity score: " << original_u << ", " << original_v << endl;
                    exit(1);
                }

                similarity = iter->second;
            }


            residual_sim_nei[original_u].push_back(make_pair(similarity, original_v));
            ++residual_edge_cnt;
        }
    }

#ifdef _CheckInfo_
    cout << "FINAL residual logical edges: " << residual_edge_cnt << endl;
#endif
}

string build_config_name(const CompressLoopConfig& cfg)
{
    string config_name;

    config_name += "tau" + to_string(cfg.tau);
    config_name += "_maxr" + to_string(cfg.max_round);

    config_name += "_k" + to_string(cfg.k);
    config_name += "_b" + to_string(cfg.bands);

    config_name += "_th" + format_double(cfg.threshold);
    config_name += "_rho" + format_double(cfg.rho);

    config_name += "_mc" + to_string(cfg.min_cluster_size);
    config_name += "_mg" + to_string(cfg.min_gain);

    return config_name;
}

void build_db_index(string name, int cfg_tau, int cfg_maxr, ui cfg_k, ui cfg_bands, double cfg_threshold, double cfg_rho, ui cfg_min_cluster_size, ui cfg_min_gain)
{
    Timer t;

    CompressLoopConfig cfg;

    cfg.tau = cfg_tau;
    cfg.max_round = cfg_maxr;

    cfg.k = cfg_k;
    cfg.bands = cfg_bands;

    cfg.threshold = cfg_threshold;
    cfg.rho = cfg_rho;

    cfg.min_cluster_size = cfg_min_cluster_size;
    cfg.min_left_size = cfg.min_cluster_size;
    cfg.min_right_size = cfg.min_cluster_size;

    cfg.stop_remain_ratio = 0.01;
    cfg.sparse_avg_degree_stop = 3.5;
    cfg.min_progress_ratio = 0.002;
    cfg.max_stall_rounds = 2;
    cfg.require_positive_gain = true;

    cfg.min_gain = cfg_min_gain;

    cfg.adaptive_relax = true;
    cfg.min_threshold = cfg.threshold/10;
    cfg.min_rho = cfg.rho/10;


    vector<unordered_map<ui, char>> ver_sim_neis(n);
    eid similar_pair_cnt = obtain_ver_sim_neis(ver_sim_neis);
    ui l_n = n;
    ui r_n = n;
    ui b_n = l_n + r_n;
    eid b_adj_cnt = 4 * similar_pair_cnt;

    cout<<"l_n: "<<l_n<<", r_n: "<<r_n<<", sim_e: "<<b_adj_cnt<<endl;


    eid * b_pstart = new eid[b_n];
    eid * b_pend = new eid[b_n];
    ui * b_edges = new ui[b_adj_cnt];
    ui * b_degree = new ui[b_n];
    construct_bipartite_graph(ver_sim_neis, b_pstart, b_pend, b_edges, b_degree, l_n, r_n);


    ui original_n = l_n;
    vector<vector<pair<char,ui>>> residual_sim_nei;
    residual_sim_nei.resize(l_n);
    vector<vector<ui>> z_list;
    z_list.resize(l_n);
    vector<vector<pair<char,ui>>> z_R;
    ui z_idx = 0;


    long long remain_e = b_adj_cnt;
    long long Residual_e = 0, Z_e = 0;
    long long total_gain = 0;

    ui * l_out_mapping = new ui[l_n];
    for(ui i = 0; i < l_n; ++i) l_out_mapping[i] = i;
    ui * r_out_mapping = new ui[r_n];
    for(ui i = l_n; i < l_n + r_n; ++i) r_out_mapping[i-l_n] = i - l_n;

    long long del_e = peel_reorg(ver_sim_neis, b_pstart, b_pend, b_edges, b_degree, residual_sim_nei, cfg.tau, l_out_mapping, r_out_mapping, l_n, r_n);
#ifdef _CostlyDebug_
    check_bigraph_correct(b_pstart, b_pend, b_edges, b_degree, l_n, r_n);
#endif
    Residual_e += del_e;
    remain_e -= del_e;
    cout<<"1st vr, l_n: "<<l_n<<", r_n: "<<r_n<<", remain_e: "<<remain_e<<endl;


    vector<char> mark_L(2 * original_n, 0);
    vector<char> mark_R(2 * original_n, 0);

    ui k = cfg.k;
    ui bands = cfg.bands;
    double threshold = cfg.threshold;
    ui min_cluster_size = cfg.min_cluster_size;

    double rho = cfg.rho;
    ui min_left_size = cfg.min_left_size;
    ui min_right_size = cfg.min_right_size;

    int round = 0;
    int stall_rounds = 0;

    while(round++ < cfg.max_round) {

        if(remain_e <= 0 || l_n == 0 || r_n == 0) break;

        assert(remain_e % 2 == 0);

        long long remain_logical_edges = remain_e / 2;
        double remain_ratio = (double)remain_e / (double)b_adj_cnt;


        long long min_required_edges = (long long)ceil(rho * min_left_size * min_right_size);

        if(remain_ratio <= cfg.stop_remain_ratio) {
            cout << "stop: remaining edge ratio = " << remain_ratio << endl; break;
        }

        if(remain_logical_edges < min_required_edges) {
            cout << "stop: too few logical edges, remain = " << remain_logical_edges << ", required = " << min_required_edges << endl; break;
        }

        if(l_n < min_left_size || r_n < min_right_size) {
            cout << "stop: too few vertices, l_n = " << l_n << ", r_n = " << r_n << endl; break;
        }

        double average_left_degree = (double)remain_logical_edges / (double)l_n;
        double average_right_degree = (double)remain_logical_edges / (double)r_n;
        double smaller_average_degree = min(average_left_degree, average_right_degree);

        if(cfg.sparse_avg_degree_stop > 0 && smaller_average_degree < cfg.sparse_avg_degree_stop) {
            cout << "stop: remaining bigraph is sparse, avgL = " << average_left_degree << ", avgR = " << average_right_degree << endl;
            break;
        }

        cout << endl << "*************** ROUND " << round << " ***************" << endl;
        cout << "l_n: " << l_n << ", r_n: " << r_n << ", remain adj: " << remain_e
             << ", logical edges: " << remain_logical_edges
             << ", avgL: " << average_left_degree << ", avgR: " << average_right_degree << endl;

        cout << "k: " << k << ", bands: " << bands << ", threshold: " << threshold
             << ", min cluster size: " << min_cluster_size << ", rho: " << rho << endl;

        long long remain_before_round = remain_e;
        long long round_z_adj = 0;
        long long round_residual_adj = 0;
        long long round_gain = 0;

        ui valid_bicluster_cnt = 0;
        ui valid_left_size_sum = 0;
        ui valid_right_size_sum = 0;


        vector<vector<ui>> clusters = minhash_lsh_cluster_left(l_n, r_n, b_pstart, b_pend, b_edges, k, bands, threshold, min_cluster_size);


        vector<BiCluster> biclusters = build_disjoint_biclusters(clusters, l_n, r_n, b_pstart, b_pend, b_edges, rho, min_left_size, min_right_size);
        check_biclusters_disjoint(biclusters, l_n, r_n);

        cout << "left cluster #: " << clusters.size() << ", bicluster #: " << biclusters.size() << endl;


        for(const BiCluster& bicluster : biclusters) {

            if(bicluster.left.size() < min_left_size) continue;
            if(bicluster.right.size() < min_right_size) continue;
            if(bicluster.edge_count == 0) continue;


            long long gain = (long long)bicluster.edge_count - (long long)bicluster.left.size() - (long long)bicluster.right.size();
            total_gain += gain;

            if(cfg.require_positive_gain && gain < cfg.min_gain) continue;


            vector<ui> original_L;
            vector<ui> original_R;

            original_L.reserve(bicluster.left.size());
            original_R.reserve(bicluster.right.size());

            for(ui u : bicluster.left) {
                assert(u < l_n);
                original_L.push_back(l_out_mapping[u]);
            }

            for(ui r : bicluster.right) {
                assert(r >= l_n && r < l_n + r_n);
                ui right_local_id = r - l_n;
                original_R.push_back(r_out_mapping[right_local_id]);
            }


            long long removed_adj = remove_edges_in_bicluster(bicluster, b_pstart, b_pend, b_edges, b_degree, mark_L, mark_R);
            assert(removed_adj != 0);
            long long expected_removed_adj = 2LL * bicluster.edge_count;

            if(removed_adj != expected_removed_adj) {
                cout << "Error: removed adjacency count is incorrect!" << endl;
                cout << "removed_adj: " << removed_adj
                     << ", expected: " << expected_removed_adj
                     << ", L size: " << bicluster.left.size()
                     << ", R size: " << bicluster.right.size()
                     << ", edge_count: " << bicluster.edge_count << endl;
                exit(1);
            }


            build_index(original_L, original_R, z_list, ver_sim_neis, z_R, z_idx);

            assert(remain_e >= removed_adj);

            remain_e -= removed_adj;
            Z_e += removed_adj;
            round_z_adj += removed_adj;
            round_gain += gain;

            ++valid_bicluster_cnt;
            valid_left_size_sum += bicluster.left.size();
            valid_right_size_sum += bicluster.right.size();


        }


        long long shrink_del_adj = peel_reorg(ver_sim_neis, b_pstart, b_pend, b_edges, b_degree, residual_sim_nei, cfg.tau, l_out_mapping, r_out_mapping, l_n, r_n);

        assert(remain_e >= shrink_del_adj);

        remain_e -= shrink_del_adj;
        Residual_e += shrink_del_adj;
        round_residual_adj += shrink_del_adj;

        long long deleted_this_round = remain_before_round - remain_e;
        double progress_ratio = remain_before_round > 0 ? (double)deleted_this_round / (double)remain_before_round : 0.0;

        cout << "==round result==" << endl;
        cout << "\tvalid bicluster #: " << valid_bicluster_cnt << endl;

        if(valid_bicluster_cnt > 0) {
            cout << "\tAVE. left size: " << valid_left_size_sum / valid_bicluster_cnt << endl;
            cout << "\tAVE. right size: " << valid_right_size_sum / valid_bicluster_cnt << endl;
        }

        cout << "\tZ removed adj: " << round_z_adj
             << ", residual removed adj: " << round_residual_adj
             << ", total removed adj: " << deleted_this_round
             << ", gain: " << round_gain
             << ", remain adj: " << remain_e
             << ", progress: " << progress_ratio << endl;

    #ifdef _CheckInfo_
        long long check_adj_cnt = 0;
        for(ui u = 0; u < l_n + r_n; ++u) check_adj_cnt += b_pend[u] - b_pstart[u];

        if(check_adj_cnt != remain_e) {
            cout << "check_adj_cnt = " << check_adj_cnt << ", remain_e = " << remain_e << endl;
            exit(1);
        }
    #endif


        bool stalled = valid_bicluster_cnt == 0 || progress_ratio < cfg.min_progress_ratio;

        if(stalled) {
            ++stall_rounds;


            if(cfg.adaptive_relax && stall_rounds < cfg.max_stall_rounds) {

                double old_threshold = threshold;
                double old_rho = rho;
                ui old_bands = bands;
                ui old_min_cluster_size = min_cluster_size;

                threshold = max(cfg.min_threshold, threshold * 0.80);
                rho = max(cfg.min_rho, rho * 0.80);
                min_cluster_size = max(min_left_size, (ui)ceil(min_cluster_size * 0.80));

                if(bands * 2 <= k && k % (bands * 2) == 0) bands *= 2;

                cout << "relax parameters:"
                     << " threshold " << old_threshold << " -> " << threshold
                     << ", rho " << old_rho << " -> " << rho
                     << ", bands " << old_bands << " -> " << bands
                     << ", min cluster size " << old_min_cluster_size << " -> " << min_cluster_size << endl;
            }
        }
        else {
            stall_rounds = 0;
        }

        if(stall_rounds >= cfg.max_stall_rounds) {
            cout << "stop: too little progress for " << stall_rounds << " consecutive rounds." << endl;
            break;
        }
    }


    if(remain_e > 0) {
        assert(remain_e % 2 == 0);
        final_bigraph_to_residual(ver_sim_neis, b_pstart, b_pend, b_edges, residual_sim_nei, l_out_mapping, r_out_mapping, l_n, r_n);
        Residual_e += remain_e;
        remain_e = 0;
    }

    assert(remain_e == 0);
    assert(Z_e + Residual_e == (long long)b_adj_cnt);

    for(ui i = 0; i < original_n; ++i) {
        sort(residual_sim_nei[i].begin(), residual_sim_nei[i].end(), [](const pair<char, ui>& a, const pair<char, ui>& b) {
            return a.first > b.first;
        });
    }

    delete [] b_pstart;
    delete [] b_pend;
    delete [] b_edges;
    delete [] b_degree;
    delete [] l_out_mapping;
    delete [] r_out_mapping;

    cout<<"*************** INDEX INFO ***************"<<endl;
    cout<<"z_idx: "<<z_idx<<endl;
    cout<<((int)(((double)((double)Z_e/b_adj_cnt))*100))<<"% edges in Z"<<endl;
    cout<<((int)(((double)((double)(Residual_e)/b_adj_cnt))*100))<<"% edges in Residual"<<endl;
    long long original_logical_edges = b_adj_cnt / 2;
    double saving_ratio = original_logical_edges > 0 ? (double)total_gain / original_logical_edges : 0.0;
    double compressed_ratio = 1.0 - saving_ratio;
    cout << "estimated saving ratio: " << saving_ratio * 100 << "%" << endl;
    cout << "estimated compressed/original ratio: " << compressed_ratio * 100 << "%" << endl;


    string out_dir = "./index";
    std::filesystem::create_directory(out_dir);

    string config_name = build_config_name(cfg);

    string file_a = out_dir + "/" + name + "_" + config_name + "_DBa.bin";
    string file_b = out_dir + "/" + name + "_" + config_name + "_DBb.bin";


    FILE * f = Utility::open_file(file_a.c_str(), "wb");
    fwrite(&original_n, sizeof(ui), 1, f);
    for(ui u = 0; u < original_n; ++u) {


        auto tmpvec = residual_sim_nei[u];
        ui num = (ui)tmpvec.size();
        fwrite(&num, sizeof(ui), 1, f);
        for(auto eachpair : tmpvec) {
            fwrite(&eachpair.first, sizeof(char), 1, f);
            fwrite(&eachpair.second, sizeof(ui), 1, f);
        }
        auto zvec = z_list[u];
        num = (ui)zvec.size();
        fwrite(&num, sizeof(ui), 1, f);
        for(ui z : zvec) {
            fwrite(&z, sizeof(ui), 1, f);
        }
    }
    fclose(f);

    f = Utility::open_file(file_b.c_str(), "wb");
    fwrite(&z_idx, sizeof(ui), 1, f);
    if(z_R.size() != z_idx) {
        cout<<"z_R.size() != z_idx"<<endl;
        exit(1);
    }
    for(auto eachzr : z_R) {


        ui num = (ui)eachzr.size();
        fwrite(&num, sizeof(ui), 1, f);
        for(auto eachpair : eachzr) {
            fwrite(&eachpair.first, sizeof(char), 1, f);
            fwrite(&eachpair.second, sizeof(ui), 1, f);
        }
    }
    fclose(f);
    cout<<"finish writing DB index to disk."<<endl;

}

static inline long long biclique_gain(ui left_size, ui right_size)
{
    return (long long)left_size * (long long)right_size
         - (long long)left_size
         - (long long)right_size;
}

ui count_unused_right_neighbors(ui u, ui l_n, ui r_n, eid* b_pstart, eid* b_pend, ui* b_edges, const vector<char>& used_R)
{
    assert(u < l_n);

    ui cnt = 0;

    for(eid p = b_pstart[u]; p < b_pend[u]; ++p) {
        ui v = b_edges[p];

        assert(v >= l_n && v < l_n + r_n);

        if(!used_R[v]) ++cnt;
    }

    return cnt;
}

bool build_one_maximal_biclique_from_seed(ui seed_u, ui l_n, ui r_n, eid* b_pstart, eid* b_pend, ui* b_edges, const vector<char>& used_L, const vector<char>& used_R, ui min_left_size, ui min_right_size, long long min_gain, vector<ui>& left_cnt, vector<ui>& left_touched, vector<ui>& right_cnt, vector<ui>& right_touched, vector<char>& in_L, vector<char>& in_R, BiCluster& result)
{
    result.left.clear();
    result.right.clear();
    result.edge_count = 0;
    result.density = 1.0;

    if(seed_u >= l_n) return false;
    if(used_L[seed_u]) return false;


    vector<ui> L;
    vector<ui> R;

    L.push_back(seed_u);
    in_L[seed_u] = 1;

    for(eid p = b_pstart[seed_u]; p < b_pend[seed_u]; ++p) {
        ui v = b_edges[p];

        assert(v >= l_n && v < l_n + r_n);

        if(used_R[v]) continue;
        if(in_R[v]) continue;

        in_R[v] = 1;
        R.push_back(v);
    }

    if(R.size() < min_right_size) {
        in_L[seed_u] = 0;
        for(ui r : R) in_R[r] = 0;
        return false;
    }

    long long cur_gain = biclique_gain((ui)L.size(), (ui)R.size());


    while(true) {
        left_touched.clear();


        for(ui r : R) {
            assert(r >= l_n && r < l_n + r_n);

            for(eid p = b_pstart[r]; p < b_pend[r]; ++p) {
                ui x = b_edges[p];

                assert(x < l_n);

                if(used_L[x]) continue;
                if(in_L[x]) continue;

                if(left_cnt[x] == 0) left_touched.push_back(x);
                ++left_cnt[x];
            }
        }

        ui best_x = (ui)-1;
        ui best_overlap = 0;
        long long best_gain = cur_gain;

        for(ui x : left_touched) {
            ui overlap = left_cnt[x];

            if(overlap >= min_right_size) {
                long long new_gain = biclique_gain((ui)L.size() + 1, overlap);

                if(new_gain > best_gain) {
                    best_gain = new_gain;
                    best_x = x;
                    best_overlap = overlap;
                }
            }

            left_cnt[x] = 0;
        }


        if(best_x == (ui)-1) break;


        vector<ui> new_R;
        new_R.reserve(best_overlap);

        for(eid p = b_pstart[best_x]; p < b_pend[best_x]; ++p) {
            ui v = b_edges[p];

            assert(v >= l_n && v < l_n + r_n);

            if(used_R[v]) continue;
            if(in_R[v]) new_R.push_back(v);
        }

        for(ui r : R) in_R[r] = 0;

        R.swap(new_R);

        for(ui r : R) in_R[r] = 1;

        L.push_back(best_x);
        in_L[best_x] = 1;

        cur_gain = best_gain;
    }


    left_touched.clear();

    for(ui r : R) {
        for(eid p = b_pstart[r]; p < b_pend[r]; ++p) {
            ui x = b_edges[p];

            assert(x < l_n);

            if(used_L[x]) continue;
            if(in_L[x]) continue;

            if(left_cnt[x] == 0) left_touched.push_back(x);
            ++left_cnt[x];
        }
    }

    for(ui x : left_touched) {
        if(left_cnt[x] == R.size()) {
            L.push_back(x);
            in_L[x] = 1;
        }

        left_cnt[x] = 0;
    }


    right_touched.clear();

    for(ui x : L) {
        for(eid p = b_pstart[x]; p < b_pend[x]; ++p) {
            ui r = b_edges[p];

            assert(r >= l_n && r < l_n + r_n);

            if(used_R[r]) continue;

            if(right_cnt[r] == 0) right_touched.push_back(r);
            ++right_cnt[r];
        }
    }

    for(ui r : R) in_R[r] = 0;
    R.clear();

    for(ui r : right_touched) {
        if(right_cnt[r] == L.size()) {
            R.push_back(r);
            in_R[r] = 1;
        }

        right_cnt[r] = 0;
    }


    bool ok = true;

    if(L.size() < min_left_size) ok = false;
    if(R.size() < min_right_size) ok = false;

    long long final_gain = biclique_gain((ui)L.size(), (ui)R.size());

    if(final_gain < min_gain) ok = false;

    if(ok) {
        sort(L.begin(), L.end());
        sort(R.begin(), R.end());

        result.left.swap(L);
        result.right.swap(R);
        result.edge_count = (eid)result.left.size() * (eid)result.right.size();
        result.density = 1.0;
    }


    for(ui x : L) in_L[x] = 0;
    for(ui r : R) in_R[r] = 0;

    if(ok) {
        for(ui x : result.left) in_L[x] = 0;
        for(ui r : result.right) in_R[r] = 0;
    }

    return ok;
}

vector<BiCluster> find_disjoint_maximal_bicliques_heuristic(ui l_n, ui r_n, eid* b_pstart, eid* b_pend, ui* b_edges, ui min_left_size, ui min_right_size, long long min_gain)
{
    vector<BiCluster> bicliques;

    if(l_n == 0 || r_n == 0) return bicliques;


    vector<char> used_L(l_n, 0);
    vector<char> used_R(l_n + r_n, 0);


    vector<ui> left_order;
    left_order.reserve(l_n);

    for(ui u = 0; u < l_n; ++u) {
        if(b_pend[u] > b_pstart[u]) {
            left_order.push_back(u);
        }
    }

    sort(left_order.begin(), left_order.end(), [&](ui a, ui b) {
        ui da = (ui)(b_pend[a] - b_pstart[a]);
        ui db = (ui)(b_pend[b] - b_pstart[b]);

        if(da != db) return da > db;
        return a < b;
    });


    vector<ui> left_cnt(l_n, 0);
    vector<ui> right_cnt(l_n + r_n, 0);

    vector<ui> left_touched;
    vector<ui> right_touched;

    vector<char> in_L(l_n, 0);
    vector<char> in_R(l_n + r_n, 0);

    ui tried_seed_cnt = 0;

    for(ui seed_u : left_order) {
        if(used_L[seed_u]) continue;


        ui unused_right_degree =
            count_unused_right_neighbors(seed_u, l_n, r_n, b_pstart, b_pend, b_edges, used_R);

        if(unused_right_degree < min_right_size) continue;

        ++tried_seed_cnt;

        BiCluster cand;

        bool ok =
            build_one_maximal_biclique_from_seed(seed_u, l_n, r_n, b_pstart, b_pend, b_edges, used_L, used_R, min_left_size, min_right_size, min_gain, left_cnt, left_touched, right_cnt, right_touched, in_L, in_R, cand);

        if(!ok) continue;


        bool conflict = false;

        for(ui u : cand.left) {
            if(used_L[u]) {
                conflict = true;
                break;
            }
        }

        if(!conflict) {
            for(ui r : cand.right) {
                if(used_R[r]) {
                    conflict = true;
                    break;
                }
            }
        }

        if(conflict) continue;


        for(ui u : cand.left) used_L[u] = 1;
        for(ui r : cand.right) used_R[r] = 1;

        bicliques.push_back(move(cand));
    }

    cout << "biclique seed tried #: " << tried_seed_cnt
         << ", accepted maximal biclique #: " << bicliques.size() << endl;

#ifdef _CheckInfo_


    vector<char> check_L(l_n, 0);
    vector<char> check_R(l_n + r_n, 0);

    for(const BiCluster& bc : bicliques) {
        for(ui u : bc.left) {
            assert(u < l_n);
            assert(!check_L[u]);
            check_L[u] = 1;
        }

        for(ui r : bc.right) {
            assert(r >= l_n && r < l_n + r_n);
            assert(!check_R[r]);
            check_R[r] = 1;
        }

        assert(bc.edge_count == (eid)bc.left.size() * (eid)bc.right.size());
        assert(bc.density == 1.0);
    }
#endif

    return bicliques;
}

static inline long long fast_biclique_gain(ui left_size, ui right_size)
{
    return (long long)left_size * (long long)right_size
         - (long long)left_size
         - (long long)right_size;
}

static inline int fast_next_mark(vector<int>& mark, int& token)
{
    ++token;

    if(token == INT_MAX) {
        fill(mark.begin(), mark.end(), 0);
        token = 1;
    }

    return token;
}


bool build_one_fast_maximal_biclique_from_seed(ui seed_u, ui l_n, ui r_n, eid* b_pstart, eid* b_pend, ui* b_edges, const vector<char>& used_L, const vector<char>& used_R, ui min_left_size, ui min_right_size, long long min_gain, ui anchor_cnt, ui max_candidate_left, vector<int>& mark_R, int& mark_token, vector<char>& in_L, vector<ui>& left_cnt, vector<ui>& touched_left, vector<ui>& L, vector<ui>& R, vector<ui>& new_R, vector<ui>& anchors, vector<ui>& candidates, BiCluster& result)
{
    result.left.clear();
    result.right.clear();
    result.edge_count = 0;
    result.density = 1.0;

    if(seed_u >= l_n) return false;
    if(used_L[seed_u]) return false;

    L.clear();
    R.clear();
    new_R.clear();
    anchors.clear();
    candidates.clear();


    L.push_back(seed_u);
    in_L[seed_u] = 1;

    for(eid p = b_pstart[seed_u]; p < b_pend[seed_u]; ++p) {
        ui r = b_edges[p];

        assert(r >= l_n && r < l_n + r_n);

        if(used_R[r]) continue;

        R.push_back(r);
    }

    if(R.size() < min_right_size) {
        in_L[seed_u] = 0;
        return false;
    }


    if(anchor_cnt == 0) anchor_cnt = 1;
    if(anchor_cnt > R.size()) anchor_cnt = (ui)R.size();

    for(ui r : R) {
        if(anchors.size() < anchor_cnt) {
            anchors.push_back(r);
        }
        else {
            ui worst_pos = 0;
            ui worst_degree = (ui)(b_pend[anchors[0]] - b_pstart[anchors[0]]);

            for(ui i = 1; i < anchors.size(); ++i) {
                ui d = (ui)(b_pend[anchors[i]] - b_pstart[anchors[i]]);

                if(d > worst_degree) {
                    worst_degree = d;
                    worst_pos = i;
                }
            }

            ui cur_degree = (ui)(b_pend[r] - b_pstart[r]);

            if(cur_degree < worst_degree) {
                anchors[worst_pos] = r;
            }
        }
    }


    touched_left.clear();

    for(ui r : anchors) {
        for(eid p = b_pstart[r]; p < b_pend[r]; ++p) {
            ui x = b_edges[p];

            assert(x < l_n);

            if(used_L[x]) continue;
            if(in_L[x]) continue;

            if(left_cnt[x] == 0) touched_left.push_back(x);
            ++left_cnt[x];
        }
    }

    for(ui x : touched_left) {
        if(left_cnt[x] == anchors.size()) {
            candidates.push_back(x);
        }

        left_cnt[x] = 0;
    }

    if(candidates.empty()) {
        in_L[seed_u] = 0;
        return false;
    }


    auto cmp_left_degree = [&](ui a, ui b) {
        ui da = (ui)(b_pend[a] - b_pstart[a]);
        ui db = (ui)(b_pend[b] - b_pstart[b]);

        if(da != db) return da > db;
        return a < b;
    };

    if(max_candidate_left > 0 && candidates.size() > max_candidate_left) {
        nth_element(candidates.begin(), candidates.begin() + max_candidate_left, candidates.end(), cmp_left_degree);
        candidates.resize(max_candidate_left);
    }

    sort(candidates.begin(), candidates.end(), cmp_left_degree);


    int cur_mark = fast_next_mark(mark_R, mark_token);

    for(ui r : R) mark_R[r] = cur_mark;

    long long cur_gain = fast_biclique_gain((ui)L.size(), (ui)R.size());


    for(ui x : candidates) {
        if(used_L[x]) continue;
        if(in_L[x]) continue;

        ui overlap = 0;

        for(eid p = b_pstart[x]; p < b_pend[x]; ++p) {
            ui r = b_edges[p];

            assert(r >= l_n && r < l_n + r_n);

            if(used_R[r]) continue;

            if(mark_R[r] == cur_mark) {
                ++overlap;
            }
        }

        if(overlap < min_right_size) continue;

        long long new_gain = fast_biclique_gain((ui)L.size() + 1, overlap);


        if(new_gain <= cur_gain) continue;

        new_R.clear();
        new_R.reserve(overlap);

        for(eid p = b_pstart[x]; p < b_pend[x]; ++p) {
            ui r = b_edges[p];

            assert(r >= l_n && r < l_n + r_n);

            if(used_R[r]) continue;

            if(mark_R[r] == cur_mark) {
                new_R.push_back(r);
            }
        }

        R.swap(new_R);

        cur_mark = fast_next_mark(mark_R, mark_token);

        for(ui r : R) mark_R[r] = cur_mark;

        L.push_back(x);
        in_L[x] = 1;

        cur_gain = new_gain;
    }

    if(L.size() < min_left_size || R.size() < min_right_size) {
        for(ui x : L) in_L[x] = 0;
        return false;
    }


    ui rare_r = R[0];
    ui rare_degree = (ui)(b_pend[rare_r] - b_pstart[rare_r]);

    for(ui r : R) {
        ui d = (ui)(b_pend[r] - b_pstart[r]);

        if(d < rare_degree) {
            rare_degree = d;
            rare_r = r;
        }
    }

    for(eid p = b_pstart[rare_r]; p < b_pend[rare_r]; ++p) {
        ui x = b_edges[p];

        assert(x < l_n);

        if(used_L[x]) continue;
        if(in_L[x]) continue;

        ui hit = 0;

        for(eid q = b_pstart[x]; q < b_pend[x]; ++q) {
            ui r = b_edges[q];

            assert(r >= l_n && r < l_n + r_n);

            if(used_R[r]) continue;

            if(mark_R[r] == cur_mark) {
                ++hit;
            }
        }

        if(hit == R.size()) {
            L.push_back(x);
            in_L[x] = 1;
        }
    }

    long long final_gain = fast_biclique_gain((ui)L.size(), (ui)R.size());

    bool ok = true;

    if(L.size() < min_left_size) ok = false;
    if(R.size() < min_right_size) ok = false;
    if(final_gain < min_gain) ok = false;

    if(ok) {
        sort(L.begin(), L.end());
        sort(R.begin(), R.end());

        result.left = L;
        result.right = R;
        result.edge_count = (eid)result.left.size() * (eid)result.right.size();
        result.density = 1.0;
    }

    for(ui x : L) in_L[x] = 0;

    return ok;
}

vector<BiCluster> find_disjoint_maximal_bicliques_fast(ui l_n, ui r_n, eid* b_pstart, eid* b_pend, ui* b_edges, ui min_left_size, ui min_right_size, long long min_gain, ui anchor_cnt = 2, ui max_candidate_left = 256)
{
    vector<BiCluster> bicliques;

    if(l_n == 0 || r_n == 0) return bicliques;

    vector<char> used_L(l_n, 0);
    vector<char> used_R(l_n + r_n, 0);


    vector<ui> left_order;
    left_order.reserve(l_n);

    for(ui u = 0; u < l_n; ++u) {
        ui deg = (ui)(b_pend[u] - b_pstart[u]);

        if(deg >= min_right_size) {
            left_order.push_back(u);
        }
    }

    sort(left_order.begin(), left_order.end(), [&](ui a, ui b) {
        ui da = (ui)(b_pend[a] - b_pstart[a]);
        ui db = (ui)(b_pend[b] - b_pstart[b]);

        if(da != db) return da > db;
        return a < b;
    });


    vector<int> mark_R(l_n + r_n, 0);
    int mark_token = 0;

    vector<char> in_L(l_n, 0);
    vector<ui> left_cnt(l_n, 0);
    vector<ui> touched_left;

    vector<ui> L;
    vector<ui> R;
    vector<ui> new_R;
    vector<ui> anchors;
    vector<ui> candidates;

    touched_left.reserve(1024);
    L.reserve(1024);
    R.reserve(1024);
    new_R.reserve(1024);
    anchors.reserve(anchor_cnt);
    candidates.reserve(max_candidate_left);

    ui tried_seed_cnt = 0;

    for(ui seed_u : left_order) {
        if(used_L[seed_u]) continue;


        ui unused_right_degree = 0;

        for(eid p = b_pstart[seed_u]; p < b_pend[seed_u]; ++p) {
            ui r = b_edges[p];

            assert(r >= l_n && r < l_n + r_n);

            if(!used_R[r]) ++unused_right_degree;
        }

        if(unused_right_degree < min_right_size) continue;

        ++tried_seed_cnt;

        BiCluster cand;

        bool ok = build_one_fast_maximal_biclique_from_seed(seed_u, l_n, r_n, b_pstart, b_pend, b_edges, used_L, used_R, min_left_size, min_right_size, min_gain, anchor_cnt, max_candidate_left, mark_R, mark_token, in_L, left_cnt, touched_left, L, R, new_R, anchors, candidates, cand);

        if(!ok) continue;


        bool conflict = false;

        for(ui u : cand.left) {
            if(used_L[u]) {
                conflict = true;
                break;
            }
        }

        if(!conflict) {
            for(ui r : cand.right) {
                if(used_R[r]) {
                    conflict = true;
                    break;
                }
            }
        }

        if(conflict) continue;

        for(ui u : cand.left) used_L[u] = 1;
        for(ui r : cand.right) used_R[r] = 1;

        bicliques.push_back(move(cand));
    }

    cout << "fast biclique seed tried #: " << tried_seed_cnt
         << ", accepted #: " << bicliques.size() << endl;

#ifdef _CheckInfo_
    vector<char> check_L(l_n, 0);
    vector<char> check_R(l_n + r_n, 0);

    for(const BiCluster& bc : bicliques) {
        assert(bc.left.size() >= min_left_size);
        assert(bc.right.size() >= min_right_size);
        assert(bc.edge_count == (eid)bc.left.size() * (eid)bc.right.size());

        for(ui u : bc.left) {
            assert(u < l_n);
            assert(!check_L[u]);
            check_L[u] = 1;
        }

        for(ui r : bc.right) {
            assert(r >= l_n && r < l_n + r_n);
            assert(!check_R[r]);
            check_R[r] = 1;
        }
    }
#endif

    return bicliques;
}

void build_bc_index(string name, int cfg_tau, int cfg_maxr, ui cfg_min_biclique_size, ui cfg_min_gain, bool be_fast)
{
    Timer t;

    CompressLoopConfig cfg;

    cfg.tau = cfg_tau;
    cfg.max_round = cfg_maxr;


    cfg.min_cluster_size = cfg_min_biclique_size;
    cfg.min_left_size = cfg_min_biclique_size;
    cfg.min_right_size = cfg_min_biclique_size;

    cfg.stop_remain_ratio = 0.01;
    cfg.sparse_avg_degree_stop = 3.5;
    cfg.min_progress_ratio = 0.0001;
    cfg.max_stall_rounds = 2;

    cfg.require_positive_gain = true;
    cfg.min_gain = cfg_min_gain;


    cfg.adaptive_relax = false;

    vector<unordered_map<ui, char>> ver_sim_neis(n);
    eid similar_pair_cnt = obtain_ver_sim_neis(ver_sim_neis);

    ui l_n = n;
    ui r_n = n;
    ui b_n = l_n + r_n;

    eid b_adj_cnt = 4ULL * similar_pair_cnt;

    cout << "l_n: " << l_n
         << ", r_n: " << r_n
         << ", sim_e: " << b_adj_cnt << endl;

    eid* b_pstart = new eid[b_n];
    eid* b_pend = new eid[b_n];
    ui* b_edges = new ui[b_adj_cnt];
    ui* b_degree = new ui[b_n];

    construct_bipartite_graph(ver_sim_neis, b_pstart, b_pend, b_edges, b_degree, l_n, r_n);

    ui original_n = l_n;

    vector<vector<pair<char,ui>>> residual_sim_nei(original_n);
    vector<vector<ui>> z_list(original_n);
    vector<vector<pair<char,ui>>> z_R;

    ui z_idx = 0;

    long long remain_e = b_adj_cnt;
    long long Residual_e = 0;
    long long Z_e = 0;
    long long total_gain = 0;

    ui* l_out_mapping = new ui[l_n];
    ui* r_out_mapping = new ui[r_n];

    for(ui i = 0; i < l_n; ++i) l_out_mapping[i] = i;
    for(ui i = 0; i < r_n; ++i) r_out_mapping[i] = i;

    long long del_e =
        peel_reorg(ver_sim_neis, b_pstart, b_pend, b_edges, b_degree, residual_sim_nei, cfg.tau, l_out_mapping, r_out_mapping, l_n, r_n);

#ifdef _CostlyDebug_
    check_bigraph_correct(b_pstart, b_pend, b_edges, b_degree, l_n, r_n);
#endif

    assert(remain_e >= del_e);

    Residual_e += del_e;
    remain_e -= del_e;

    cout << "1st vr, l_n: " << l_n
         << ", r_n: " << r_n
         << ", remain_e: " << remain_e << endl;

    vector<char> mark_L(2 * original_n, 0);
    vector<char> mark_R(2 * original_n, 0);

    ui min_left_size = cfg.min_left_size;
    ui min_right_size = cfg.min_right_size;

    int round = 0;
    int stall_rounds = 0;

    while(round++ < cfg.max_round) {
        if(remain_e <= 0 || l_n == 0 || r_n == 0) break;

        assert(remain_e % 2 == 0);

        long long remain_logical_edges = remain_e / 2;

        double remain_ratio =
            b_adj_cnt > 0
            ? (double)remain_e / (double)b_adj_cnt
            : 0.0;

        long long min_required_edges =
            (long long)min_left_size * (long long)min_right_size;

        if(remain_ratio <= cfg.stop_remain_ratio) {
            cout << "stop: remaining edge ratio = " << remain_ratio << endl;
            break;
        }

        if(remain_logical_edges < min_required_edges) {
            cout << "stop: too few logical edges, remain = " << remain_logical_edges
                 << ", required = " << min_required_edges << endl;
            break;
        }

        if(l_n < min_left_size || r_n < min_right_size) {
            cout << "stop: too few vertices, l_n = " << l_n
                 << ", r_n = " << r_n << endl;
            break;
        }

        double average_left_degree =
            (double)remain_logical_edges / (double)l_n;

        double average_right_degree =
            (double)remain_logical_edges / (double)r_n;

        double smaller_average_degree =
            min(average_left_degree, average_right_degree);

        if(cfg.sparse_avg_degree_stop > 0 &&
           smaller_average_degree < cfg.sparse_avg_degree_stop) {
            cout << "stop: remaining bigraph is sparse, avgL = "
                 << average_left_degree << ", avgR = "
                 << average_right_degree << endl;
            break;
        }

        cout << endl << "*************** BICLIQUE ROUND "
             << round << " ***************" << endl;

        cout << "l_n: " << l_n
             << ", r_n: " << r_n
             << ", remain adj: " << remain_e
             << ", logical edges: " << remain_logical_edges
             << ", avgL: " << average_left_degree
             << ", avgR: " << average_right_degree << endl;

        cout << "min biclique size: " << min_left_size
             << ", min gain: " << cfg.min_gain << endl;

        long long remain_before_round = remain_e;
        long long round_z_adj = 0;
        long long round_residual_adj = 0;
        long long round_gain = 0;

        ui valid_biclique_cnt = 0;
        ui valid_left_size_sum = 0;
        ui valid_right_size_sum = 0;


        vector<BiCluster> bicliques;
        if(be_fast == true)
            bicliques = find_disjoint_maximal_bicliques_fast(l_n, r_n, b_pstart, b_pend, b_edges, min_left_size, min_right_size, cfg.min_gain, 2, 128);
        else
            bicliques = find_disjoint_maximal_bicliques_heuristic(l_n, r_n, b_pstart, b_pend, b_edges, min_left_size, min_right_size, cfg.min_gain);

        cout << "maximal biclique #: " << bicliques.size() << endl;


        for(const BiCluster& biclique : bicliques) {
            if(biclique.left.size() < min_left_size) continue;
            if(biclique.right.size() < min_right_size) continue;
            if(biclique.edge_count == 0) continue;


            assert(biclique.edge_count == (eid)biclique.left.size() * (eid)biclique.right.size());

            long long gain =
                (long long)biclique.edge_count
                - (long long)biclique.left.size()
                - (long long)biclique.right.size();

            if(cfg.require_positive_gain && gain < cfg.min_gain) continue;

            vector<ui> original_L;
            vector<ui> original_R;

            original_L.reserve(biclique.left.size());
            original_R.reserve(biclique.right.size());

            for(ui u : biclique.left) {
                assert(u < l_n);
                original_L.push_back(l_out_mapping[u]);
            }

            for(ui r : biclique.right) {
                assert(r >= l_n && r < l_n + r_n);

                ui right_local_id = r - l_n;
                original_R.push_back(r_out_mapping[right_local_id]);
            }


            long long removed_adj =
                remove_edges_in_bicluster(biclique, b_pstart, b_pend, b_edges, b_degree, mark_L, mark_R);

            long long expected_removed_adj =
                2LL * biclique.edge_count;

            if(removed_adj != expected_removed_adj) {
                cout << "Error: removed adjacency count is incorrect!" << endl;
                cout << "removed_adj: " << removed_adj
                     << ", expected: " << expected_removed_adj
                     << ", L size: " << biclique.left.size()
                     << ", R size: " << biclique.right.size()
                     << ", edge_count: " << biclique.edge_count << endl;
                exit(1);
            }

            build_index(original_L, original_R, z_list, ver_sim_neis, z_R, z_idx);

            assert(remain_e >= removed_adj);

            remain_e -= removed_adj;
            Z_e += removed_adj;
            round_z_adj += removed_adj;
            round_gain += gain;
            total_gain += gain;

            ++valid_biclique_cnt;
            valid_left_size_sum += biclique.left.size();
            valid_right_size_sum += biclique.right.size();
        }

        long long shrink_del_adj =
            peel_reorg(ver_sim_neis, b_pstart, b_pend, b_edges, b_degree, residual_sim_nei, cfg.tau, l_out_mapping, r_out_mapping, l_n, r_n);

        assert(remain_e >= shrink_del_adj);

        remain_e -= shrink_del_adj;
        Residual_e += shrink_del_adj;
        round_residual_adj += shrink_del_adj;

        long long deleted_this_round =
            remain_before_round - remain_e;

        double progress_ratio =
            remain_before_round > 0
            ? (double)deleted_this_round / (double)remain_before_round
            : 0.0;

        cout << "==round result==" << endl;
        cout << "\tvalid biclique #: " << valid_biclique_cnt << endl;

        if(valid_biclique_cnt > 0) {
            cout << "\tAVE. left size: "
                 << valid_left_size_sum / valid_biclique_cnt << endl;

            cout << "\tAVE. right size: "
                 << valid_right_size_sum / valid_biclique_cnt << endl;
        }

        cout << "\tZ removed adj: " << round_z_adj
             << ", residual removed adj: " << round_residual_adj
             << ", total removed adj: " << deleted_this_round
             << ", gain: " << round_gain
             << ", remain adj: " << remain_e
             << ", progress: " << progress_ratio << endl;

#ifdef _CheckInfo_
        long long check_adj_cnt = 0;

        for(ui u = 0; u < l_n + r_n; ++u) {
            check_adj_cnt += b_pend[u] - b_pstart[u];
        }

        if(check_adj_cnt != remain_e) {
            cout << "check_adj_cnt = " << check_adj_cnt
                 << ", remain_e = " << remain_e << endl;
            exit(1);
        }
#endif

        bool stalled =
            valid_biclique_cnt == 0 ||
            progress_ratio < cfg.min_progress_ratio;

        if(stalled) ++stall_rounds;
        else stall_rounds = 0;

        if(stall_rounds >= cfg.max_stall_rounds) {
            cout << "stop: too little progress for "
                 << stall_rounds << " consecutive rounds." << endl;
            break;
        }
    }


    if(remain_e > 0) {
        assert(remain_e % 2 == 0);

        final_bigraph_to_residual(ver_sim_neis, b_pstart, b_pend, b_edges, residual_sim_nei, l_out_mapping, r_out_mapping, l_n, r_n);

        Residual_e += remain_e;
        remain_e = 0;
    }

    assert(remain_e == 0);
    assert(Z_e + Residual_e == (long long)b_adj_cnt);

    for(ui i = 0; i < original_n; ++i) {
        sort(residual_sim_nei[i].begin(), residual_sim_nei[i].end(), [](const pair<char,ui>& a, const pair<char,ui>& b) {
            if(a.first != b.first) return a.first > b.first;
            return a.second < b.second;
        });
    }

    delete [] b_pstart;
    delete [] b_pend;
    delete [] b_edges;
    delete [] b_degree;
    delete [] l_out_mapping;
    delete [] r_out_mapping;

    cout << "*************** BICLIQUE INDEX INFO ***************" << endl;
    cout << "z_idx: " << z_idx << endl;

    double z_ratio =
        b_adj_cnt > 0
        ? (double)Z_e / (double)b_adj_cnt
        : 0.0;

    double residual_ratio =
        b_adj_cnt > 0
        ? (double)Residual_e / (double)b_adj_cnt
        : 0.0;

    cout << (int)(z_ratio * 100) << "% edges in Z" << endl;
    cout << (int)(residual_ratio * 100) << "% edges in Residual" << endl;

    long long original_logical_edges = b_adj_cnt / 2;

    double saving_ratio =
        original_logical_edges > 0
        ? (double)total_gain / (double)original_logical_edges
        : 0.0;

    double compressed_ratio =
        1.0 - saving_ratio;

    cout << "estimated saving ratio: "
         << saving_ratio * 100 << "%" << endl;

    cout << "estimated compressed/original ratio: "
         << compressed_ratio * 100 << "%" << endl;

    string out_dir = "./index";
    std::filesystem::create_directory(out_dir);

    string config_name =
        "tau" + to_string(cfg.tau)
        + "_maxr" + to_string(cfg.max_round)
        + "_mc" + to_string(cfg_min_biclique_size)
        + "_mg" + to_string(cfg_min_gain);

    string file_a =
        out_dir + "/" + name + "_" + config_name + "_BCa.bin";

    string file_b =
        out_dir + "/" + name + "_" + config_name + "_BCb.bin";

    FILE* f = Utility::open_file(file_a.c_str(), "wb");

    fwrite(&original_n, sizeof(ui), 1, f);

    for(ui u = 0; u < original_n; ++u) {
        const auto& tmpvec = residual_sim_nei[u];

        ui num = (ui)tmpvec.size();
        fwrite(&num, sizeof(ui), 1, f);

        for(const auto& eachpair : tmpvec) {
            fwrite(&eachpair.first, sizeof(char), 1, f);
            fwrite(&eachpair.second, sizeof(ui), 1, f);
        }

        const auto& zvec = z_list[u];

        num = (ui)zvec.size();
        fwrite(&num, sizeof(ui), 1, f);

        for(ui z : zvec) {
            fwrite(&z, sizeof(ui), 1, f);
        }
    }

    fclose(f);

    f = Utility::open_file(file_b.c_str(), "wb");

    fwrite(&z_idx, sizeof(ui), 1, f);

    if(z_R.size() != z_idx) {
        cout << "z_R.size() != z_idx" << endl;
        exit(1);
    }

    for(const auto& eachzr : z_R) {
        ui num = (ui)eachzr.size();
        fwrite(&num, sizeof(ui), 1, f);

        for(const auto& eachpair : eachzr) {
            fwrite(&eachpair.first, sizeof(char), 1, f);
            fwrite(&eachpair.second, sizeof(ui), 1, f);
        }
    }

    fclose(f);

    cout << "finish writing biclique BCa.bin and BCb.bin to disk." << endl;
}

void obtain_one_vertex_sim_neis(ui u, vector<pair<ui,char>>& sim_neis, ui* vis, ui* comnei_cnt)
{
    sim_neis.clear();


    vector<ui> u_nei;
    for(eid i = pstart[u]; i < pstart[u+1]; ++i) {
        u_nei.push_back(edges[i]);
        assert(vis[edges[i]] == 0);
        vis[edges[i]] = 1;
    }
    vector<ui> u_2hopnei;
    for(auto e : u_nei) {
        for(eid i = pstart[e]; i < pstart[e+1]; ++i) {
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
        char char_s = sim_score * 100;
        if(comnei_cnt[e] >= ComNeiThre ) sim_neis.push_back({e, char_s});
    }

    for(auto e : u_nei) {
        assert(vis[e] == 1);
        vis[e] = 0;
    }
    for(auto e : u_2hopnei) {
        comnei_cnt[e] = 0;
        assert(vis[e] == 2);
        vis[e] = 0;
    }

}

ui obtain_ver_sim_neis_batch(ui batch_start, ui original_n, eid edge_budget, vector<vector<pair<ui,char>>>& batch_sim_neis, eid& directed_edge_cnt, ui* vis, ui* comnei_cnt)
{
    assert(batch_start < original_n);
    assert(edge_budget > 0);

    batch_sim_neis.clear();
    directed_edge_cnt = 0;

    ui u = batch_start;

    while(u < original_n) {
        vector<pair<ui,char>> one_vertex_sim_neis;
        obtain_one_vertex_sim_neis(u, one_vertex_sim_neis, vis, comnei_cnt);

#ifdef _CheckInfo_
        unordered_set<ui> check_duplicate;

        for(const auto& e : one_vertex_sim_neis) {
            assert(e.first < original_n);
            assert(e.first != u);
            assert(check_duplicate.insert(e.first).second);
        }
#endif

        eid degree_u = (eid)one_vertex_sim_neis.size();


        if(!batch_sim_neis.empty() && (degree_u > edge_budget || directed_edge_cnt > edge_budget - degree_u) ) {
            break;
        }


        if(batch_sim_neis.empty() && degree_u > edge_budget) {
            cout << "Warning: vertex " << u
                 << " has " << degree_u
                 << " similar neighbors, exceeding batch budget "
                 << edge_budget << endl;
        }

        assert(directed_edge_cnt <= numeric_limits<eid>::max() - degree_u);

        directed_edge_cnt += degree_u;
        batch_sim_neis.push_back(move(one_vertex_sim_neis));

        ++u;
    }

    assert(u > batch_start);

    return u;
}

void build_batch_right_mapping(const vector<vector<pair<ui,char>>>& batch_sim_neis, vector<ui>& right_local_id, vector<ui>& touched_right, vector<ui>& r_out_mapping)
{
    touched_right.clear();
    r_out_mapping.clear();

    for(const auto& sim_list : batch_sim_neis) {
        for(const auto& e : sim_list) {
            ui original_v = e.first;

            assert(original_v < right_local_id.size());

            if(right_local_id[original_v] == INVALID_UI) {
                ui local_id = (ui)r_out_mapping.size();

                right_local_id[original_v] = local_id;
                r_out_mapping.push_back(original_v);
                touched_right.push_back(original_v);
            }
        }
    }
}

void clear_batch_right_mapping(vector<ui>& right_local_id, const vector<ui>& touched_right)
{
    for(ui original_v : touched_right) {
        right_local_id[original_v] = INVALID_UI;
    }
}

void construct_batch_bipartite_graph(const vector<vector<pair<ui,char>>>& batch_sim_neis, const vector<ui>& right_local_id, eid*& b_pstart, eid*& b_pend, ui*& b_edges, char*& b_score, ui*& b_degree, ui l_n, ui r_n, eid directed_edge_cnt)
{
    ui b_n = l_n + r_n;
    eid b_adj_cnt = 2ULL * directed_edge_cnt;

    b_pstart = b_n > 0 ? new eid[b_n] : nullptr;
    b_pend = b_n > 0 ? new eid[b_n] : nullptr;
    b_degree = b_n > 0 ? new ui[b_n] : nullptr;

    b_edges = b_adj_cnt > 0 ? new ui[b_adj_cnt] : nullptr;
    b_score = b_adj_cnt > 0 ? new char[b_adj_cnt] : nullptr;

    for(ui u = 0; u < b_n; ++u) {
        b_degree[u] = 0;
    }


    for(ui local_u = 0; local_u < l_n; ++local_u) {
        for(const auto& e : batch_sim_neis[local_u]) {
            ui original_v = e.first;
            ui local_r = right_local_id[original_v];

            assert(local_r != INVALID_UI);
            assert(local_r < r_n);

            ui right_global_id = l_n + local_r;

            ++b_degree[local_u];
            ++b_degree[right_global_id];
        }
    }


    eid pos = 0;

    for(ui u = 0; u < b_n; ++u) {
        b_pstart[u] = pos;
        b_pend[u] = pos;
        pos += b_degree[u];
    }

    assert(pos == b_adj_cnt);


    for(ui local_u = 0; local_u < l_n; ++local_u) {
        for(const auto& e : batch_sim_neis[local_u]) {
            ui original_v = e.first;
            char similarity = e.second;

            ui local_r = right_local_id[original_v];
            ui right_global_id = l_n + local_r;

            eid p1 = b_pend[local_u]++;
            b_edges[p1] = right_global_id;
            b_score[p1] = similarity;

            eid p2 = b_pend[right_global_id]++;
            b_edges[p2] = local_u;
            b_score[p2] = similarity;
        }
    }

    for(ui u = 0; u < b_n; ++u) {
        assert(b_pend[u] - b_pstart[u] == b_degree[u]);
    }
}

void write_batch_vertex_index(FILE* file_a, vector<vector<pair<char,ui>>>& batch_residual, const vector<vector<ui>>& batch_z_list)
{
    assert(batch_residual.size() == batch_z_list.size());

    for(ui local_u = 0; local_u < batch_residual.size(); ++local_u) {
        auto& residual = batch_residual[local_u];

        sort(residual.begin(), residual.end(), [](const pair<char,ui>& a, const pair<char,ui>& b) {
            if(a.first != b.first) return a.first > b.first;
            return a.second < b.second;
        });

        ui num = (ui)residual.size();
        fwrite(&num, sizeof(ui), 1, file_a);

        for(const auto& e : residual) {
            fwrite(&e.first, sizeof(char), 1, file_a);
            fwrite(&e.second, sizeof(ui), 1, file_a);
        }

        const auto& zvec = batch_z_list[local_u];

        num = (ui)zvec.size();
        fwrite(&num, sizeof(ui), 1, file_a);

        for(ui zid : zvec) {
            fwrite(&zid, sizeof(ui), 1, file_a);
        }
    }
}

eid peel_reorg_batch_left_only(eid*& b_pstart, eid*& b_pend, ui*& b_edges, char*& b_score, ui*& b_degree, vector<vector<pair<char,ui>>>& batch_residual, int tau, ui* l_out_mapping, ui* r_out_mapping, ui batch_start, ui batch_vertex_cnt, ui& l_n, ui& r_n)
{
    ui old_l_n = l_n;
    ui old_r_n = r_n;
    ui old_b_n = old_l_n + old_r_n;

    eid old_adj_cnt = 0;

    for(ui u = 0; u < old_b_n; ++u) {
        old_adj_cnt += b_pend[u] - b_pstart[u];
    }

    vector<char> delete_left(old_l_n, 0);
    vector<ui> live_right_degree(old_r_n, 0);

    eid deleted_logical_edges = 0;
    eid surviving_logical_edges = 0;


    for(ui u = 0; u < old_l_n; ++u) {
        if((int)b_degree[u] < tau) {
            delete_left[u] = 1;
        }
    }


    for(ui u = 0; u < old_l_n; ++u) {
        ui original_u = l_out_mapping[u];

        assert(original_u >= batch_start);
        assert(original_u < batch_start + batch_vertex_cnt);

        ui batch_local_u = original_u - batch_start;

        if(delete_left[u]) {
            for(eid p = b_pstart[u]; p < b_pend[u]; ++p) {
                ui right_global_id = b_edges[p];

                assert(right_global_id >= old_l_n);
                assert(right_global_id < old_l_n + old_r_n);

                ui old_right_local_id = right_global_id - old_l_n;
                ui original_v = r_out_mapping[old_right_local_id];

                batch_residual[batch_local_u].push_back(
                    make_pair(b_score[p], original_v)
                );

                ++deleted_logical_edges;
            }
        }
        else {
            for(eid p = b_pstart[u]; p < b_pend[u]; ++p) {
                ui right_global_id = b_edges[p];
                ui old_right_local_id = right_global_id - old_l_n;

                ++live_right_degree[old_right_local_id];
                ++surviving_logical_edges;
            }
        }
    }

    vector<ui> new_left_id(old_l_n, INVALID_UI);
    vector<ui> new_right_id(old_r_n, INVALID_UI);

    ui new_l_n = 0;
    ui new_r_n = 0;

    for(ui u = 0; u < old_l_n; ++u) {
        if(!delete_left[u]) {
            new_left_id[u] = new_l_n++;
        }
    }

    for(ui r = 0; r < old_r_n; ++r) {
        if(live_right_degree[r] > 0) {
            new_right_id[r] = new_r_n++;
        }
    }


    if(new_l_n == old_l_n && new_r_n == old_r_n) {
        assert(deleted_logical_edges == 0);
        return 0;
    }

    ui new_b_n = new_l_n + new_r_n;
    eid new_adj_cnt = 2ULL * surviving_logical_edges;

    eid* new_pstart = new_b_n > 0 ? new eid[new_b_n] : nullptr;
    eid* new_pend = new_b_n > 0 ? new eid[new_b_n] : nullptr;
    ui* new_degree = new_b_n > 0 ? new ui[new_b_n] : nullptr;

    ui* new_edges = new_adj_cnt > 0 ? new ui[new_adj_cnt] : nullptr;
    char* new_score = new_adj_cnt > 0 ? new char[new_adj_cnt] : nullptr;

    for(ui u = 0; u < new_b_n; ++u) {
        new_degree[u] = 0;
    }


    for(ui old_u = 0; old_u < old_l_n; ++old_u) {
        if(delete_left[old_u]) continue;

        ui new_u = new_left_id[old_u];

        for(eid p = b_pstart[old_u]; p < b_pend[old_u]; ++p) {
            ui old_right_global_id = b_edges[p];
            ui old_right_local_id = old_right_global_id - old_l_n;

            ui new_r = new_right_id[old_right_local_id];

            assert(new_r != INVALID_UI);

            ui new_right_global_id = new_l_n + new_r;

            ++new_degree[new_u];
            ++new_degree[new_right_global_id];
        }
    }

    eid position = 0;

    for(ui u = 0; u < new_b_n; ++u) {
        new_pstart[u] = position;
        new_pend[u] = position;
        position += new_degree[u];
    }

    assert(position == new_adj_cnt);


    for(ui old_u = 0; old_u < old_l_n; ++old_u) {
        if(delete_left[old_u]) continue;

        ui new_u = new_left_id[old_u];

        for(eid p = b_pstart[old_u]; p < b_pend[old_u]; ++p) {
            ui old_right_global_id = b_edges[p];
            ui old_right_local_id = old_right_global_id - old_l_n;

            ui new_r = new_right_id[old_right_local_id];
            ui new_right_global_id = new_l_n + new_r;

            eid p1 = new_pend[new_u]++;
            new_edges[p1] = new_right_global_id;
            new_score[p1] = b_score[p];

            eid p2 = new_pend[new_right_global_id]++;
            new_edges[p2] = new_u;
            new_score[p2] = b_score[p];
        }
    }

    for(ui u = 0; u < new_b_n; ++u) {
        assert(new_pend[u] - new_pstart[u] == new_degree[u]);
    }


    for(ui old_u = 0; old_u < old_l_n; ++old_u) {
        if(!delete_left[old_u]) {
            ui new_u = new_left_id[old_u];
            l_out_mapping[new_u] = l_out_mapping[old_u];
        }
    }

    for(ui old_r = 0; old_r < old_r_n; ++old_r) {
        if(new_right_id[old_r] != INVALID_UI) {
            ui new_r = new_right_id[old_r];
            r_out_mapping[new_r] = r_out_mapping[old_r];
        }
    }

    delete [] b_pstart;
    delete [] b_pend;
    delete [] b_edges;
    delete [] b_score;
    delete [] b_degree;

    b_pstart = new_pstart;
    b_pend = new_pend;
    b_edges = new_edges;
    b_score = new_score;
    b_degree = new_degree;

    l_n = new_l_n;
    r_n = new_r_n;

    eid deleted_adj_cnt = 2ULL * deleted_logical_edges;

    if(old_adj_cnt != new_adj_cnt + deleted_adj_cnt) {
        cout << "Error: batch peel edge accounting mismatch!" << endl;
        cout << "old adj: " << old_adj_cnt
             << ", new adj: " << new_adj_cnt
             << ", deleted adj: " << deleted_adj_cnt << endl;
        exit(1);
    }

    return deleted_adj_cnt;
}

vector<pair<char,ui>> prepare_z_right_entries(const BiCluster& bicluster, eid* b_pstart, eid* b_pend, ui* b_edges, char* b_score, ui* r_out_mapping, ui l_n, ui r_n, vector<int>& right_position)
{
    vector<char> max_score(bicluster.right.size(), 0);
    vector<char> visited(bicluster.right.size(), 0);

    for(ui i = 0; i < bicluster.right.size(); ++i) {
        ui right_global_id = bicluster.right[i];

        assert(right_global_id >= l_n);
        assert(right_global_id < l_n + r_n);

        ui right_local_id = right_global_id - l_n;

        assert(right_position[right_local_id] == -1);
        right_position[right_local_id] = (int)i;
    }

    eid counted_edges = 0;

    for(ui u : bicluster.left) {
        assert(u < l_n);

        for(eid p = b_pstart[u]; p < b_pend[u]; ++p) {
            ui right_global_id = b_edges[p];
            ui right_local_id = right_global_id - l_n;

            int position = right_position[right_local_id];

            if(position == -1) continue;

            if(!visited[position] || b_score[p] > max_score[position]) {
                max_score[position] = b_score[p];
                visited[position] = 1;
            }

            ++counted_edges;
        }
    }

    if(counted_edges != bicluster.edge_count) {
        cout << "Error: prepare Z edge count mismatch!" << endl;
        cout << "counted: " << counted_edges
             << ", expected: " << bicluster.edge_count << endl;
        exit(1);
    }

    vector<pair<char,ui>> z_entries;
    z_entries.reserve(bicluster.right.size());

    for(ui i = 0; i < bicluster.right.size(); ++i) {
        if(!visited[i]) {
            cout << "Error: a right vertex in bicluster has no internal edge." << endl;
            exit(1);
        }

        ui right_global_id = bicluster.right[i];
        ui right_local_id = right_global_id - l_n;
        ui original_v = r_out_mapping[right_local_id];

        z_entries.push_back(make_pair(max_score[i], original_v));

        right_position[right_local_id] = -1;
    }

    sort(z_entries.begin(), z_entries.end(), [](const pair<char,ui>& a, const pair<char,ui>& b) {
        if(a.first != b.first) return a.first > b.first;
        return a.second < b.second;
    });

    return z_entries;
}

void commit_z_to_index(const BiCluster& bicluster, const vector<pair<char,ui>>& z_entries, vector<vector<ui>>& batch_z_list, FILE* file_b, ui* l_out_mapping, ui batch_start, ui batch_vertex_cnt, ui& z_idx)
{
    for(ui current_u : bicluster.left) {
        ui original_u = l_out_mapping[current_u];

        assert(original_u >= batch_start);
        assert(original_u < batch_start + batch_vertex_cnt);

        ui batch_local_u = original_u - batch_start;
        batch_z_list[batch_local_u].push_back(z_idx);
    }

    ui num = (ui)z_entries.size();
    fwrite(&num, sizeof(ui), 1, file_b);

    for(const auto& e : z_entries) {
        fwrite(&e.first, sizeof(char), 1, file_b);
        fwrite(&e.second, sizeof(ui), 1, file_b);
    }

    ++z_idx;
}

eid remove_edges_in_bicluster_batch(const BiCluster& bicluster, eid* b_pstart, eid* b_pend, ui* b_edges, char* b_score, ui* b_degree, vector<char>& mark_L, vector<char>& mark_R)
{
    for(ui u : bicluster.left) {
        assert(u < mark_L.size());
        mark_L[u] = 1;
    }

    for(ui r : bicluster.right) {
        assert(r < mark_R.size());
        mark_R[r] = 1;
    }

    eid removed_adj_cnt = 0;


    for(ui u : bicluster.left) {
        eid write_pos = b_pstart[u];

        for(eid p = b_pstart[u]; p < b_pend[u]; ++p) {
            ui v = b_edges[p];

            if(mark_R[v]) {
                ++removed_adj_cnt;
            }
            else {
                b_edges[write_pos] = b_edges[p];
                b_score[write_pos] = b_score[p];
                ++write_pos;
            }
        }

        b_pend[u] = write_pos;
        b_degree[u] = (ui)(b_pend[u] - b_pstart[u]);
    }


    for(ui r : bicluster.right) {
        eid write_pos = b_pstart[r];

        for(eid p = b_pstart[r]; p < b_pend[r]; ++p) {
            ui v = b_edges[p];

            if(mark_L[v]) {
                ++removed_adj_cnt;
            }
            else {
                b_edges[write_pos] = b_edges[p];
                b_score[write_pos] = b_score[p];
                ++write_pos;
            }
        }

        b_pend[r] = write_pos;
        b_degree[r] = (ui)(b_pend[r] - b_pstart[r]);
    }

    for(ui u : bicluster.left) mark_L[u] = 0;
    for(ui r : bicluster.right) mark_R[r] = 0;

    assert(removed_adj_cnt % 2 == 0);

    return removed_adj_cnt;
}

eid final_bigraph_to_residual_batch(eid* b_pstart, eid* b_pend, ui* b_edges, char* b_score, vector<vector<pair<char,ui>>>& batch_residual, ui* l_out_mapping, ui* r_out_mapping, ui batch_start, ui batch_vertex_cnt, ui l_n, ui r_n)
{
    eid logical_edge_cnt = 0;

    for(ui u = 0; u < l_n; ++u) {
        ui original_u = l_out_mapping[u];

        assert(original_u >= batch_start);
        assert(original_u < batch_start + batch_vertex_cnt);

        ui batch_local_u = original_u - batch_start;

        for(eid p = b_pstart[u]; p < b_pend[u]; ++p) {
            ui right_global_id = b_edges[p];

            assert(right_global_id >= l_n);
            assert(right_global_id < l_n + r_n);

            ui right_local_id = right_global_id - l_n;
            ui original_v = r_out_mapping[right_local_id];

            batch_residual[batch_local_u].push_back(
                make_pair(b_score[p], original_v)
            );

            ++logical_edge_cnt;
        }
    }

    return 2ULL * logical_edge_cnt;
}

void compress_one_batch(const CompressLoopConfig& cfg, ui batch_start, ui batch_vertex_cnt, eid*& b_pstart, eid*& b_pend, ui*& b_edges, char*& b_score, ui*& b_degree, ui* l_out_mapping, ui* r_out_mapping, ui& l_n, ui& r_n, vector<vector<pair<char,ui>>>& batch_residual, vector<vector<ui>>& batch_z_list, FILE* file_b, ui& z_idx, eid batch_b_adj_cnt, eid& batch_Z_e, eid& batch_Residual_e, long long& batch_gain)
{
    batch_Z_e = 0;
    batch_Residual_e = 0;
    batch_gain = 0;

    eid remain_e = batch_b_adj_cnt;

    ui initial_l_n = l_n;
    ui initial_r_n = r_n;


    eid del_e = peel_reorg_batch_left_only(b_pstart, b_pend, b_edges, b_score, b_degree, batch_residual, cfg.tau, l_out_mapping, r_out_mapping, batch_start, batch_vertex_cnt, l_n, r_n);

    assert(remain_e >= del_e);

    remain_e -= del_e;
    batch_Residual_e += del_e;

    vector<char> mark_L(initial_l_n, 0);
    vector<char> mark_R(initial_l_n + initial_r_n, 0);
    vector<int> right_position(initial_r_n, -1);

    ui k = cfg.k;
    ui bands = cfg.bands;
    double threshold = cfg.threshold;
    ui min_cluster_size = cfg.min_cluster_size;

    double rho = cfg.rho;
    ui min_left_size = cfg.min_left_size;
    ui min_right_size = cfg.min_right_size;

    int round = 0;
    int stall_rounds = 0;

    while(round++ < cfg.max_round) {
        if(remain_e == 0 || l_n == 0 || r_n == 0) break;

        assert(remain_e % 2 == 0);

        eid remain_logical_edges = remain_e / 2;
        double remain_ratio = (double)remain_e / (double)batch_b_adj_cnt;

        eid min_required_edges = (eid)ceil(rho * min_left_size * min_right_size);

        if(remain_ratio <= cfg.stop_remain_ratio) break;
        if(remain_logical_edges < min_required_edges) break;
        if(l_n < min_left_size || r_n < min_right_size) break;

        double average_left_degree =
            (double)remain_logical_edges / (double)l_n;

        double average_right_degree =
            (double)remain_logical_edges / (double)r_n;

        double smaller_average_degree =
            min(average_left_degree, average_right_degree);

        if(cfg.sparse_avg_degree_stop > 0 &&
           smaller_average_degree < cfg.sparse_avg_degree_stop) {
            break;
        }

        cout << "\tROUND " << round
             << ", l_n: " << l_n
             << ", r_n: " << r_n
             << ", logical edges: " << remain_logical_edges
             << ", k: " << k << ", bands: " << bands << ", threshold: " << threshold
             << ", min cluster size: " << min_cluster_size << ", rho: " << rho << endl;

        eid remain_before_round = remain_e;
        eid round_z_adj = 0;
        eid round_residual_adj = 0;

        ui valid_bicluster_cnt = 0;

        vector<vector<ui>> clusters =
            minhash_lsh_cluster_left(
                l_n, r_n,
                b_pstart, b_pend, b_edges,
                k, bands,
                threshold,
                min_cluster_size
            );

        vector<BiCluster> biclusters =
            build_disjoint_biclusters(
                clusters,
                l_n, r_n,
                b_pstart, b_pend, b_edges,
                rho,
                min_left_size,
                min_right_size
            );

#ifdef _CheckInfo_
        check_biclusters_disjoint(biclusters, l_n, r_n);
#endif

        for(const BiCluster& bicluster : biclusters) {
            if(bicluster.left.size() < min_left_size) continue;
            if(bicluster.right.size() < min_right_size) continue;
            if(bicluster.edge_count == 0) continue;

            long long gain =
                (long long)bicluster.edge_count -
                (long long)bicluster.left.size() -
                (long long)bicluster.right.size();

            if(cfg.require_positive_gain && gain < cfg.min_gain) {
                continue;
            }


            vector<pair<char,ui>> z_entries =
                prepare_z_right_entries(
                    bicluster,
                    b_pstart, b_pend,
                    b_edges, b_score,
                    r_out_mapping,
                    l_n, r_n,
                    right_position
                );

            eid removed_adj =
                remove_edges_in_bicluster_batch(
                    bicluster,
                    b_pstart, b_pend,
                    b_edges, b_score,
                    b_degree,
                    mark_L, mark_R
                );

            eid expected_removed_adj =
                2ULL * bicluster.edge_count;

            if(removed_adj != expected_removed_adj) {
                cout << "Error: removed adjacency mismatch!" << endl;
                cout << "removed: " << removed_adj
                     << ", expected: " << expected_removed_adj << endl;
                exit(1);
            }


            commit_z_to_index(
                bicluster,
                z_entries,
                batch_z_list,
                file_b,
                l_out_mapping,
                batch_start,
                batch_vertex_cnt,
                z_idx
            );

            assert(remain_e >= removed_adj);

            remain_e -= removed_adj;
            batch_Z_e += removed_adj;
            round_z_adj += removed_adj;
            batch_gain += gain;

            ++valid_bicluster_cnt;
        }

        eid shrink_del_adj =
            peel_reorg_batch_left_only(
                b_pstart, b_pend,
                b_edges, b_score,
                b_degree,
                batch_residual,
                cfg.tau,
                l_out_mapping,
                r_out_mapping,
                batch_start,
                batch_vertex_cnt,
                l_n, r_n
            );

        assert(remain_e >= shrink_del_adj);

        remain_e -= shrink_del_adj;
        batch_Residual_e += shrink_del_adj;
        round_residual_adj += shrink_del_adj;

        eid deleted_this_round =
            remain_before_round - remain_e;

        double progress_ratio =
            remain_before_round > 0
            ? (double)deleted_this_round / remain_before_round
            : 0.0;

        cout << "\t\tresult: Z adj=" << round_z_adj
             << ", residual adj=" << round_residual_adj
             << ", remain adj=" << remain_e
             << ", progress=" << progress_ratio << endl;


        bool stalled =
            progress_ratio < cfg.min_progress_ratio;

        if(stalled) {
            ++stall_rounds;

            if(cfg.adaptive_relax &&
               stall_rounds < cfg.max_stall_rounds) {
                threshold =
                    max(cfg.min_threshold, threshold * 0.80);

                rho =
                    max(cfg.min_rho, rho * 0.80);

                min_cluster_size =
                    max(min_left_size,
                        (ui)ceil(min_cluster_size * 0.80));

                if(bands * 2 <= k &&
                   k % (bands * 2) == 0) {
                    bands *= 2;
                }
            }
        }
        else {
            stall_rounds = 0;
        }

        if(stall_rounds >= cfg.max_stall_rounds) {
            break;
        }
    }


    if(remain_e > 0) {
        eid final_adj =
            final_bigraph_to_residual_batch(
                b_pstart, b_pend,
                b_edges, b_score,
                batch_residual,
                l_out_mapping,
                r_out_mapping,
                batch_start,
                batch_vertex_cnt,
                l_n, r_n
            );

        if(final_adj != remain_e) {
            cout << "Error: final residual edge count mismatch!" << endl;
            cout << "final_adj: " << final_adj
                 << ", remain_e: " << remain_e << endl;
            exit(1);
        }

        batch_Residual_e += final_adj;
        remain_e = 0;
    }

    assert(batch_Z_e + batch_Residual_e == batch_b_adj_cnt);
}

void build_db_index_memory_bounded(string name, int cfg_tau, int cfg_maxr, ui cfg_k, ui cfg_bands, double cfg_threshold, double cfg_rho, ui cfg_min_cluster_size, ui cfg_min_gain)
{
    assert(n < std::numeric_limits<ui>::max());

    Timer t;

    CompressLoopConfig cfg;

    cfg.tau = cfg_tau;
    cfg.max_round = cfg_maxr;

    cfg.k = cfg_k;
    cfg.bands = cfg_bands;

    cfg.threshold = cfg_threshold;
    cfg.rho = cfg_rho;

    cfg.min_cluster_size = cfg_min_cluster_size;
    cfg.min_left_size = cfg.min_cluster_size;
    cfg.min_right_size = cfg.min_cluster_size;

    cfg.stop_remain_ratio = 0.01;
    cfg.sparse_avg_degree_stop = 3.5;
    cfg.min_progress_ratio = 0.002;
    cfg.max_stall_rounds = 2;

    cfg.require_positive_gain = true;
    cfg.min_gain = cfg_min_gain;

    cfg.adaptive_relax = true;
    cfg.min_threshold = cfg.threshold / 10.0;
    cfg.min_rho = cfg.rho / 10.0;

    assert(cfg.k > 0);
    assert(cfg.bands > 0);
    assert(cfg.k % cfg.bands == 0);

    ui original_n = n;


    eid batch_directed_edge_budget = 300000ULL;

    string out_dir = "./index";
    std::filesystem::create_directories(out_dir);

    string config_name = build_config_name(cfg);
    string file_a_name = out_dir + "/" + name + "_" + config_name + "_DBBatcha.bin";
    string file_b_name = out_dir + "/" + name + "_" + config_name + "_DBBatchb.bin";
    FILE* file_a = Utility::open_file(file_a_name.c_str(), "wb");
    FILE* file_b = Utility::open_file(file_b_name.c_str(), "wb");


    fwrite(&original_n, sizeof(ui), 1, file_a);


    ui z_idx = 0;
    fwrite(&z_idx, sizeof(ui), 1, file_b);


    vector<ui> right_local_id(original_n, INVALID_UI);
    vector<ui> touched_right;

    eid total_physical_adj = 0;
    eid total_Z_e = 0;
    eid total_Residual_e = 0;
    long long total_gain = 0;

    ui batch_start = 0;
    ui batch_id = 0;

    ui * vis = new ui[original_n];
    memset(vis, 0, sizeof(ui)*original_n);
    ui * comnei_cnt = new ui[original_n];
    memset(comnei_cnt, 0, sizeof(ui)*original_n);

    while(batch_start < original_n) {
        ++batch_id;

        cout << endl;
        cout << "========================================" << endl;
        cout << "BUILD BATCH " << batch_id << ", start vertex: " << batch_start << endl;

        vector<vector<pair<ui,char>>> batch_sim_neis;
        eid directed_edge_cnt = 0;

        ui batch_end = obtain_ver_sim_neis_batch(batch_start, original_n, batch_directed_edge_budget, batch_sim_neis, directed_edge_cnt, vis, comnei_cnt);

        ui batch_vertex_cnt = batch_end - batch_start;

        assert(batch_vertex_cnt == batch_sim_neis.size());

        cout << "batch vertex range: [" << batch_start << ", " << batch_end << ")" << endl;
        cout << "batch left vertices: " << batch_vertex_cnt << ", directed similar edges: " << directed_edge_cnt << endl;

        vector<ui> r_out_mapping;


        build_batch_right_mapping(batch_sim_neis, right_local_id, touched_right, r_out_mapping);

        ui initial_l_n = batch_vertex_cnt;
        ui initial_r_n = (ui)r_out_mapping.size();

        vector<ui> l_out_mapping(initial_l_n);

        for(ui i = 0; i < initial_l_n; ++i) {
            l_out_mapping[i] = batch_start + i;
        }


        vector<vector<pair<char,ui>>> batch_residual(batch_vertex_cnt);
        vector<vector<ui>> batch_z_list(batch_vertex_cnt);
        eid batch_b_adj_cnt = 2ULL * directed_edge_cnt;

        eid batch_Z_e = 0;
        eid batch_Residual_e = 0;
        long long batch_gain = 0;


        if(directed_edge_cnt == 0) {
            write_batch_vertex_index(file_a, batch_residual, batch_z_list);
            clear_batch_right_mapping(right_local_id, touched_right);
            batch_start = batch_end;
            continue;
        }

        eid* b_pstart = nullptr;
        eid* b_pend = nullptr;
        ui* b_edges = nullptr;
        char* b_score = nullptr;
        ui* b_degree = nullptr;

        construct_batch_bipartite_graph(
            batch_sim_neis,
            right_local_id,
            b_pstart,
            b_pend,
            b_edges,
            b_score,
            b_degree,
            initial_l_n,
            initial_r_n,
            directed_edge_cnt
        );


        vector<vector<pair<ui,char>>>().swap(
            batch_sim_neis
        );

        clear_batch_right_mapping(
            right_local_id,
            touched_right
        );

        ui current_l_n = initial_l_n;
        ui current_r_n = initial_r_n;

        compress_one_batch(
            cfg,
            batch_start,
            batch_vertex_cnt,
            b_pstart,
            b_pend,
            b_edges,
            b_score,
            b_degree,
            l_out_mapping.data(),
            r_out_mapping.data(),
            current_l_n,
            current_r_n,
            batch_residual,
            batch_z_list,
            file_b,
            z_idx,
            batch_b_adj_cnt,
            batch_Z_e,
            batch_Residual_e,
            batch_gain
        );

        assert(batch_Z_e + batch_Residual_e == batch_b_adj_cnt);


        write_batch_vertex_index(
            file_a,
            batch_residual,
            batch_z_list
        );

        total_physical_adj += batch_b_adj_cnt;
        total_Z_e += batch_Z_e;
        total_Residual_e += batch_Residual_e;
        total_gain += batch_gain;

        delete [] b_pstart;
        delete [] b_pend;
        delete [] b_edges;
        delete [] b_score;
        delete [] b_degree;

        cout << "finish batch " << batch_id
             << ", Z adj: " << batch_Z_e
             << ", residual adj: " << batch_Residual_e
             << ", Z count so far: " << z_idx << endl;

        batch_start = batch_end;
    }


    fseek(file_b, 0, SEEK_SET);
    fwrite(&z_idx, sizeof(ui), 1, file_b);

    fclose(file_a);
    fclose(file_b);

    assert(total_Z_e +
           total_Residual_e ==
           total_physical_adj);

    cout << endl;
    cout << "*************** FINAL INDEX INFO ***************" << endl;
    cout << "batch count: " << batch_id << endl;
    cout << "z_idx: " << z_idx << endl;
    cout << "total physical adjacency: "
         << total_physical_adj << endl;

    double z_ratio =
        total_physical_adj > 0
        ? (double)total_Z_e / total_physical_adj
        : 0.0;

    double residual_ratio =
        total_physical_adj > 0
        ? (double)total_Residual_e / total_physical_adj
        : 0.0;

    cout << "edges in Z: "
         << z_ratio * 100.0 << "%" << endl;

    cout << "edges in residual: "
         << residual_ratio * 100.0 << "%" << endl;

    eid total_logical_edges =
        total_physical_adj / 2;

    double saving_ratio =
        total_logical_edges > 0
        ? (double)total_gain / total_logical_edges
        : 0.0;

    cout << "estimated saving ratio: "
         << saving_ratio * 100.0 << "%" << endl;

    cout << "finish writing memory-bounded DB index to disk!"<< endl;

    delete [] vis;
    delete [] comnei_cnt;
}

eid count_simedges_only()
{
    ui * vis = new ui[n];
    memset(vis, 0, sizeof(ui)*n);
    ui * comnei_cnt = new ui[n];
    memset(comnei_cnt, 0, sizeof(ui)*n);

    eid similar_edges_cnt = 0;
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
            char char_s = sim_score * 100;
            if(comnei_cnt[e] >= ComNeiThre && e>u) similar_edges_cnt++;
        }
        for(auto e : u_nei) {
            assert(vis[e] == 1);
            vis[e] = 0;
        }
        for(auto e : u_2hopnei) {
            comnei_cnt[e] = 0;
            assert(vis[e] == 2);
            vis[e] = 0;
        }
    }
    delete [] vis;
    delete [] comnei_cnt;
    return similar_edges_cnt;
}

static void print_usage() {
    cout << "Usage:\n"
         << "  build_index <data_dir> <graph> <index_type> [parameters]\n\n"
         << "Index types:\n"
         << "  DB        <tau> <max_round> <k> <bands> <threshold> <rho> <min_cluster> <min_gain>\n"
         << "  DB-Batch  <tau> <max_round> <k> <bands> <threshold> <rho> <min_cluster> <min_gain>\n"
         << "  BC        <tau> <max_round> <min_cluster> <min_gain>\n"
         << "  VSN       <omit_score_lb> <segment_threshold> <segment_ratio>\n\n"
         << "DB-Batch is the memory-bounded batch construction of DB-Index.\n"
         << "Generated index files are written to ./index/.\n";
}

int main(int argc, const char * argv[]) {
    if(argc < 4) {
        print_usage();
        return 1;
    }

    const string data_dir = argv[1];
    const string graph_name = argv[2];
    const string index_type = argv[3];

    read_graph_binary(data_dir, graph_name);
    Timer timer;

    if(index_type == "DB" || index_type == "DB-Batch") {
        if(argc != 12) {
            print_usage();
            return 1;
        }

        const int tau = atoi(argv[4]);
        const int max_round = atoi(argv[5]);
        const ui k = (ui)atoi(argv[6]);
        const ui bands = (ui)atoi(argv[7]);
        const double threshold = atof(argv[8]);
        const double rho = atof(argv[9]);
        const ui min_cluster = (ui)atoi(argv[10]);
        const ui min_gain = (ui)atoi(argv[11]);

        if(k == 0 || bands == 0 || k < bands || k % bands != 0) {
            cerr << "Error: require k >= bands >= 1 and k % bands == 0.\n";
            return 1;
        }
        if(threshold < 0.0 || threshold > 1.0 || rho < 0.0 || rho > 1.0) {
            cerr << "Error: threshold and rho must be in [0,1].\n";
            return 1;
        }

        if(index_type == "DB") {
            build_db_index(graph_name, tau, max_round, k, bands,
                           threshold, rho, min_cluster, min_gain);
        } else {
            build_db_index_memory_bounded(graph_name, tau, max_round, k, bands,
                                          threshold, rho, min_cluster, min_gain);
        }
    }
    else if(index_type == "BC") {
        if(argc != 8) {
            print_usage();
            return 1;
        }

        const int tau = atoi(argv[4]);
        const int max_round = atoi(argv[5]);
        const ui min_cluster = (ui)atoi(argv[6]);
        const ui min_gain = (ui)atoi(argv[7]);

        build_bc_index(graph_name, tau, max_round, min_cluster, min_gain, true);
    }
    else if(index_type == "VSN") {
        if(argc != 7) {
            print_usage();
            return 1;
        }

        const double omit_score_lb = atof(argv[4]);
        const int segment_threshold = atoi(argv[5]);
        const double segment_ratio = atof(argv[6]);

        if(omit_score_lb < 0.0 || omit_score_lb > 1.0 || segment_threshold < 2) {
            cerr << "Error: invalid VSN parameters.\n";
            return 1;
        }

        build_vsn_index(data_dir, graph_name,
                        omit_score_lb, segment_threshold, segment_ratio);
    }
    else {
        cerr << "Error: unknown index type '" << index_type << "'.\n";
        print_usage();
        return 1;
    }

    cout << "Index construction time: "
         << (double)timer.elapsed() / CLOCKS_PER_SEC << " s\n";

    delete [] pstart;
    delete [] edges;
    delete [] degree;
    pstart = nullptr;
    edges = nullptr;
    degree = nullptr;

    return 0;
}
