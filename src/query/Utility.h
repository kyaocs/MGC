#ifndef _UTILITY_H_
#define _UTILITY_H_

#include <ctime>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <sstream>
#include <iostream>
#include <tuple>
#include <queue>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <fstream>
#include <iomanip>
#include <filesystem>
#include <climits>
#include <chrono>
#include <random>
#include <cfloat>


#include <cstdint>
#include <numeric>
#include <limits>
#include <iomanip>

#define NDEBUG
#include <cassert>


typedef long long i64;
typedef __int128 i128;


#define _Pivot_
#define _Coloring_
#define _BnBVR_
#define _HeuEgo_
#define _FalseTwinHeu_

#define ComNeiThre 3

using namespace std;

using ui = unsigned int;
using eid = uint64_t;
using ull = unsigned long long;
const ui INVALID_UI = numeric_limits<ui>::max();

const ui BNB_VR_SIZE_THRESHOLD = 128;
const ui BNB_VR_MAX_DEPTH = 4;

#define pb push_back
#define mp make_pair

#define mmax(a,b) ((a)>(b)?(a):(b))
#define mmin(a,b) ((a)<(b)?(a):(b))

ui n, m;
ui * pstart;
ui * edges;
ui * degree;

char * f_edges;

ui * oid_mapping;
ui * newid_mapping;
char ** Matrix;
ui * trs;
ui * s_pstart;
ui * s_pend;
ui * s_edges;
ui * s_degree;

long long ss;
long long resnum;
int max_gc_size;
vector<vector<ui>> res;

ui seed_num = 32;

double epsi;
int sz;

long long tt_mat;

class Utility {
public:
	static FILE *open_file(const char *file_name, const char *mode) {
		FILE *f = fopen(file_name, mode);
		if(f == nullptr) {
			printf("Can not open file: %s\n", file_name);
			exit(1);
		}

		return f;
	}

	static std::string integer_to_string(long long number) {
		std::vector<ui> sequence;
		if(number == 0) sequence.pb(0);
		while(number > 0) {
			sequence.pb(number%1000);
			number /= 1000;
		}

		char buf[5];
		std::string res;
		for(ui i = sequence.size();i > 0;i --) {
			if(i == sequence.size()) sprintf(buf, "%u", sequence[i-1]);
			else sprintf(buf, ",%03u", sequence[i-1]);
			res += std::string(buf);
		}
		return res;
	}
};

inline pair<double,ui> js(ui u, ui v)
{
    int du = degree[u], dv = degree[v];
    if( (double) min(du, dv) / max(du, dv) < epsi) return make_pair(0, 0);

    ui idx1 = pstart[u], idx2 = pstart[v];
    ui idx1_end = idx1 + du, idx2_end = idx2 + dv;
    int common = 0;

    while (idx1 < idx1_end && idx2 < idx2_end) {
        if(edges[idx1] == edges[idx2]){
            ++ common; ++ idx1; ++ idx2;
        }
        else{
            if(edges[idx1] > edges[idx2]) ++ idx2;
            else ++ idx1;
        }
    }
    if(common<ComNeiThre) common=0;

    return make_pair((double)common/(du + dv - common), common);
}

inline bool js_decision(ui u,ui v)
{
    int du = degree[u], dv = degree[v];
    if(du <= dv && ((double) du/dv) < epsi ) return false;
    else if (((double) dv/du) < epsi) return false;
    int thre = ceil(epsi*(du+dv)/(1+epsi));
    ui idx1 = pstart[u], idx2 = pstart[v];
    ui idx1_end = idx1 + du, idx2_end = idx2 + dv;
    int common=0;

    while (idx1 < idx1_end && idx2 < idx2_end) {
        if(edges[idx1] == edges[idx2]){
            ++ common;
            ++ idx1; ++ idx2;
            if(common>=thre && common >= ComNeiThre) return true;
        }
        else{
            if(edges[idx1] > edges[idx2]) ++ idx2;
            else ++ idx1;
        }
    }
    return false;
}

bool is_structural_neighbor(ui u, ui v)
{
    return binary_search(edges + pstart[u], edges + pstart[u+1], v);
}

void check_gc_correct(const vector<ui>& clique)
{
    for(ui i = 0; i < clique.size(); ++i) {
        for(ui j = i + 1; j < clique.size(); ++j) {
            ui u = clique[i];
            ui v = clique[j];

            if(is_structural_neighbor(u, v)) continue;

            auto jsp = js(u, v);

            if(jsp.first < epsi) {
                cout << "Error: heuristic result is not a GC!" << endl;
                cout << "u = " << u
                     << ", v = " << v
                     << ", js = " << jsp.first << endl;
                exit(1);
            }
        }
    }
}

#endif
