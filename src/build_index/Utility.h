#ifndef _UTILITY_H_
#define _UTILITY_H_

#include <ctime>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>
#include <random>
#include <algorithm>
#include <sstream>
#include <iostream>
#include <tuple>
#include <queue>
#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <fstream>
#include <iomanip>
#include <filesystem>
#include <climits>
#define NDEBUG
#include <cassert>

using namespace std;

static std::mt19937 rng(std::random_device{}());


#define _Pivot_

#define ComNeiThre 3

using ui = unsigned int;
using eid = uint64_t;
using ull = unsigned long long;
const ui INVALID_UI = numeric_limits<ui>::max();

const int INF = 1000000000;
long long search_space = 0;


long long PeelSG_round_interval;
long long PeelSG_core_sum;
long long PeelSG_size_sum;
double PeelSG_den_sum;
long long PeelSG_del_e_sum;

vector<pair<vector<ui>,vector<ui>>> mbc_res;

#define pb push_back
#define mp make_pair

#define mmax(a,b) ((a)>(b)?(a):(b))
#define mmin(a,b) ((a)<(b)?(a):(b))

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

#endif
