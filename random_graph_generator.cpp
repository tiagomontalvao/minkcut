#include <bits/stdc++.h>
using namespace std;

int n = 128;
double edgeProb = 0.2;
int maxWeight = 20;
const int N = 1024;
int c[N][N];

void dfs(int u, vector<int>& vis) {
    for (int v = 1; v <= n; ++v) {
        if (!c[u][v] or vis[v]) continue;
        vis[v] = vis[u];
        dfs(v, vis);
    }
}

void fixComponents(vector<tuple<int,int,int>>& edges) {
    vector<int> vis(n+1, 0);
    vector<int> rep;
    for (int i = 1; i <= n; i++) {
        if (!vis[i]) {
            vis[i] = i;
            rep.push_back(i);
            dfs(i, vis);
        }
    }
    for (int i = 1; i < rep.size(); ++i) {
        c[rep[i]][rep[0]] = c[rep[0]][rep[i]] = rand() % maxWeight + 1;
        edges.push_back(make_tuple(rep[0], rep[i], c[rep[0]][rep[i]]));
    }
}


int main(int argc, char const *argv[]) {
    if (argc >= 2)
        n = atoi(argv[1]);
    if (argc >= 3)
        edgeProb = atof(argv[2]);
    if (argc >= 4)
        maxWeight = atoi(argv[3]);
    srand(time(NULL));
    vector<tuple<int,int,int>> edges;
    for (int i = 1; i < n; ++i) {
        for (int j = i+1; j <= n; ++j) {
            double pickRandom = rand();
            if (pickRandom <= edgeProb*RAND_MAX) {
                int w = rand() % maxWeight + 1;
                c[i][j] = c[j][i] = w;
                edges.push_back(make_tuple(i, j, w));
            }
        }
    }
    fixComponents(edges);
    printf("%d %d\n", n, (int)edges.size());
    for (auto& edge: edges)
        printf("%d %d %d\n", get<0>(edge), get<1>(edge), get<2>(edge));
    return 0;
}