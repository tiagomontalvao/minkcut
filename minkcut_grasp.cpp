#include <algorithm>
#include <cassert>
#include <cstdio>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <utility>
#include <vector>
using namespace std;

#define lower first
#define upper second

constexpr int alpha = 1;
constexpr int n_elite = 10;

constexpr int MAX_ITER = 4096;
constexpr int N = 1024;
constexpr int M = 1048576;
constexpr int INF = 0x3F3F3F3F;

struct Edge {
    int u, v, w, i;
    Edge() {}
    Edge(int v, int w): u(-1), v(v), w(w), i(-1) {}
    Edge(int v, int w, int i): u(-1), v(v), w(w), i(i) {}
    Edge(int u, int v, int w, int i): u(u), v(v), w(w), i(i) {}
    bool operator<(const Edge& o) const {
        if (w != o.w) return w > o.w;
        if (u != o.u) return u < o.u;
        if (v != o.v) return v < o.v;
        if (i != o.i) return i < o.i;
    }
};

typedef vector<vector<Edge>> Graph;
typedef vector<Edge> EdgeList;

Graph graph;
EdgeList edgeList;

int n, m, k;
int sumEdgeCosts;
map<pair<int,int>, pair<int,int>> edgeMap;

void dfs(vector<int>& vis, int u) {
    vis[u] = 1;
    for (Edge edge: graph[u]) {
        int v = edge.v;
        if (vis[v]) continue;
        dfs(vis, v);
    }
}

int cntComponents() {
    vector<int> vis(n+1, 0);
    int ans = 0;
    for (int i = 1; i <= n; ++i) {
        if (!vis[i]) {
            ans++;
            dfs(vis, i);
        }
    }
    return ans;
}

void relabel(int u, int newComp, int oldComp, vector<int>& comp) {
    comp[u] = newComp;
    for (Edge e: graph[u]) {
        if (comp[e.v] != oldComp) continue;
        relabel(e.v, newComp, oldComp, comp);
    }
}

int local_search(vector<int>& x, vector<int>& comp) {
    vector<int> vertices(n+1);
    iota(vertices.begin(), vertices.end(), 0);
    random_shuffle(vertices.begin()+1, vertices.end());
    int improvedSolution = 0;
    for (int i = 0; i < n; ++i) {

        vector<int> compSum(n+1, 0);
        int u = vertices[i];
        int hasCompNeighbors = 0, uNeighbor;
        for (Edge e: graph[u]) {
            if (comp[e.v] == comp[u]) {
                uNeighbor = e.v;
                hasCompNeighbors = 1; 
            }
            compSum[comp[e.v]] += e.w;
        }
        if (!hasCompNeighbors) continue;
        int bestComponent = -1, bestSum = 0;
        for (int v = 1; v <= n; ++v) {
            if (comp[v] != v) continue;
            if (compSum[comp[v]] - compSum[comp[u]] > bestSum) {
                bestSum = compSum[comp[v]] - compSum[comp[u]];
                bestComponent = comp[v];
            }
        }
        if (bestComponent == -1) continue;
        if (u == comp[u]) continue;
        improvedSolution += bestSum;
        int oldComponent = comp[u];
        comp[u] = bestComponent;
        for (Edge e: graph[u]) {
            assert(0 <= e.i and e.i < m);
            if (comp[e.v] == oldComponent) x[e.i] = 1;
            if (comp[e.v] == bestComponent) x[e.i] = 0;
        }
    }
    return improvedSolution;
}

// guloso para solução inicial
pair<vector<int>, int> greedy(vector<int>& comp) {
    vector<int> usedEdges(m, 1);
    vector<int> dad(n+1);
    vector<int> cost(n+1, 0);
    vector<int> vis(n+1, 0);
    set<Edge> heap;
    set<pair<int,int>> S;
    for (int i = 1; i <= n; ++i) {
        if (comp[i] == i) {
            dad[i] = i;
            cost[i] = INF;
            heap.insert(Edge(i, cost[i]));
        }
    }
    int sumLocalEdgeCosts = 0, cntVertices = 0;
    while (!heap.empty()) {

        Edge x = *heap.begin();
        if (x.w == INF) {
            heap.erase(heap.begin());
        } else {

            set<Edge>::iterator it = heap.begin();
            vector<set<Edge>::iterator> LRC;
            while (it != heap.end()) {
                if (it->w * alpha < x.w) break;
                LRC.push_back(it);
                it++;
            }

            assert(LRC.size() > 0);
            int idx = rand() % (int) LRC.size();
            x = *LRC[idx];
            heap.erase(LRC[idx]);
        }

        int u = x.v, edgeCost = x.w;
        if (vis[u]) continue;
        vis[u] = 1;
        comp[u] = comp[dad[u]];
        cntVertices++;

        if (edgeCost < INF) {
            S.insert({min(u, dad[u]), max(u, dad[u])});
            sumLocalEdgeCosts += edgeCost;
            assert(0 <= x.i and x.i < m);
            usedEdges[x.i] = 0;
        }

        for (Edge e: graph[u]) {
            int v = e.v, w = e.w;
            if (comp[v] == comp[u]) {
                if (!S.count({min(u, v), max(u,v)})) {
                    S.insert({min(u, v), max(u,v)});
                    sumLocalEdgeCosts += w;
                    assert(0 <= x.i and x.i < m);
                    usedEdges[e.i] = 0;
                }
                continue;
            }
            if (comp[v] != 0 or cost[v] >= w) continue;
            // int dadv = dad[v];
            // int idx = edgeMap[{min(v, dadv), max(v, dadv)}].second;
            // heap.erase(Edge(v, cost[v], idx));
            heap.erase(Edge(v, cost[v]));
            cost[v] = w;
            dad[v] = u;
            heap.insert(Edge(v, cost[v], e.i));
        }

    }
    return {usedEdges, sumEdgeCosts - sumLocalEdgeCosts};
}

void dfs(vector<int>& vis, vector<int>& x, int u) {
    vis[u] = 1;
    for (Edge edge: graph[u]) {
        int v = edge.v;
        if (vis[v]) continue;
        int u2 = u, v2 = v;
        if (u2 > v2) swap(u2, v2);
        if (x[edgeMap[{u2,v2}].second] == 1) continue;
        dfs(vis, x, v);
    }
}

int cntComponentsFromX(vector<int>& x) {
    vector<int> vis(n+1, 0);
    int ans = 0;
    for (int i = 1; i <= n; ++i) {
        if (!vis[i]) {
            ans++;
            dfs(vis, x, i);
        }
    }
    return ans;
}

// implementação boba do path relinking
void path_relinking(int aval, vector<int>& x, vector<int>& comp, set<pair<int, vector<int>>>& elite) {
    int idx = rand()%elite.size();
    auto it = elite.begin();
    for (int i = 0; i < idx; ++it, ++i);
    vector<int> origin, destiny;
    if (aval > it->first) {
        origin = x;
        destiny = it->second;
    } else {
        origin = it->second;
        destiny = x;
    }
    vector<int> toZero, toOne;
    int newAval = 0;
    for (int i = 0; i < m; ++i) {
        newAval += origin[i] * edgeList[i].w;
        if (origin[i] ^ destiny[i] != 1) continue;
        if (origin[i] == 1) toZero.push_back(i);
        if (destiny[i] == 1) toOne.push_back(i);
    }
    int i = 0, j = 0;
    random_shuffle(toZero.begin(), toZero.end());
    random_shuffle(toOne.begin(), toOne.end());
    int bestAval = sumEdgeCosts;
    vector<int> bestX;
    while (i < toZero.size() and j < toOne.size()) {
        int r = rand()%2;
        if (r == 0) {
            int idx = toZero[i++];
            origin[idx] = 0;
            newAval -= edgeList[idx].w;
        } else {
            int idx = toOne[j++];
            origin[idx] = 1;
            newAval += edgeList[idx].w;
        }
        if (cntComponentsFromX(origin) != k) continue;
        if (newAval < bestAval) {
            bestAval = newAval;
            bestX = origin;
        }
    }
    while (i < toZero.size()) {
        int idx = toZero[i++];
        origin[idx] = 0;
        newAval -= edgeList[idx].w;
    }
    while (j < toOne.size()) {
        int idx = toOne[j++];
        origin[idx] = 1;
        newAval += edgeList[idx].w;
    }

    // if (bestAval < elite.end()->first) { puts("Update"); }

    int worstAval = (--elite.end())->first;
    if (bestAval < worstAval) {
        elite.erase(--elite.end());
        elite.insert({bestAval, bestX});
    }
}

// meta-heurística para o problema do k-corte mínimo
pair<int,vector<int>> minkcut_grasp() {

    // aloca vetores auxiliares
    vector<int> vertices(n+1);
    vector<int> comp(n+1, -1);
    iota(vertices.begin(), vertices.end(), 0);
    set<pair<int, vector<int>>> elite;

    // para cada uma das iterações
    for (int iter = 0; iter < MAX_ITER; ++iter) {

        // configura valores aleatórios e os k representantes de cada conjunto
        random_shuffle(vertices.begin()+1, vertices.end());
        fill(comp.begin()+1, comp.end(), 0);
        for (int j = 1; j <= k; ++j)
            comp[vertices[j]] = vertices[j];
        vector<int> usedEdges;

        // solução inicial gulosa, com escolhas internas aleatórias, a partir dos valores acima
        int heur;
        tie(usedEdges, heur) = greedy(comp);

        // local search tenta melhorar solução
        int cntLocalSearch = 0, localImprove;
        while (localImprove = local_search(usedEdges, comp))
            cntLocalSearch++, heur -= localImprove;

        // a partir de um certo ponto, ativa o path relinking com soluções da elite
        if (iter >= MAX_ITER/2 and iter >= n_elite)
            path_relinking(heur, usedEdges, comp, elite);
        
        // atualiza elite a cada iteração
        if (elite.size() < n_elite or heur < (--elite.end())->first) {
            elite.insert({heur, usedEdges});
            if (elite.size() > n_elite)
                elite.erase(--elite.end());
        }
    }
    return *elite.begin();
}


int main() {
    // semente para gerador de números pseudo-aleatórios
    srand(time(0));

    // leitura dos parâmetros da entrada 
    scanf("%d %d %d", &n, &m, &k);

    // alocação do espaço para a entrada
    graph.resize(n+1);
    edgeList.resize(m);

    // leitura da entrada
    for (int i = 0, u, v, w; i < m; ++i) {
        scanf("%d %d %d", &u, &v, &w);
        sumEdgeCosts += w;
        
        // constroi estrutura auxiliar
        if (u > v) swap(u, v);
        edgeList[i] = Edge(u, v, w, i);
        edgeMap[{u, v}] = {w, i};

        // monta lista de adjacências
        graph[u].push_back(Edge(u, v, w, i));
        graph[v].push_back(Edge(v, u, w, i));
    }

    int ans;
    vector<int> solution;
    tie(ans, solution) = minkcut_grasp();

    // imprime resposta
    clog << "Cost of minimum k-cut: " << ans << endl;
    for (int i = 0; i < m; ++i)
        if (solution[i])
            printf("%d. (%d, %d): %d\n", edgeList[i].i, edgeList[i].u, edgeList[i].v, edgeList[i].w);

    return 0;
}
