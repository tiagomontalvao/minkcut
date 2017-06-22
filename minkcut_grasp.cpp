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

// parameters of GRASP
constexpr int alpha = 3;
constexpr int n_elite = 10;
constexpr int MAX_ITER = 1024;

constexpr int INF = 0x3F3F3F3F;

// edge of the graph
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

void dfs(vector<int>& vis, int u);
int cntComponents();
int local_search(vector<int>& x, vector<int>& comp);
pair<vector<int>, int> greedy(vector<int>& comp);
void dfs(vector<int>& vis, vector<int>& x, int u);
int cntComponentsFromX(vector<int>& x);
void path_relinking(int aval, vector<int>& x, vector<int>& comp, set<pair<int, vector<int>>>& elite);
pair<int,vector<int>> grasp();

// Main function
int main() {
    // seed to pseudorangom number generator so that different runs yield different results  
    srand(time(0));

    // reads number of vertices, edges and the parameter k, respectively
    scanf("%d %d %d", &n, &m, &k);

    // allocates graph and list of edges
    graph.resize(n+1);
    edgeList.resize(m);

    // reads input, assuming no multiple edges are allowed
    for (int i = 0, u, v, w; i < m; ++i) {
        scanf("%d %d %d", &u, &v, &w);
        sumEdgeCosts += w;
        
        // edgeList[i] contains the i-th edge
        // edgeList[{u, v}] contains the pair {w, i} of the i-th edge, if u < v (to save space)
        if (u > v) swap(u, v);
        edgeList[i] = Edge(u, v, w, i);
        edgeMap[{u, v}] = {w, i};

        // creates adjacency list
        graph[u].push_back(Edge(u, v, w, i));
        graph[v].push_back(Edge(v, u, w, i));
    }

    // calls the grasp() function to give answer {bestCost, bestCut}
    int bestCost;
    vector<int> bestCut;
    tie(bestCost, bestCut) = grasp();

    // prints answer
    printf("Cost of minimum k-cut: %d\n", bestCost);

    // prints edges on k-cut
    for (int i = 0; i < m; ++i)
        if (bestCut[i])
            printf("%d. (%d, %d): %d\n", edgeList[i].i, edgeList[i].u, edgeList[i].v, edgeList[i].w);

    return 0;
}

// Deapth-first search
void dfs(vector<int>& vis, int u) {
    vis[u] = 1;
    for (Edge edge: graph[u]) {
        int v = edge.v;
        if (vis[v]) continue;
        dfs(vis, v);
    }
}

// Returns the number of connected components
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

// Returns a better solution than the current one given by x
// Local seach implemented
int local_search(vector<int>& x, vector<int>& comp) {

    // auxiliary vector for the random part
    vector<int> vertices(n+1);
    iota(vertices.begin(), vertices.end(), 0);
    random_shuffle(vertices.begin()+1, vertices.end());

    // improve of the answer
    int improvedSolution = 0;

    for (int i = 0; i < n; ++i) {
        vector<int> compSum(n+1, 0);

        // for each vertex u
        int u = vertices[i];
        int hasCompNeighbors = 0, uNeighbor;
        
        // computes sum of edges for each component
        for (Edge e: graph[u]) {
            if (comp[e.v] == comp[u]) {
                uNeighbor = e.v;
                hasCompNeighbors = 1; 
            }
            compSum[comp[e.v]] += e.w;
        }

        // if u is the only vertex in a connected component, it can't be moved to another component
        if (!hasCompNeighbors) continue;
        int bestComponent = -1, bestSum = 0;

        // select best component to move u
        for (int v = 1; v <= n; ++v) {
            if (comp[v] != v) continue;
            if (compSum[comp[v]] - compSum[comp[u]] > bestSum) {
                bestSum = compSum[comp[v]] - compSum[comp[u]];
                bestComponent = comp[v];
            }
        }

        // if there is no such component, continue
        if (bestComponent == -1) continue;

        // if u is a component representant, it can't be moved to another one
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

// Greedy function initial solution
pair<vector<int>, int> greedy(vector<int>& comp) {

    // auxiliary vectors
    vector<int> usedEdges(m, 1);
    vector<int> dad(n+1);
    vector<int> cost(n+1, 0);
    vector<int> vis(n+1, 0);
    set<pair<int,int>> S;
    
    // a binary search tree, used as a heap
    set<Edge> heap;
    
    // insert all the k chosen vertices on the heap
    for (int i = 1; i <= n; ++i) {
        if (comp[i] == i) {
            dad[i] = i;
            cost[i] = INF;
            heap.insert(Edge(i, cost[i]));
        }
    }

    int sumLocalEdgeCosts = 0, cntVertices = 0;
    while (!heap.empty()) {

        // select vertex from heap
        Edge x = *heap.begin();
        if (x.w == INF) {
            heap.erase(heap.begin());
        } else {

            // form LRC list
            set<Edge>::iterator it = heap.begin();
            vector<set<Edge>::iterator> LRC;
            while (it != heap.end()) {
                if (it->w * alpha < x.w) break;
                LRC.push_back(it);
                it++;
            }

            // choose some vertex at random
            int idx = rand() % (int) LRC.size();
            x = *LRC[idx];
            heap.erase(LRC[idx]);
        }

        // vertex u chosen
        int u = x.v, edgeCost = x.w;
        if (vis[u]) continue;
        vis[u] = 1;
        comp[u] = comp[dad[u]];
        cntVertices++;

        // if u is a component representant
        if (edgeCost < INF) {
            S.insert({min(u, dad[u]), max(u, dad[u])});
            sumLocalEdgeCosts += edgeCost;
            usedEdges[x.i] = 0;
        }

        // for each edge e that is adjacent to u
        for (Edge e: graph[u]) {

            // neighbor v with edge weight w
            int v = e.v, w = e.w;
            
            // if they are both on same component, use that edge
            if (comp[v] == comp[u]) {
                if (!S.count({min(u, v), max(u,v)})) {
                    S.insert({min(u, v), max(u,v)});
                    sumLocalEdgeCosts += w;
                    usedEdges[e.i] = 0;
                }
                continue;
            }
            // if vertex v is on another component or if 
            if (comp[v] != 0 or cost[v] >= w) continue;
            int dadv = dad[v];
            int idx = edgeMap[{min(v, dadv), max(v, dadv)}].second;
            heap.erase(Edge(v, cost[v], idx));
            cost[v] = w;
            dad[v] = u;
            heap.insert(Edge(v, cost[v], e.i));
        }

    }
    return {usedEdges, sumEdgeCosts - sumLocalEdgeCosts};
}

// Deapth-first search
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

// Returns the number of connected components, giving some edges on cut
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

// Implementation of path relinking
void path_relinking(int aval, vector<int>& x, vector<int>& comp, set<pair<int, vector<int>>>& elite) {
    int idx = rand()%elite.size();
    auto it = elite.begin();
    for (int i = 0; i < idx; ++it, ++i);
    vector<int> origin, destiny;
    
    // go from best to worst solution
    if (aval > it->first) {
        origin = x;
        destiny = it->second;
    } else {
        origin = it->second;
        destiny = x;
    }

    // positions to change to zero and one, respectively
    vector<int> toZero, toOne;
    int newAval = 0;
    for (int i = 0; i < m; ++i) {
        newAval += origin[i] * edgeList[i].w;
        if (origin[i] ^ destiny[i] != 1) continue;
        if (origin[i] == 1) toZero.push_back(i);
        if (destiny[i] == 1) toOne.push_back(i);
    }

    // random order of change
    int i = 0, j = 0;
    random_shuffle(toZero.begin(), toZero.end());
    random_shuffle(toOne.begin(), toOne.end());
    int bestAval = sumEdgeCosts;
    vector<int> bestX;

    // moving from origin to destiny solution
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

    // updates elite set if necessary
    int worstAval = (--elite.end())->first;
    if (bestAval < worstAval) {
        elite.erase(--elite.end());
        elite.insert({bestAval, bestX});
    }
}

// Returns pair the minimum k-cut
// GRASP: Greedy Randomized Adaptive Search Procedure
pair<int,vector<int>> grasp() {

    // auxiliary vector for the random part
    vector<int> vertices(n+1);
    vector<int> comp(n+1, -1);
    iota(vertices.begin(), vertices.end(), 0);
    set<pair<int, vector<int>>> elite;

    // for each of the MAX_ITER iterations
    for (int iter = 0; iter < MAX_ITER; ++iter) {

        // select the k representants of each connected component
        random_shuffle(vertices.begin()+1, vertices.end());
        fill(comp.begin()+1, comp.end(), 0);
        for (int j = 1; j <= k; ++j)
            comp[vertices[j]] = vertices[j];
        vector<int> usedEdges;

        // greedy initial solution, with random internal choices, based on parameters defined as consts up in the code
        int heur;
        tie(usedEdges, heur) = greedy(comp);

        // local search tries to improve solution
        int cntLocalSearch = 0, localImprove;
        while (localImprove = local_search(usedEdges, comp))
            cntLocalSearch++, heur -= localImprove;

        // from some given iteration, path relinking is activated com soluções da elite
        if (iter >= MAX_ITER/2 and iter >= n_elite)
            path_relinking(heur, usedEdges, comp, elite);
        
        // updates elite set each iteration
        if (elite.size() < n_elite or heur < (--elite.end())->first) {
            elite.insert({heur, usedEdges});
            if (elite.size() > n_elite)
                elite.erase(--elite.end());
        }
    }
    return *elite.begin();
}
