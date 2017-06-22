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

#define isAvailable(x) (avEdges.count(x))
#define isFixed(x) (fixedEdges.count(x))
#define isProhibited(x) (!isAvailable(x) and !isFixed(x))

constexpr int MAX_ITER = 100;
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
typedef pair<int, int> Bounds;

Graph graph;
EdgeList edgeList;

int n, m, k;
int sumEdgeCosts;
map<pair<int,int>, pair<int,int>> edgeMap;

struct edgeSet {
    int i;
    edgeSet() {}
    edgeSet(int i): i(i) {}
    bool operator<(const edgeSet& o) const {
        int w = edgeList[i].w;
        int ow = edgeList[o.i].w;
        return w != ow ? w < ow : i < o.i;
    }
};

struct Node {
    Bounds bounds;
    int currCost, idx, last, cntComponents;
    set<edgeSet> avEdges;
    set<edgeSet> fixedEdges;

    Node() {}
    Node(set<edgeSet>& avEdges): currCost(0), idx(0), last(-1), bounds({INF, INF}) {
        this->avEdges = avEdges;
    }
    Node(set<edgeSet>& avEdges, set<edgeSet>& fixedEdges): Node(avEdges) {
        this->fixedEdges = fixedEdges;
    }
    // Node(int c, int l, int u, int i, int last): currCost(c), bounds.lower(l), bounds.upper(u), idx(i), last(last) {}
    bool operator<(const Node& o) const {
        return bounds.lower != o.bounds.lower ? bounds.lower < o.bounds.lower : idx < o.idx;
    }
    bool operator>(const Node& o) const {
        return bounds.lower != o.bounds.lower ? bounds.lower > o.bounds.lower : idx > o.idx;
    }

    void print() {
        for (int i = 0; i < m; ++i) printf("%2d%c", i, " \n"[i==m-1]);
        for (int i = 0; i < m; ++i) printf("%2d%c", isAvailable(i) ? 1 : isFixed(i) ? 2 : 0, " \n"[i==m-1]);
        puts("");
    }
};

void dfs(int u, vector<int>& vis, set<edgeSet>& avEdges, set<edgeSet>& fixedEdges) {
    for (Edge& edge: graph[u]) {
        int v = edge.v;
        if (vis[v]) continue;
        if (isProhibited(edge.i)) continue;
        vis[v] = vis[u];
        dfs(v, vis, avEdges, fixedEdges);
    }
}

int cntComponents(set<edgeSet>& avEdges, set<edgeSet>& fixedEdges, vector<int>& comp) {
    fill(comp.begin(), comp.end(), 0);
    int ans = 0;
    for (int i = 1; i <= n; i++) {
        if (!comp[i]) {
            ans++;
            comp[i] = i;
            dfs(i, comp, avEdges, fixedEdges);
        }
    }
    return ans;
}

int cntComponents(set<edgeSet>& avEdges, set<edgeSet>& fixedEdges) {
    vector<int> comp(n+1, 0);
    return cntComponents(avEdges, fixedEdges, comp);
}

int debug = 0;

// guloso para solução inicial
int greedy(set<edgeSet> avEdges, set<edgeSet>& fixedEdges, vector<int>& comp) {
    vector<int> dad(n+1);
    vector<int> cost(n+1, 0);
    vector<int> vis(n+1, 0);
    set<Edge> heap;
    set<pair<int,int>> S;
    if (debug) printf("Comp: ");
    for (int i = 1; i <= n; ++i) {
        if (comp[i] == i) {
            if (debug) printf("%d ", i);
            dad[i] = i;
            cost[i] = INF;
            heap.insert(Edge(i, cost[i]));
        }
    }
    if (debug) puts("");
    int sumLocalEdgeCosts = 0, cntVertices = 0;
    while (!heap.empty()) {

        Edge x = *heap.begin();
        heap.erase(heap.begin());
        int u = x.v, edgeCost = x.w;

        int idx = edgeMap[{min(u, dad[u]), max(u,dad[u])}].second;
        if (vis[u] or isProhibited(idx)) continue;

        vis[u] = 1;
        comp[u] = comp[dad[u]];
        cntVertices++;

        // if (dad[u] != u) {
        if (edgeCost < INF) {
            S.insert({min(u, dad[u]), max(u, dad[u])});
            sumLocalEdgeCosts += edgeCost;
        }

        for (Edge e: graph[u]) {
            int v = e.v, w = e.w;
            int idx = edgeMap[{min(u, v), max(u, v)}].second;
            if (isProhibited(idx)) continue;
            if (comp[v] == comp[u]) {
                if (!S.count({min(u, v), max(u,v)})) {
                    S.insert({min(u, v), max(u,v)});
                    sumLocalEdgeCosts += w;
                }
                continue;
            }
            if (comp[v] != 0 or cost[v] >= w) continue;
            idx = edgeMap[{min(v, dad[v]), max(v, dad[v])}].second;
            heap.erase(Edge(v, cost[v], idx));
            cost[v] = w;
            dad[v] = u;
            heap.insert(Edge(v, cost[v], e.i));
        }
    }
    if (debug) {
        printf("Comp: ");
        for (int i = 1; i <= n; ++i)
            printf("%d%c", comp[i], " \n"[i==n]);
        printf("%d\n", sumEdgeCosts - sumLocalEdgeCosts);
    }
    return sumEdgeCosts - sumLocalEdgeCosts;
}

Bounds boundFunction(Node& node) {
    
    int usedEdges = 0;
    int lower = node.currCost;
    vector<int> comp(n+1, -1);

    node.cntComponents = cntComponents(node.avEdges, node.fixedEdges, comp);

    if (node.avEdges.size() < k-node.cntComponents)
        return {INF,INF};

    if (node.cntComponents > k)
        return {INF, INF};

    set<edgeSet>::iterator it = node.avEdges.begin();
    if (debug) printf("t: %d\n", node.cntComponents);
    while (it != node.avEdges.end() and usedEdges < k-node.cntComponents) {
        Edge edge = edgeList[it->i];
        // node.avEdges.erase(node.avEdges.begin());
        ++it;
        lower += edgeMap[{edge.u, edge.v}].first;
        usedEdges++;
    }
    if (usedEdges < k-node.cntComponents)
        return {INF, INF};
    if (debug) printf("currCost: %d\n", node.currCost);

    // aloca vetores auxiliares
    vector<int> vertices(n+1);
    iota(vertices.begin(), vertices.end(), 0);

    random_shuffle(vertices.begin()+1, vertices.end());
    int cntComponentsDiscovered = 0;
    vector<int> rep(n+1, 0);
    fill(rep.begin()+1, rep.end(), 0);
    // vector<int> chosen;
    // if (debug) printf("here:");
    int l = 0;
    for (int i = 1; i <= n; ++i) {
        int u = vertices[i];
        if (comp[u] == u) {
            ++cntComponentsDiscovered;
            rep[u] = u;
            // chosen.push_back(u);
            // if (debug) printf("%d ", u);
        }
    // }
    // for (int i = 1; i <= n; ++i) {
    //     int u = vertices[i];
        else if (l != k - node.cntComponents) {
            int found = 0;
            for (int v = 1; v <= n; ++v) {
                if (!edgeMap.count({min(u, v), max(u, v)})) continue;
                if (debug and u != v and (u == 1 or u == 4 or u == 12 or u == 16 or u == 20) and (v == 1 or v == 4 or v == 12 or v == 16 or u == 20))
                    printf("AQUWIUIWE: %d %d\n", u, v);
                // if (comp[v] == v) {
                //     found = 1;
                //     break;
                // }
                // if (debug and v == 1) printf("UE2: (%d, %d)\n", u, v);
                // if (debug) printf(" -- (%d, %d)\n", u, v);
                // if (debug) printf(" ++ (%d, %d)\n", u, v);
                if (node.fixedEdges.count(edgeMap[{min(u, v), max(u, v)}].second)) {
                    found = 1;
                    break;
                }
            }
            if (found) continue;
            ++l;
            rep[u] = u;
            if (debug) printf("%d ", u);
            // chosen.push_back(u);
        }
    }
    int upper = -1;
    if (l + cntComponentsDiscovered < k) upper = INF;
    if (debug) puts("");
    if (upper < INF) upper = greedy(node.avEdges, node.fixedEdges, rep);
    if (debug) {
        for (int i = 1; i <= n; ++i)
            printf("%d%c", comp[i], " \n"[i==n]);
    }

    if (debug) for (int i = 0; i < m; ++i) {
        if (!node.fixedEdges.count(i)) continue;
        int u = edgeList[i].u, v = edgeList[i].v;
        if (comp[u] != comp[v]) printf("((%d, %d))\n", u, v);
    }

    return {lower, upper};
}

// Returns the cost of minimum k-cut of a connected graph
// Branch and bound implemented
pair<int, set<edgeSet>> minkcut(set<edgeSet>& avEdges) {
    int bestCost = INF;
    int nodeIdx = 0;
    set<edgeSet> bestCut;
    set<edgeSet> fixedEdges;
    // heap
    set<Node> heap;
    Node root = Node(avEdges);
    root.cntComponents = -1;
    root.bounds = boundFunction(root);
    heap.insert(root);
    while (!heap.empty()) {
        Node node = *heap.begin();
        heap.erase(heap.begin());
        if (node.bounds.lower > node.bounds.upper) {

            printf("Lower: %d\n", node.bounds.lower);
            printf("Upper: %d\n", node.bounds.upper);
            
            for (auto e: node.fixedEdges) printf("(%d, %d)\n", edgeList[e.i].u, edgeList[e.i].v);
            node.print();
            debug = 1;
            boundFunction(node);

            // exit(0);

        }
        assert(node.bounds.lower <= node.bounds.upper);
        if (node.avEdges.size() == 0) {
            if (node.currCost < bestCost and node.cntComponents == k) {
                bestCost = node.currCost;
                bestCut.clear();
                for (int i = 0; i < m; i++)
                    if (!node.fixedEdges.count(i))
                        bestCut.insert(i);
            }
            continue;
        }
        if (node.cntComponents > k or node.bounds.lower >= bestCost or node.currCost >= bestCost)
            continue;
        if (node.bounds.lower == node.bounds.upper) {
            if (node.bounds.lower < bestCost) {
                // printf("node.idx: %d\n", node.idx);
                bestCost = node.bounds.lower;
                bestCut.clear();
                for (int i = 0; i < m; i++)
                    if (!node.fixedEdges.count(i))
                        bestCut.insert(i);
            }
            continue;
        }

        int next = node.last + 1;

        // erase edge (edge from cut)
        Node nextNode = Node(node.avEdges, node.fixedEdges);
        nextNode.last = next;
        nextNode.idx = nodeIdx++;
        nextNode.avEdges.erase(next);
        nextNode.currCost = node.currCost + edgeList[next].w;
        nextNode.bounds = boundFunction(nextNode);
        if (node.bounds.lower < bestCost)
            heap.insert(nextNode);
        
        // fix edge (edge from resulting graph)
        nextNode.idx = nodeIdx++;
        nextNode.fixedEdges.insert(next);
        nextNode.currCost = node.currCost;
        nextNode.bounds = boundFunction(nextNode);
        if (node.bounds.lower < bestCost)
            heap.insert(nextNode);

    }
    return {bestCost, bestCut};
}

int main() {
    srand(time(NULL));
    // Reads number of vertices, edges and the parameter k, respectively
    scanf("%d %d %d", &n, &m, &k);
    // Declares graph and list of edges
    graph.resize(n+1);
    edgeList.resize(m);

    set<edgeSet> avEdges;
    set<edgeSet> fixedEdges;
    // Reads input, assuming no multiple edges are allowed
    for (int i = 0, u, v, w; i < m; i++) {
        scanf("%d %d %d", &u, &v, &w);
        sumEdgeCosts += w;

        if (u > v) swap(u, v);
        edgeList[i] = Edge(u, v, w, i);
        edgeMap[{u, v}] = {w, i};
        avEdges.insert(i);

        graph[u].push_back(Edge(u, v, w, i));
        graph[v].push_back(Edge(v, u, w, i));
    }

    // // tests for g1.txt
    // avEdges.erase(15);
    // avEdges.erase(16);
    // avEdges.erase(32);

    vector<int> vis(n+1);
    printf("Number of connected components: %d\n", cntComponents(avEdges, fixedEdges, vis));

    // int lower, upper;
    // tie(lower, upper) = boundFunction(avEdges, fixedEdges, 9);
    // printf("Lower: %d\n", lower);
    // printf("Upper: %d\n", upper);


    // Calls the minkcut() function to give answer
    int bestCost;
    set<edgeSet> bestCut;
    tie(bestCost, bestCut) = minkcut(avEdges);
    if (bestCost == INF) return 0*puts("Unfeasible problem");
    printf("Cost of minimum k-cut: %d\n", bestCost);
    for (int i = 0; i < m; ++i)
        if (bestCut.count(i))
            printf("%d. (%d, %d): %d\n", edgeList[i].i, edgeList[i].u, edgeList[i].v, edgeList[i].w);
    return 0;
}
