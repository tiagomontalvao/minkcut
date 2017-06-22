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

// useful macros
#define lower first
#define upper second

#define isAvailable(x) (avEdges.count(x))
#define isFixed(x) (fixedEdges.count(x))
#define isProhibited(x) (!isAvailable(x) and !isFixed(x))

constexpr int N = 1024;
constexpr int M = 1048576;
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
typedef pair<int, int> Bounds;

Graph graph;
EdgeList edgeList;

int n, m, k;
int sumEdgeCosts;
map<pair<int,int>, pair<int,int>> edgeMap;

// useful struct
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

// node of branch and bound
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
    bool operator<(const Node& o) const {
        return bounds.lower != o.bounds.lower ? bounds.lower < o.bounds.lower : idx < o.idx;
    }
    void print() {
        for (int i = 0; i < m; ++i) printf("%2d%c", i, " \n"[i==m-1]);
        for (int i = 0; i < m; ++i) printf("%2d%c", isAvailable(i) ? 1 : isFixed(i) ? 2 : 0, " \n"[i==m-1]);
        puts("");
    }
};

void dfs(int u, vector<int>& vis, set<edgeSet>& avEdges, set<edgeSet>& fixedEdges);
int cntComponents(set<edgeSet>& avEdges, set<edgeSet>& fixedEdges, vector<int>& comp);
int cntComponents(set<edgeSet>& avEdges, set<edgeSet>& fixedEdges);
int greedy(set<edgeSet> avEdges, set<edgeSet>& fixedEdges, vector<int>& comp);
Bounds boundFunction(Node& node);
pair<int, set<edgeSet>> minkcut(set<edgeSet>& avEdges);

int main() {

    // seed to pseudorangom number generator so that different runs yield different results
    srand(time(NULL));

    // reads number of vertices, edges and the parameter k, respectively
    scanf("%d %d %d", &n, &m, &k);

    // allocates graph and list of edges
    graph.resize(n+1);
    edgeList.resize(m);

    // initial set of available and fixed edges
    set<edgeSet> avEdges;
    set<edgeSet> fixedEdges;

    // reads input, assuming no multiple edges are allowed
    for (int i = 0, u, v, w; i < m; i++) {
        scanf("%d %d %d", &u, &v, &w);
        sumEdgeCosts += w;

        // edgeList[i] contains the i-th edge
        // edgeList[{u, v}] contains the pair {w, i} of the i-th edge, if u < v (to save space)
        if (u > v) swap(u, v);
        edgeList[i] = Edge(u, v, w, i);
        edgeMap[{u, v}] = {w, i};
        avEdges.insert(i);

        // creates adjacency list
        graph[u].push_back(Edge(u, v, w, i));
        graph[v].push_back(Edge(v, u, w, i));
    }

    // number of connected components
    vector<int> vis(n+1);
    printf("Number of connected components: %d\n", cntComponents(avEdges, fixedEdges, vis));

    // calls the minkcut() function to give answer {bestCost, bestCut}
    int bestCost;
    set<edgeSet> bestCut;
    tie(bestCost, bestCut) = minkcut(avEdges);
    if (bestCost == INF) return 0*puts("Unfeasible problem");

    // prints bestCost
    printf("Cost of minimum k-cut: %d\n", bestCost);

    // prints bestCut
    for (int i = 0; i < m; ++i)
        if (bestCut.count(i))
            printf("%d. (%d, %d): %d\n", edgeList[i].i, edgeList[i].u, edgeList[i].v, edgeList[i].w);
    return 0;
}


// Deapth-first search
void dfs(int u, vector<int>& vis, set<edgeSet>& avEdges, set<edgeSet>& fixedEdges) {
    for (Edge& edge: graph[u]) {
        int v = edge.v;
        if (vis[v]) continue;
        if (isProhibited(edge.i)) continue;
        vis[v] = vis[u];
        dfs(v, vis, avEdges, fixedEdges);
    }
}

// Returns the number of connected components
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

// Returns the number of connected components
int cntComponents(set<edgeSet>& avEdges, set<edgeSet>& fixedEdges) {
    vector<int> comp(n+1, 0);
    return cntComponents(avEdges, fixedEdges, comp);
}

// Greedy function for primal limit
int greedy(set<edgeSet> avEdges, set<edgeSet>& fixedEdges, vector<int>& comp) {
// pair<vector<int>, int> greedy(set<edgeSet> avEdges, set<edgeSet>& fixedEdges, vector<int>& comp) {
   
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         // vector<int> usedEdges(m, 1);
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
        heap.erase(heap.begin());
        int u = x.v, edgeCost = x.w;

        int idx = edgeMap[{min(u, dad[u]), max(u,dad[u])}].second;
        if (vis[u] or isProhibited(idx)) continue;

        vis[u] = 1;
        comp[u] = comp[dad[u]];
        cntVertices++;

        if (edgeCost < INF) {
            S.insert({min(u, dad[u]), max(u, dad[u])});
            sumLocalEdgeCosts += edgeCost;
            // usedEdges[x.i] = 0;
        }

        for (Edge e: graph[u]) {
            int v = e.v, w = e.w;
            int idx = edgeMap[{min(u, v), max(u, v)}].second;
            if (isProhibited(idx)) continue;
            if (comp[v] == comp[u]) {
                if (!S.count({min(u, v), max(u,v)})) {
                    S.insert({min(u, v), max(u,v)});
                    sumLocalEdgeCosts += w;
                    // usedEdges[e.i] = 0;
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
    return sumEdgeCosts - sumLocalEdgeCosts;
    // return {usedEdges[e.i], sumEdgeCosts - sumLocalEdgeCosts};
}

// Returns a pair {lower, upper} of bounds of a node
Bounds boundFunction(Node& node) {

    int usedEdges = 0;
    int lower = node.currCost;
    vector<int> comp(n+1, -1);

    node.cntComponents = cntComponents(node.avEdges, node.fixedEdges, comp);

    // infeasible solutions
    if (node.avEdges.size() < k-node.cntComponents)
        return {INF,INF};
    if (node.cntComponents > k)
        return {INF, INF};

    // iterator for getting the k-node.cntComponents cheapest available edges
    set<edgeSet>::iterator it = node.avEdges.begin();
    while (it != node.avEdges.end() and usedEdges < k-node.cntComponents) {
        Edge edge = edgeList[it->i];
        ++it;
        lower += edgeMap[{edge.u, edge.v}].first;
        usedEdges++;
    }
    // infeasible if there are no such edges
    if (usedEdges < k-node.cntComponents)
        return {INF, INF};

    // auxiliary vector for the random part
    vector<int> vertices(n+1);
    iota(vertices.begin(), vertices.end(), 0);
    random_shuffle(vertices.begin()+1, vertices.end());

    int cntComponentsDiscovered = 0;
    vector<int> rep(n+1, 0);
    fill(rep.begin()+1, rep.end(), 0);
    int l = 0;

    // select the k representants of each connected component
    for (int i = 1; i <= n; ++i) {
        int u = vertices[i];
        if (comp[u] == u) {
            ++cntComponentsDiscovered;
            rep[u] = u;
        }
        else if (l != k - node.cntComponents) {
            int found = 0;
            for (int v = 1; v <= n; ++v) {
                if (!edgeMap.count({min(u, v), max(u, v)})) continue;

                if (node.fixedEdges.count(edgeMap[{min(u, v), max(u, v)}].second)) {
                    found = 1;
                    break;
                }
            }
            if (found) continue;
            ++l;
            rep[u] = u;
        }
    }
    int upper = -1;
    if (l + cntComponentsDiscovered < k) upper = INF;
    if (upper < INF) upper = greedy(node.avEdges, node.fixedEdges, rep);

    return {lower, upper};
}

// Returns the cost of minimum k-cut of a connected graph
// Branch and bound implemented
pair<int, set<edgeSet>> minkcut(set<edgeSet>& avEdges) {

    // initial default values
    int bestCost = INF;
    int nodeIdx = 0;
    set<edgeSet> bestCut;
    set<edgeSet> fixedEdges;

    // struct to store nodes of branch and bound: a binary search tree, used as a heap
    set<Node> heap;
    
    // insert full graph with no restrictions on graphs
    Node root = Node(avEdges);
    root.cntComponents = -1;
    root.bounds = boundFunction(root);
    heap.insert(root);

    // while there is vertex to explore
    while (!heap.empty()) {

        // node with lowest lower bound
        Node node = *heap.begin();
        heap.erase(heap.begin());

        // if all edges are either fixed or prohibited, it's a possible solution
        if (node.avEdges.size() == 0) {

            // if number of connected components is exactly k and node has a better cost, update bestCost 
            if (node.currCost < bestCost and node.cntComponents == k) {
                bestCost = node.currCost;
                bestCut.clear();
                for (int i = 0; i < m; i++)
                    if (!node.fixedEdges.count(i))
                        bestCut.insert(i);
            }
            continue;
        }

        // cut the subtree in case of occurrence of some of these conditions
        if (node.cntComponents > k or node.bounds.lower >= bestCost or node.currCost >= bestCost)
            continue;

        // if lower bound is equal to upper bound, there is no reason to explore subtree
        if (node.bounds.lower == node.bounds.upper) {
            if (node.bounds.lower < bestCost) {
                // printf("node.idx: %d\n", node.idx);
                bestCost = node.bounds.lower;
                bestCut.clear();
                for (int i = 0; i < m; i++)
                    if (!node.fixedEdges.count(i) and !node.avEdges.count(i))
                        bestCut.insert(i);
            }
            continue;
        }

        // next edge to process
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
