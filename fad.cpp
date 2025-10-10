#include <fstream>
#include <iostream>
#include <vector>
#include <set>
#include <unordered_map>
#include <stdio.h>
#include <stdlib.h>
#include <map>
#include <string>
#include <unordered_set>
#include <algorithm>
#include <queue>
#include <functional>
#include <climits>
#include <chrono>
#include <iomanip>
using namespace std;

#define INITIAL -1
#define INITMAX 100000;

int initK = 0;
int initL = 0;
int maxK = 0;
int maxL = 0;
int n = 0;
int m = 0;
int b = 0;
unordered_map<int, int> nodeMapping;
unordered_map<int, int> reverseMapping;
vector<bool> inCoreStorageInitKInitL;
vector<bool> inCoreStorageMaxKMaxL;
vector<int> tempInitialOutDegree_init;
vector<int> tempInitialOutDegree_max;
vector<int> tempInitialInDegree_init;
vector<int> tempInitialInDegree_max;

struct Graph
{
    int V;
    int edgeNum;
    vector<vector<int>> adj;
    vector<vector<int>> revAdj;
    vector<int> initialOutDegree;
    vector<int> initialInDegree;

    Graph() {};
    Graph(int V)
    {
        this->V = V;
        adj.resize(V);
        revAdj.resize(V);
        initialOutDegree.resize(V, 0);
        initialInDegree.resize(V, 0);
    }

    void addEdge(int v, int w)
    {
        initialOutDegree[v]++;
        initialInDegree[w]++;
        adj[v].push_back(w);
        revAdj[w].push_back(v);
    }
};

struct pair_hash
{
    template <class T1, class T2>
    std::size_t operator()(const std::pair<T1, T2> &p) const
    {
        auto h1 = std::hash<T1>{}(p.first);
        auto h2 = std::hash<T2>{}(p.second);
        return h1 ^ (h2 << 1);
    }
};

vector<int> parent;
vector<vector<int>> parentToChildren;
struct DSU
{
    vector<int> parent, rank;
    vector<vector<int>> parentToChildren;

    DSU() {};

    DSU(int n)
    {
        rank.resize(n, 0);
        parentToChildren.resize(n);
        parent.resize(n);
        for (int i = 0; i < n; ++i)
        {
            parent[i] = i;
            parentToChildren[i].push_back(i);
        }
    }

    void clear()
    {
        parent.clear();
        rank.clear();
        parentToChildren.clear();
    }
    int find(int u)
    {
        if (u != parent[u])
        {
            parent[u] = find(parent[u]);
        }
        return parent[u];
    }

    void unite(int u, int v)
    {
        int rootU = find(u);
        int rootV = find(v);
        if (rootU != rootV)
        {
            if (rank[rootU] > rank[rootV])
            {
                parent[rootV] = rootU;
                parentToChildren[rootU].insert(parentToChildren[rootU].end(), parentToChildren[rootV].begin(), parentToChildren[rootV].end());
                parentToChildren[rootV].clear();
            }
            else if (rank[rootU] < rank[rootV])
            {
                parent[rootU] = rootV;
                parentToChildren[rootV].insert(parentToChildren[rootV].end(), parentToChildren[rootU].begin(), parentToChildren[rootU].end());
                parentToChildren[rootU].clear();
            }
            else
            {
                parent[rootV] = rootU;
                parentToChildren[rootU].insert(parentToChildren[rootU].end(), parentToChildren[rootV].begin(), parentToChildren[rootV].end());
                parentToChildren[rootV].clear();
                rank[rootU]++;
            }
        }
    }

    vector<int> getChildrenOfParent(int parent)
    {
        int root = find(parent);
        return parentToChildren[root];
    }
};

struct ShellOrderInfo
{
    DSU dsu;
    vector<int> delete_shell_order;
    vector<int> id2order;
    vector<int> id2layerNum;
    vector<bool> delete_info_isTrue;
    vector<int> layerEnd_loca;

    int layerNum = 0;

    unordered_map<int, vector<int>> components;

    void clear()
    {
        dsu.clear();
        delete_shell_order.clear();
        id2order.clear();
        id2layerNum.clear();
        delete_info_isTrue.clear();
        layerEnd_loca.clear();
        components.clear();
    }
};

Graph G;

vector<bool> anchor_tag;
vector<bool> isAffected;
vector<bool> k_1shell;
vector<bool> l_1shell;

bool previousAnchoredNode_inSHell = true;
int previousAV = -1;
vector<int> previous_cA_MaxFNum_Set;
vector<set<int>> previous_cA_upper_Set;
vector<vector<int>> previous_cA_Nv_set;
unordered_map<int, int> previous_outNVnode2orderSet;
int previous_KL_1_SUM = -1;
vector<int> previous_cAnchore_Set;
unordered_map<int, vector<int>> previous_Anchore_Follow;
vector<bool> previous_delete_info_isTrue;
DSU dsuPrevious;

vector<vector<int>> previous_cA_cAoutNV;
vector<vector<int>> cA_cAoutNV;

vector<int> previous_dsuRootSetOut;

vector<int> dsuRootSetOut;

void readGraphFromFile(const string &filename, unordered_map<int, int> &nodeMapping);
void print_Shell_Core();

vector<int> intersection_hash();
void initializeItem(int maxK, int maxL);

vector<int> intersection_hash(const std::vector<int> &nums1, const std::vector<int> &nums2)
{
    std::unordered_set<int> set1(nums1.begin(), nums1.end());
    std::unordered_set<int> resultSet;

    for (int num : nums2)
    {
        if (set1.find(num) != set1.end())
        {
            resultSet.insert(num);
        }
    }

    return std::vector<int>(resultSet.begin(), resultSet.end());
}

void readGraphFromFile(const string &filename, unordered_map<int, int> &nodeMapping)
{
    ifstream infile(filename);
    if (!infile)
    {
        cerr << "Error opening file." << endl;
        exit(1);
    }

    vector<pair<int, int>> edges;
    unordered_set<string> edgeSet;
    unordered_map<int, int> originalToNew;
    int nodeCount = 0;
    int u, v;
    int flag = 0;
    while (infile >> v >> u)
    {
        originalToNew[v] = (originalToNew.find(v) == originalToNew.end()) ? nodeCount++ : originalToNew[v];
        originalToNew[u] = (originalToNew.find(u) == originalToNew.end()) ? nodeCount++ : originalToNew[u];
        string edgeKey = to_string(originalToNew[v]) + "-" + to_string(originalToNew[u]);

        if (edgeSet.find(edgeKey) == edgeSet.end())
        {
            edgeSet.insert(edgeKey);
            edges.push_back({originalToNew[v], originalToNew[u]});
        }
        else
        {
            flag = 1;
        }
    }
    if (flag == 0)
    {
        cout << "没有重复的" << endl;
    }
    else
    {
        cout << "有重复的" << endl;
    }

    for (const auto &pair : originalToNew)
    {
        reverseMapping[pair.second] = pair.first;
    }

    Graph G1(nodeCount);
    G = G1;
    for (const auto &edge : edges)
    {
        G.addEdge(edge.first, edge.second);
    }
    G.edgeNum = edges.size();
    nodeMapping = move(originalToNew);
    infile.close();
}

void pruneCore(int k, int l, vector<int> &outDegree, vector<int> &inDegree, vector<bool> &inCore)
{
    queue<int> q;

    for (int i = 0; i < G.V; ++i)
    {
        if (anchor_tag[i])
            continue;
        if (inCore[i] && (outDegree[i] < k || inDegree[i] < l))
        {
            q.push(i);
            inCore[i] = false;
        }
    }

    while (!q.empty())
    {
        int v = q.front();
        q.pop();
        for (int u : G.adj[v])
        {
            if (anchor_tag[u])
                continue;
            if (inCore[u])
            {
                inDegree[u]--;
                if (inDegree[u] < l)
                {
                    q.push(u);
                    inCore[u] = false;
                }
            }
        }
        for (int u : G.revAdj[v])
        {
            if (anchor_tag[u])
                continue;
            if (inCore[u])
            {
                outDegree[u]--;
                if (outDegree[u] < k)
                {
                    q.push(u);
                    inCore[u] = false;
                }
            }
        }
    }
}

void pruneCorek_1(int k, int l)
{
    vector<bool> inCore = inCoreStorageInitKInitL;
    vector<int> outDegree;
    outDegree = tempInitialOutDegree_init;
    vector<int> inDegree;
    inDegree = tempInitialInDegree_init;
    queue<int> q;
    k = k - 1;
    for (int i = 0; i < G.V; ++i)
    {
        if (anchor_tag[i])
            continue;
        if (inCore[i] && (outDegree[i] < k || inDegree[i] < l))
        {
            q.push(i);
            inCore[i] = false;
        }
    }

    while (!q.empty())
    {
        int v = q.front();
        q.pop();
        for (int u : G.adj[v])
        {
            if (anchor_tag[u])
                continue;
            if (inCore[u])
            {
                inDegree[u]--;
                if (inDegree[u] < l)
                {
                    q.push(u);
                    inCore[u] = false;
                }
            }
        }
        for (int u : G.revAdj[v])
        {
            if (anchor_tag[u])
                continue;
            if (inCore[u])
            {
                outDegree[u]--;
                if (outDegree[u] < k)
                {
                    q.push(u);
                    inCore[u] = false;
                }
            }
        }
    }
    for (int i = 0; i < G.V; i++)
    {
        if (!inCoreStorageMaxKMaxL[i])
        {
            if (inCore[i])
            {
                k_1shell[i] = true;
            }
        }
    }
}

void pruneCorel_1(int k, int l)
{
    vector<bool> inCore = inCoreStorageInitKInitL;
    vector<int> outDegree;
    outDegree = tempInitialOutDegree_init;
    vector<int> inDegree;
    inDegree = tempInitialInDegree_init;
    queue<int> q;
    l = l - 1;
    for (int i = 0; i < G.V; ++i)
    {
        if (anchor_tag[i])
            continue;
        if (inCore[i] && (outDegree[i] < k || inDegree[i] < l))
        {
            q.push(i);
            inCore[i] = false;
        }
    }

    while (!q.empty())
    {
        int v = q.front();
        q.pop();
        for (int u : G.adj[v])
        {
            if (anchor_tag[u])
                continue;
            if (inCore[u])
            {
                inDegree[u]--;
                if (inDegree[u] < l)
                {
                    q.push(u);
                    inCore[u] = false;
                }
            }
        }
        for (int u : G.revAdj[v])
        {
            if (anchor_tag[u])
                continue;
            if (inCore[u])
            {
                outDegree[u]--;
                if (outDegree[u] < k)
                {
                    q.push(u);
                    inCore[u] = false;
                }
            }
        }
    }
    for (int i = 0; i < G.V; i++)
    {
        if (!inCoreStorageMaxKMaxL[i])
        {
            if (inCore[i])
            {
                l_1shell[i] = true;
            }
        }
    }
}

vector<int> pruneCore1(int k, int l, vector<int> outDegree, vector<int> inDegree, vector<bool> inCore, ShellOrderInfo &shell_KL_1_info)
{
    DSU dsu(G.V);
    shell_KL_1_info.dsu = dsu;
    shell_KL_1_info.layerNum = 0;
    shell_KL_1_info.id2layerNum.resize(G.V, -1);
    shell_KL_1_info.id2order.resize(G.V);
    shell_KL_1_info.delete_info_isTrue.resize(G.V, false);

    queue<int> q;

    int layer_loca = 0;

    for (int i = 0; i < G.V; ++i)
    {
        if (anchor_tag[i])
            continue;
        if (inCore[i] && (outDegree[i] < k || inDegree[i] < l))
        {
            q.push(i);
            inCore[i] = false;
            shell_KL_1_info.delete_shell_order.push_back(i);
            shell_KL_1_info.id2order[i] = layer_loca;
            shell_KL_1_info.id2layerNum[i] = shell_KL_1_info.layerNum;
            shell_KL_1_info.delete_info_isTrue[i] = true;
            layer_loca++;
        }
    }

    shell_KL_1_info.layerEnd_loca.push_back(layer_loca);
    if (q.empty())
    {
        inCoreStorageMaxKMaxL = inCore;
        return shell_KL_1_info.delete_shell_order;
    }

    shell_KL_1_info.layerNum++;

    int qs = q.size();

    while (!q.empty())
    {
        qs--;
        int v = q.front();
        q.pop();

        for (int u : G.adj[v])
        {
            if (anchor_tag[u])
                continue;
            if (shell_KL_1_info.delete_info_isTrue[u])
            {
                shell_KL_1_info.dsu.unite(u, v);
            }

            if (inCore[u])
            {
                inDegree[u]--;
                if (inDegree[u] < l)
                {
                    shell_KL_1_info.dsu.unite(u, v);
                    q.push(u);
                    inCore[u] = false;
                    shell_KL_1_info.delete_shell_order.push_back(u);
                    shell_KL_1_info.delete_info_isTrue[u] = true;
                    shell_KL_1_info.id2order[u] = layer_loca;
                    shell_KL_1_info.id2layerNum[u] = shell_KL_1_info.layerNum;
                    layer_loca++;
                }
            }
        }

        for (int u : G.revAdj[v])
        {
            if (anchor_tag[u])
                continue;
            if (shell_KL_1_info.delete_info_isTrue[u])
            {
                shell_KL_1_info.dsu.unite(u, v);
            }

            if (inCore[u])
            {
                outDegree[u]--;
                if (outDegree[u] < k)
                {
                    shell_KL_1_info.dsu.unite(u, v);
                    q.push(u);
                    inCore[u] = false;
                    shell_KL_1_info.delete_shell_order.push_back(u);
                    shell_KL_1_info.delete_info_isTrue[u] = true;
                    shell_KL_1_info.id2order[u] = layer_loca;
                    shell_KL_1_info.id2layerNum[u] = shell_KL_1_info.layerNum;
                    layer_loca++;
                }
            }
        }

        if (q.size() == 0)
        {
            break;
        }
        if (qs == 0)
        {
            shell_KL_1_info.layerNum++;
            shell_KL_1_info.layerEnd_loca.push_back(layer_loca);
            qs = q.size();
        }
    }

    inCoreStorageMaxKMaxL = inCore;
    return shell_KL_1_info.delete_shell_order;
}

vector<int> orderKL;
ShellOrderInfo shell_KL_1_info;

void bliudSC()
{
    orderKL.clear();
    shell_KL_1_info.clear();
    tempInitialOutDegree_init = G.initialOutDegree;
    tempInitialInDegree_init = G.initialInDegree;
    inCoreStorageInitKInitL.resize(G.V, true);
    inCoreStorageMaxKMaxL.resize(G.V, true);

    pruneCore(initK, initL, tempInitialOutDegree_init, tempInitialInDegree_init, inCoreStorageInitKInitL);

    orderKL = pruneCore1(maxK, maxL, tempInitialOutDegree_init, tempInitialInDegree_init, inCoreStorageInitKInitL, shell_KL_1_info);
    pruneCorek_1(maxK, maxL);
    pruneCorel_1(maxK, maxL);
}

vector<int> shell_order;

vector<vector<int>> adjOrRevAdj;

vector<bool> incore;

int maxCA = -1;
vector<int> max_F_real_set;
vector<int> maxFollowerSetState;
vector<int> isMaxfollowerSetState;
vector<bool> isVisitedF;
vector<bool> inCoreStoragePrevi;

vector<int> cAnchore_Set;
vector<bool> IscAnchore_Set;
vector<int> cA_MaxFNum_Set;
vector<set<int>> cA_upper_Set;
unordered_map<int, int> outNVnode2orderSet;
vector<vector<int>> cA_Nv_set;
vector<vector<int>> cF_num_to_ver;
int remainFollSum = 0;
int KL_1_SUM = 0;

int tempCanFollSize = 0;
int max_FollowerNum = -1;

void computeUpNum(int vOrder)
{
    for (auto isAddV : cA_Nv_set[vOrder])
    {
        cA_upper_Set[vOrder].insert(cA_upper_Set[outNVnode2orderSet.at(isAddV)].begin(), cA_upper_Set[outNVnode2orderSet.at(isAddV)].end());
        cA_upper_Set[vOrder].insert(isAddV);
    }
    cA_MaxFNum_Set[vOrder] = cA_upper_Set[vOrder].size();
}

void computeUpShell(int &maxFollSum)
{
    shell_order.clear();
    adjOrRevAdj.clear();
    incore.clear();

    shell_order = shell_KL_1_info.delete_shell_order;
    int orderLen = KL_1_SUM;
    int tempMaxFv = 0;
    int vOrder = -1;
    int nvOrder = -1;
    int out_CAnchoreSize = 0;

    cA_MaxFNum_Set.resize(orderLen, 0);
    cA_upper_Set.resize(orderLen);
    cA_Nv_set.resize(orderLen, vector<int>(0));
    cA_cAoutNV.resize(orderLen, vector<int>(0));
    IscAnchore_Set.resize(G.V, false);
    for (auto it = shell_order.begin(); it != shell_order.end(); it++)
    {
        cAnchore_Set.push_back(*it);
        outNVnode2orderSet.insert({*it, shell_KL_1_info.id2order[*it]});
    }

    incore = inCoreStorageInitKInitL;

    if (previousAnchoredNode_inSHell)
    {
        int rootPerviousAV = dsuPrevious.find(previousAV);

        for (auto it = shell_order.rbegin(); it != shell_order.rend(); it++)
        {
            int v = *it;
            vOrder = shell_KL_1_info.id2order[v];
            IscAnchore_Set[v] = true;
            int vLayerNum = shell_KL_1_info.id2layerNum[v];

            if (vLayerNum == shell_KL_1_info.layerNum)
            {
                continue;
            }
            int perVorder = previous_outNVnode2orderSet.at(v);
            int vPreviousRoot = dsuPrevious.find(v);
            if (rootPerviousAV != vPreviousRoot && perVorder < previous_KL_1_SUM)
            {
                cA_MaxFNum_Set[vOrder] = previous_cA_MaxFNum_Set[perVorder];
                cA_upper_Set[vOrder] = previous_cA_upper_Set[perVorder];
                cA_Nv_set[vOrder] = previous_cA_Nv_set[perVorder];
                tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]);
            }
            else
            {
                for (auto nv : G.adj[v])
                {
                    if (inCoreStorageMaxKMaxL[nv] || anchor_tag[nv] || isAffected[nv])
                    {
                        continue;
                    }

                    if (shell_KL_1_info.delete_info_isTrue[nv])
                    {
                        if (vLayerNum < shell_KL_1_info.id2layerNum[nv])
                        {
                            cA_Nv_set[vOrder].push_back(nv);
                        }
                    }
                }

                for (auto nv : G.revAdj[v])
                {
                    if (inCoreStorageMaxKMaxL[nv] || anchor_tag[nv] || isAffected[nv])
                    {
                        continue;
                    }

                    if (shell_KL_1_info.delete_info_isTrue[nv])
                    {
                        if (vLayerNum < shell_KL_1_info.id2layerNum[nv])
                        {
                            if (find(cA_Nv_set[vOrder].begin(), cA_Nv_set[vOrder].end(), nv) == cA_Nv_set[vOrder].end())
                            {
                                cA_Nv_set[vOrder].push_back(nv);
                            }
                        }
                    }
                }

                computeUpNum(vOrder);
                tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]);
            }
        }

        vector<int> temp_cA_Nv_set;
        for (int i = previous_KL_1_SUM; i < previous_cAnchore_Set.size(); i++)
        {
            int oV = previous_cAnchore_Set[i];
            temp_cA_Nv_set.clear();

            for (auto cnv : previous_cA_Nv_set[i])
            {
                if (!inCoreStorageMaxKMaxL[cnv])
                {
                    int cnvOrder = shell_KL_1_info.id2order[cnv];
                    cA_cAoutNV[cnvOrder].push_back(oV);
                    temp_cA_Nv_set.push_back(cnv);
                }
            }
            if (temp_cA_Nv_set.size() == 0)
            {
                continue;
            }

            IscAnchore_Set[oV] = true;
            cA_Nv_set.push_back(temp_cA_Nv_set);
            cAnchore_Set.push_back(oV);
            cA_MaxFNum_Set.push_back(0);
            cA_upper_Set.push_back(std::set<int>());
            outNVnode2orderSet.insert({oV, orderLen + out_CAnchoreSize});
            computeUpNum(orderLen + out_CAnchoreSize);
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[orderLen + out_CAnchoreSize]);
            out_CAnchoreSize++;
        }
    }
    else if (maxCA == -1)
    {
        for (auto it = shell_order.rbegin(); it != shell_order.rend(); it++)
        {
            int v = *it;
            IscAnchore_Set[v] = true;
            vOrder = shell_KL_1_info.id2order[v];
            int vLayerNum = shell_KL_1_info.id2layerNum[v];
            if (anchor_tag[v] || isAffected[v])
            {
                continue;
            }

            if (vLayerNum == shell_KL_1_info.layerNum)
            {
                continue;
            }

            for (auto nv : G.adj[v])
            {
                if (inCoreStorageMaxKMaxL[nv] || anchor_tag[nv] || isAffected[nv])
                {
                    continue;
                }

                if (shell_KL_1_info.delete_info_isTrue[nv])
                {
                    if (vLayerNum < shell_KL_1_info.id2layerNum[nv])
                    {
                        cA_Nv_set[vOrder].push_back(nv);
                    }
                }
                else if (!incore[nv])
                {
                    if (!IscAnchore_Set[nv])
                    {
                        if (find(G.revAdj[v].begin(), G.revAdj[v].end(), nv) != G.revAdj[v].end())
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()});
                            cAnchore_Set.push_back(nv);
                            cA_MaxFNum_Set.push_back(0);
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }
                        else if (k_1shell[v])
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()});
                            cAnchore_Set.push_back(nv);
                            cA_MaxFNum_Set.push_back(0);
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }
                    }
                    else
                    {
                        if (find(G.revAdj[v].begin(), G.revAdj[v].end(), nv) != G.revAdj[v].end())
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            nvOrder = outNVnode2orderSet.at(nv);
                            cA_Nv_set[nvOrder].push_back(v);
                        }
                        else if (k_1shell[v])
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            nvOrder = outNVnode2orderSet.at(nv);
                            cA_Nv_set[nvOrder].push_back(v);
                        }
                    }
                }
            }

            for (auto nv : G.revAdj[v])
            {
                if (anchor_tag[nv] || isAffected[nv] || inCoreStorageMaxKMaxL[nv])
                {
                    continue;
                }

                if (shell_KL_1_info.delete_info_isTrue[nv])
                {
                    if (vLayerNum < shell_KL_1_info.id2layerNum[nv])
                    {
                        if (find(cA_Nv_set[vOrder].begin(), cA_Nv_set[vOrder].end(), nv) == cA_Nv_set[vOrder].end())
                        {
                            cA_Nv_set[vOrder].push_back(nv);
                        }
                    }
                }
                else if (!incore[nv])
                {
                    if (!IscAnchore_Set[nv])
                    {
                        if (l_1shell[v])
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()});
                            cAnchore_Set.push_back(nv);
                            cA_MaxFNum_Set.push_back(0);
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }
                    }
                    else
                    {
                        if (l_1shell[v])
                        {
                            if (find(cA_cAoutNV[vOrder].begin(), cA_cAoutNV[vOrder].end(), nv) == cA_cAoutNV[vOrder].end())
                            {
                                cA_cAoutNV[vOrder].push_back(nv);
                            }

                            nvOrder = outNVnode2orderSet.at(nv);
                            if (cA_Nv_set[nvOrder].back() != v)
                            {
                                cA_Nv_set[nvOrder].push_back(v);
                            }
                        }
                    }
                }
            }

            computeUpNum(vOrder);
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]);
        }

        for (int i = orderLen; i < cAnchore_Set.size(); i++)
        {
            computeUpNum(i);
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[i]);
        }
    }
    else
    {
        for (auto it = shell_order.rbegin(); it != shell_order.rend(); it++)
        {
            int v = *it;
            IscAnchore_Set[v] = true;
            vOrder = shell_KL_1_info.id2order[v];
            int vLayerNum = shell_KL_1_info.id2layerNum[v];
            if (anchor_tag[v] || isAffected[v])
            {
                continue;
            }

            if (vLayerNum == shell_KL_1_info.layerNum)
            {
                continue;
            }

            int vPreviousRoot = dsuPrevious.find(v);

            if (previous_delete_info_isTrue[v] &&
                find(previous_dsuRootSetOut.begin(),
                     previous_dsuRootSetOut.end(), vPreviousRoot) == previous_dsuRootSetOut.end())
            {
                int perVorder = previous_outNVnode2orderSet.at(v);
                cA_MaxFNum_Set[vOrder] = previous_cA_MaxFNum_Set[perVorder];
                cA_upper_Set[vOrder] = previous_cA_upper_Set[perVorder];
                cA_Nv_set[vOrder] = previous_cA_Nv_set[perVorder];

                tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]);

                for (auto caOV : previous_cA_cAoutNV[perVorder])
                {
                    cA_cAoutNV[vOrder].push_back(caOV);
                    if (!IscAnchore_Set[caOV])
                    {
                        IscAnchore_Set[caOV] = true;
                        outNVnode2orderSet.insert({caOV, cAnchore_Set.size()});
                        cAnchore_Set.push_back(caOV);
                        cA_MaxFNum_Set.push_back(0);
                        cA_upper_Set.push_back(std::set<int>());
                        cA_Nv_set.push_back({v});
                    }
                    else
                    {
                        int caOVOrder = outNVnode2orderSet.at(caOV);
                        cA_Nv_set[caOVOrder].push_back(v);
                    }
                }
                continue;
            }

            for (auto nv : G.adj[v])
            {
                if (inCoreStorageMaxKMaxL[nv] || anchor_tag[nv] || isAffected[nv])
                {
                    continue;
                }

                if (shell_KL_1_info.delete_info_isTrue[nv])
                {
                    if (vLayerNum < shell_KL_1_info.id2layerNum[nv])
                    {
                        cA_Nv_set[vOrder].push_back(nv);
                    }
                }
                else if (!incore[nv])
                {
                    if (!IscAnchore_Set[nv])
                    {
                        if (find(G.revAdj[v].begin(), G.revAdj[v].end(), nv) != G.revAdj[v].end())
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()});
                            cAnchore_Set.push_back(nv);
                            cA_MaxFNum_Set.push_back(0);
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }
                        else if (k_1shell[v])
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()});
                            cAnchore_Set.push_back(nv);
                            cA_MaxFNum_Set.push_back(0);
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }
                    }
                    else
                    {
                        if (find(G.revAdj[v].begin(), G.revAdj[v].end(), nv) != G.revAdj[v].end())
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            nvOrder = outNVnode2orderSet.at(nv);
                            cA_Nv_set[nvOrder].push_back(v);
                        }
                        else if (k_1shell[v])
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            nvOrder = outNVnode2orderSet.at(nv);
                            cA_Nv_set[nvOrder].push_back(v);
                        }
                    }
                }
            }

            for (auto nv : G.revAdj[v])
            {
                if (anchor_tag[nv] || isAffected[nv] || inCoreStorageMaxKMaxL[nv])
                {
                    continue;
                }

                if (shell_KL_1_info.delete_info_isTrue[nv])
                {
                    if (vLayerNum < shell_KL_1_info.id2layerNum[nv])
                    {
                        if (find(cA_Nv_set[vOrder].begin(), cA_Nv_set[vOrder].end(), nv) == cA_Nv_set[vOrder].end())
                        {
                            cA_Nv_set[vOrder].push_back(nv);
                        }
                    }
                }
                else if (!incore[nv])
                {
                    if (!IscAnchore_Set[nv])
                    {
                        if (l_1shell[v])
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()});
                            cAnchore_Set.push_back(nv);
                            cA_MaxFNum_Set.push_back(0);
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }
                    }
                    else
                    {
                        if (l_1shell[v])
                        {
                            if (find(cA_cAoutNV[vOrder].begin(), cA_cAoutNV[vOrder].end(), nv) == cA_cAoutNV[vOrder].end())
                            {
                                cA_cAoutNV[vOrder].push_back(nv);
                            }

                            nvOrder = outNVnode2orderSet.at(nv);
                            if (cA_Nv_set[nvOrder].back() != v)
                            {
                                cA_Nv_set[nvOrder].push_back(v);
                            }
                        }
                    }
                }
            }

            computeUpNum(vOrder);
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]);
        }

        for (int i = orderLen; i < cAnchore_Set.size(); i++)
        {
            computeUpNum(i);
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[i]);
        }
    }

    maxFollSum = tempMaxFv;
}

int temp_FollowerNum = 0;
vector<int> tempFollowerSet;
vector<int> isTempFollowerSet;
vector<int> tempInDegree;
vector<int> tempOutDegree;

int tempF_real_num = 0;

queue<int> deleteUnavlueFollower;
queue<int> deleteUnavlueFollowerLoca;

void deleteF(vector<int> sl_out, vector<int> sl_in)
{
    {
        for (auto nv : sl_out)
        {
            if (anchor_tag[nv] || isAffected[nv])
            {
                continue;
            }
            else if (isTempFollowerSet[nv] > -1)
            {
                {
                    tempInDegree[nv]--;
                    if (tempInDegree[nv] < maxL)
                    {
                        deleteUnavlueFollowerLoca.push(isTempFollowerSet[nv]);
                        isTempFollowerSet[nv] = -2;
                        deleteUnavlueFollower.push(nv);
                        tempF_real_num--;
                    }
                }
            }
        }
    }
    {
        for (auto nv : sl_in)
        {
            if (anchor_tag[nv] || isAffected[nv])
            {
                continue;
            }
            else if (isTempFollowerSet[nv] > -1)
            {
                {
                    tempOutDegree[nv]--;
                    if (tempOutDegree[nv] < maxK)
                    {
                        deleteUnavlueFollowerLoca.push(isTempFollowerSet[nv]);
                        isTempFollowerSet[nv] = -2;
                        deleteUnavlueFollower.push(nv);
                        tempF_real_num--;
                    }
                }
            }
        }
    }
}

bool computeFollower(int cA)
{
    isTempFollowerSet.clear();
    tempFollowerSet.clear();
    tempInDegree.clear();
    tempOutDegree.clear();
    isTempFollowerSet.resize(G.V, -1);
    tempF_real_num = 0;

    tempInDegree = tempInitialInDegree_max;
    tempOutDegree = tempInitialOutDegree_max;

    tempInDegree[cA] = INITMAX;
    tempOutDegree[cA] = INITMAX;

    int cAorder = -1;
    int vOrder = -1;
    int currentMaxF = -1;
    int cAlayer = shell_KL_1_info.id2layerNum[cA];

    if (IscAnchore_Set[cA])
    {
        cAorder = outNVnode2orderSet.at(cA);
        currentMaxF = cA_MaxFNum_Set[cAorder];

        int tempKL_OutNum = 0;
        int tempKL_InNum = 0;
        int tempAffect_OutNum = 0;
        int tempAffect_InNum = 0;
        int tempUnexplor_outNum = 0;
        int tempUnexplor_inNum = 0;

        vector<vector<int>> unVisitedSet(G.V);

        vector<vector<int>> slOUT(0);
        vector<vector<int>> slIN(0);
        vector<int> slOUT_temp;
        vector<int> slIN_temp;

        int cFSize = 0;

        tempFollowerSet.push_back(cA);
        isTempFollowerSet[cA] = 0;
        anchor_tag[cA] = true;

        unVisitedSet[cA] = cA_Nv_set[outNVnode2orderSet.at(cA)];
        slOUT.push_back(unVisitedSet[cA]);
        slIN.push_back(unVisitedSet[cA]);

        for (int iv = 0; iv < tempFollowerSet.size(); iv++)
        {
            int tfv = tempFollowerSet[iv];

            for (auto v : unVisitedSet[tfv])
            {
                vOrder = outNVnode2orderSet.at(v);
                slOUT_temp.clear();
                slIN_temp.clear();

                tempKL_OutNum = 0;
                tempKL_InNum = 0;
                tempAffect_OutNum = 0;
                tempAffect_InNum = 0;
                tempUnexplor_inNum = 0;
                tempUnexplor_outNum = 0;

                if (anchor_tag[v] || isAffected[v])
                {
                    continue;
                }
                if (isTempFollowerSet[v] != -1)
                {
                    continue;
                }

                for (int nv : G.adj[v])
                {
                    if (nv == cA || inCoreStorageMaxKMaxL[nv])
                    {
                        tempKL_OutNum++;
                    }
                    else if (inCoreStorageInitKInitL[nv])
                    {
                        if (isTempFollowerSet[nv] > -1)
                        {
                            tempAffect_OutNum++;
                            slOUT_temp.push_back(nv);
                        }
                        else if (isTempFollowerSet[nv] == -1 && shell_KL_1_info.id2layerNum[nv] > cAlayer)
                        {
                            unVisitedSet[v].push_back(nv);
                            slOUT_temp.push_back(nv);
                            tempUnexplor_outNum++;
                        }
                    }
                }

                for (int nv : G.revAdj[v])
                {
                    if (nv == cA || inCoreStorageMaxKMaxL[nv])
                    {
                        tempKL_InNum++;
                    }
                    else if (inCoreStorageInitKInitL[nv])
                    {
                        if (isTempFollowerSet[nv] > -1)
                        {
                            slIN_temp.push_back(nv);
                            tempAffect_InNum++;
                        }
                        else if (isTempFollowerSet[nv] == -1 && shell_KL_1_info.id2layerNum[nv] > cAlayer)
                        {
                            unVisitedSet[v].push_back(nv);
                            slIN_temp.push_back(nv);
                            tempUnexplor_inNum++;
                        }
                    }
                }

                if ((tempKL_OutNum + tempAffect_OutNum + tempUnexplor_outNum) >= maxK &&
                    (tempKL_InNum + tempAffect_InNum + tempUnexplor_inNum) >= maxL)
                {
                    cFSize++;
                    tempInDegree[v] = tempKL_InNum + tempAffect_InNum + tempUnexplor_inNum;
                    tempOutDegree[v] = tempKL_OutNum + tempAffect_OutNum + tempUnexplor_outNum;

                    tempFollowerSet.push_back(v);
                    tempF_real_num++;
                    isTempFollowerSet[v] = cFSize;

                    slOUT.push_back(slOUT_temp);
                    slIN.push_back(slIN_temp);
                }
                else
                {
                    unVisitedSet[v].clear();
                    isTempFollowerSet[v] = -2;

                    deleteF(slOUT_temp, slIN_temp);

                    while (!deleteUnavlueFollower.empty())
                    {
                        int vF = deleteUnavlueFollower.front();
                        deleteUnavlueFollower.pop();

                        int vFOrder = deleteUnavlueFollowerLoca.front();
                        deleteUnavlueFollowerLoca.pop();

                        deleteF(slOUT[vFOrder], slIN[vFOrder]);
                        slOUT[vFOrder].clear();
                        slIN[vFOrder].clear();
                    }
                }
            }
        }

        anchor_tag[cA] = false;
        temp_FollowerNum = tempF_real_num;
        return true;
    }
    return false;
}

void initializeItem()
{
    std::fill(inCoreStorageInitKInitL.begin(), inCoreStorageInitKInitL.end(), true);
    std::fill(inCoreStorageMaxKMaxL.begin(), inCoreStorageMaxKMaxL.end(), true);
    std::fill(tempInitialOutDegree_init.begin(), tempInitialOutDegree_init.end(), 0);
    std::fill(tempInitialOutDegree_max.begin(), tempInitialOutDegree_max.end(), 0);
    std::fill(tempInitialInDegree_init.begin(), tempInitialInDegree_init.end(), 0);
    std::fill(tempInitialInDegree_max.begin(), tempInitialInDegree_max.end(), 0);
    std::fill(IscAnchore_Set.begin(), IscAnchore_Set.end(), false);
    std::fill(isVisitedF.begin(), isVisitedF.end(), false);

    cAnchore_Set.clear();
    cA_MaxFNum_Set.clear();
    cA_upper_Set.clear();
    outNVnode2orderSet.clear();
    cA_Nv_set.clear();
    cF_num_to_ver.clear();

    remainFollSum = 0;
    KL_1_SUM = 0;
    max_FollowerNum = -1;

    maxFollowerSetState.clear();
    isMaxfollowerSetState.clear();

    inCoreStoragePrevi.clear();

    cA_cAoutNV.clear();
}

int main(int argc, char *argv[])
{

    const string filename = string(argv[1]) + ".txt";

    double begin_time = clock();
    readGraphFromFile(filename, nodeMapping);
    double end_time = clock();
    int follower_size = 0;
    cout << "finish reading graph, time: " << (end_time - begin_time) / CLOCKS_PER_SEC << endl;
    std::ofstream outfile("fad_" + string(argv[1]) + ".txt", std::ios::app);
    if (!outfile.is_open())
    {
        std::cout << "文件创建失败" << std::endl;
    }
    auto now = std::chrono::system_clock::now();
    std::time_t now_time = std::chrono::system_clock::to_time_t(now);
    string dataName = string(argv[1]);

    maxK = stoi(argv[2]);
    maxL = stoi(argv[3]);
    int bmax = stoi(argv[4]);
    b = bmax;
    initK = max(maxK - 1, 0);
    initL = max(maxL - 1, 0);
    n = G.V;
    m = G.edgeNum;
    cout << "点数：" << n << " 边数：" << m << endl;
    anchor_tag.resize(G.V, false);
    isAffected.resize(G.V, false);
    k_1shell.resize(G.V, false);
    l_1shell.resize(G.V, false);
    double begin_time1 = clock();
    outfile << "----------------------------FAD算法----------------------------" << endl;
    outfile << "\t\t\t\t\t\t" << std::ctime(&now_time) << endl;
    outfile << "数据集：" << filename << endl;
    outfile << "节点数：\t" << n << endl;
    outfile << "边数：\t" << m << endl;
    outfile << "K：\t" << maxK << endl;
    outfile << "L：\t" << maxL << endl;

    inCoreStorageInitKInitL.resize(n, true);
    inCoreStorageMaxKMaxL.resize(n, true);

    tempInitialOutDegree_init.resize(n, 0);
    tempInitialOutDegree_max.resize(n, 0);
    tempInitialInDegree_init.resize(n, 0);
    tempInitialInDegree_max.resize(n, 0);
    IscAnchore_Set.resize(G.V, false);
    isVisitedF.resize(G.V, false);
    vector<bool> dsustate(n, false);

    while (b--)
    {
        cout << "-------------剩余次数:" << b << "---------------" << endl;

        if (maxCA == -1)
        {
            cout << "第一次锚定呀" << endl;
            previousAnchoredNode_inSHell = false;
        }
        else if (shell_KL_1_info.delete_info_isTrue[maxCA])
        {
            previous_cA_MaxFNum_Set.clear();
            previous_cA_upper_Set.clear();
            previous_cA_Nv_set.clear();
            previous_outNVnode2orderSet.clear();
            previous_cAnchore_Set.clear();
            dsuPrevious.clear();
            previous_cA_cAoutNV.clear();
            cout << "锚定的是内部的节点呀" << endl;
            previousAnchoredNode_inSHell = true;
            previous_cA_MaxFNum_Set = cA_MaxFNum_Set;
            previous_cA_upper_Set = cA_upper_Set;
            previous_cA_Nv_set = cA_Nv_set;
            previous_outNVnode2orderSet = outNVnode2orderSet;
            previous_KL_1_SUM = KL_1_SUM;
            previousAV = maxCA;
            previous_cAnchore_Set = cAnchore_Set;
            dsuPrevious = shell_KL_1_info.dsu;
            previous_delete_info_isTrue = shell_KL_1_info.delete_info_isTrue;
        }
        else
        {
            previous_cA_MaxFNum_Set.clear();
            previous_cA_upper_Set.clear();
            previous_cA_Nv_set.clear();
            previous_outNVnode2orderSet.clear();
            previous_cAnchore_Set.clear();
            dsuPrevious.clear();
            previous_cA_cAoutNV.clear();
            cout << "锚定的是外部的节点呀" << endl;
            previousAnchoredNode_inSHell = false;
            previous_cA_MaxFNum_Set = cA_MaxFNum_Set;
            previous_cA_upper_Set = cA_upper_Set;
            previous_cA_Nv_set = cA_Nv_set;
            previous_outNVnode2orderSet = outNVnode2orderSet;
            previous_KL_1_SUM = KL_1_SUM;
            previousAV = maxCA;
            previous_cAnchore_Set = cAnchore_Set;
            dsuPrevious = shell_KL_1_info.dsu;
            previous_delete_info_isTrue = shell_KL_1_info.delete_info_isTrue;
            previous_dsuRootSetOut = dsuRootSetOut;
            previous_cA_cAoutNV = cA_cAoutNV;
        }

        initializeItem();

        begin_time = clock();
        double t1 = clock();
        bliudSC();
        inCoreStoragePrevi = inCoreStorageMaxKMaxL;
        bool flag = false;
        if (orderKL.size() == 0)
        {
            cout << "随便选个点添加咯。" << endl;
            for (int i = 0; i < G.V; i++)
            {
                if (!inCoreStorageMaxKMaxL[i])
                {
                    flag=true;
                    maxCA = i;
                    cout << "随便选个点添加咯。" << endl;
                    break;
                }
            }
        }
        else
        {
            double t2 = clock();
            cout << "计算k-core的时间：Elapsed time:\t" << (t2 - t1) / CLOCKS_PER_SEC << " s" << std::endl;
            KL_1_SUM = shell_KL_1_info.delete_shell_order.size();

            computeUpShell(remainFollSum);
            double t3 = clock();
            cout << "计算shell和上界的时间：Elapsed time:\t" << (t3 - t2) / CLOCKS_PER_SEC << " s" << std::endl;
            cout << "shell：\t" << orderKL.size() << endl;
            cout << "L：\t" << cAnchore_Set.size() << endl;

            cout << remainFollSum << " " << KL_1_SUM << endl;
            remainFollSum = min(remainFollSum, KL_1_SUM);

            cF_num_to_ver.resize(remainFollSum + 1);

            for (int i = 0; i < cAnchore_Set.size(); i++)
            {
                tempCanFollSize = cA_MaxFNum_Set[i];
                cF_num_to_ver[tempCanFollSize].push_back(cAnchore_Set[i]);
            }

            double t4 = clock();
            cout << "计算排序：Elapsed time:\t" << (t4 - t3) / CLOCKS_PER_SEC << " s" << std::endl;
            int cot = 0;
            int dian = 0;
            vector<int> tempSet;
            while (remainFollSum)
            {
                if (max_FollowerNum < remainFollSum)
                {
                    for (auto cA : cF_num_to_ver[remainFollSum])
                    {
                        if (isVisitedF[cA])
                        {
                            continue;
                        }
                        cot++;
                        auto it = previous_Anchore_Follow.find(cA);
                        if (it != previous_Anchore_Follow.end() && dsuPrevious.find(previousAV) != dsuPrevious.find(cA))
                        {
                            int sizeN = it->second.size();
                            if (sizeN > max_FollowerNum)
                            {
                                maxCA = cA;
                                max_F_real_set = it->second;
                                max_FollowerNum = sizeN - 1;

                                if (sizeN >= remainFollSum)
                                {
                                    previous_Anchore_Follow.erase(cA);
                                    break;
                                }

                                for (auto v : it->second)
                                {
                                    isVisitedF[v] = true;
                                }
                            }
                            continue;
                        }

                        temp_FollowerNum = 0;

                        if (computeFollower(cA))
                        {
                            dian += tempFollowerSet.size();
                            tempSet.clear();
                            for (auto v : tempFollowerSet)
                            {
                                if (isTempFollowerSet[v] > -1)
                                {
                                    tempSet.push_back(v);
                                    if (!isVisitedF[v])
                                    {
                                        isVisitedF[v] = true;
                                    }
                                }
                            }
                            if (shell_KL_1_info.delete_info_isTrue[cA])
                            {
                                previous_Anchore_Follow.insert({cA, tempSet});
                            }
                            if (max_FollowerNum < temp_FollowerNum)
                            {
                                max_F_real_set.clear();
                                maxCA = cA;
                                max_FollowerNum = temp_FollowerNum;
                                max_F_real_set = tempSet;

                                if (max_FollowerNum >= remainFollSum)
                                {
                                    break;
                                }
                            }
                        }
                    }
                }
                else
                {
                    break;
                }
                remainFollSum--;
            }
            cout << "计算锚点的追随者次数：" << cot << endl;
            cout << "遍历追随者点数：" << dian << endl;
            if (max_FollowerNum == -1)
            {
                max_F_real_set.clear();
                maxFollowerSetState.clear();
                maxCA = shell_KL_1_info.delete_shell_order[KL_1_SUM - 1];
                anchor_tag[maxCA] = true;
                isAffected[maxCA] = true;
                maxFollowerSetState.push_back(maxCA);
                max_FollowerNum = 0;
                max_F_real_set.push_back(maxCA);
                cout << "---呦吼,没有随机挑选，所以肯定存在出入，莫要在意，  是对的" << endl;
            }

            int rootMaxCA = shell_KL_1_info.dsu.find(maxCA);
            int outvorder = outNVnode2orderSet.at(maxCA);
            if (outvorder >= orderKL.size())
            {
                std::fill(dsustate.begin(), dsustate.end(), false);
                dsuRootSetOut.clear();
                int root;

                for (auto upV : cA_Nv_set[outvorder])
                {
                    root = shell_KL_1_info.dsu.find(upV);
                    if (!dsustate[root])
                    {
                        dsustate[root] = true;
                        dsuRootSetOut.push_back(root);
                        for (auto vdsu : shell_KL_1_info.dsu.parentToChildren[root])
                        {
                            previous_Anchore_Follow.erase(vdsu);
                        }
                    }
                }
                cout << endl;
            }
            else
            {
                for (auto vdsu : shell_KL_1_info.dsu.parentToChildren[rootMaxCA])
                {
                    previous_Anchore_Follow.erase(vdsu);
                }
            }

            double t5 = clock();
            cout << "计算锚点时间：Elapsed time:\t" << (t5 - t4) / CLOCKS_PER_SEC << " s" << std::endl;
            cout << "\n\n";
            cout << "@@@锚点：" << reverseMapping.at(maxCA) << "跟随者数量：" << max_F_real_set.size() << " 跟随者：";
            follower_size += max_FollowerNum;
            for (auto v : max_F_real_set)
            {
                isAffected[v] = true;
                cout << reverseMapping.at(v) << " ";
            }
            cout << endl;
        }

        if (flag==false){
            outfile << "所有顶点已在("<<maxK<<","<<maxL<<")-core中" << endl;
            break;
        }
        anchor_tag[maxCA] = true;
        end_time = clock();

        outfile << "b：\t" << bmax - b << endl;
        outfile << "anchor：\t" << reverseMapping.at(maxCA) << endl;
        outfile << "follower：\t" << follower_size << endl;
        double end_time1 = clock();
        outfile << "计算锚定的时间：Elapsed time:\t" << (end_time1 - begin_time1) / CLOCKS_PER_SEC << " s" << std::endl;
        
    }

    double end_time1 = clock();
    cout << "computeUpShell, time: " << (end_time1 - begin_time1) / CLOCKS_PER_SEC << endl;
    cout << "\n\n";
    outfile << "程序结束\n\n";
    outfile.close();

    return 0;
}
