#include <fstream>
#include <iostream>
#include <vector>
#include <set>
#include <unordered_map>
#include <stdio.h>
#include <stdlib.h>
// #include <sys/resource.h>
#include <map>

#include <unordered_set>
#include <algorithm>
#include <queue>
#include <functional>
#include <climits>
#include <chrono>
using namespace std;

/***
 * @attention 去重上界版贪心
 *
 * 运行时间直接从7s提升到了0.5s
 *
 * 直接按照 林老师的方法进行代码的撰写。
 *
 * @date 2024年8月28日 2024年8月28日22:04:26
 * @brief print_Shell_Core(); //打印shell_core
 * @brief vector<int> intersection_hash();//求解shell的交集，用于避免无效的存储
 * @brief bliudSC();计算每个(k,l)-集合的同时计算索引结构
 * @brief DSU中存在： find(v)、unite(u,v)、computeComponents(inCore)、addNode(u,components)
 */

#define INITIAL -1
#define INITMAX 100000;

/**
 * 基础(k,l)-core求解过程中的信息
 */
int initK = 0;
int initL = 0;
int maxK = 0;
int maxL = 0;
int n = 0; // 点数:G.V
int m = 0; // 边数:G.edgeNum
int b = 0;
unordered_map<int, int> nodeMapping;
unordered_map<int, int> reverseMapping;
vector<bool> inCoreStorageInitKInitL;
vector<bool> inCoreStorageMaxKMaxL;
vector<int> tempInitialOutDegree_init; // 出度：存储k向每个(k,l)节点的出度数，可以用于存储每个(k,l)节点的剩余出度数情况
vector<int> tempInitialOutDegree_max;  // 入度：存储k向每个(k,l)节点的入度数，可以用于存储每个(k,l)节点的剩余入度数情况

vector<int> tempInitialInDegree_init; // 出度：存储k向每个(k,l)节点的出度数，可以用于存储每个(k,l)节点的剩余出度数情况
vector<int> tempInitialInDegree_max;

struct Graph // 原始图结构
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

// 自定义哈希函数
struct pair_hash
{
    template <class T1, class T2>
    std::size_t operator()(const std::pair<T1, T2> &p) const
    {
        auto h1 = std::hash<T1>{}(p.first);
        auto h2 = std::hash<T2>{}(p.second);
        // 组合两个哈希值
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

            parentToChildren[i].push_back(i); // 初始化每个节点为自己的子节点
        }
    }

    void clear()
    {
        parent.clear(); // 组件状态
        rank.clear();
        parentToChildren.clear();
    }
    int find(int u) // 寻找父节点
    {
        if (u != parent[u])
        {
            parent[u] = find(parent[u]);
        }
        return parent[u];
    }

    void unite(int u, int v) // 对比修改08了unite
    {
        int rootU = find(u);
        int rootV = find(v);
        if (rootU != rootV)
        {
            if (rank[rootU] > rank[rootV])
            {
                parent[rootV] = rootU;
                parentToChildren[rootU].insert(parentToChildren[rootU].end(), parentToChildren[rootV].begin(), parentToChildren[rootV].end()); // 合并树
                // parentToChildren.erase(rootV);
                parentToChildren[rootV].clear(); // 清空已合并的子节点                                                                                        // 删除旧父节点的数据，用于获取最终的每个联通组件的父节点，
            }
            else if (rank[rootU] < rank[rootV])
            {
                parent[rootU] = rootV;
                parentToChildren[rootV].insert(parentToChildren[rootV].end(), parentToChildren[rootU].begin(), parentToChildren[rootU].end());
                // parentToChildren.erase(rootU); // 删除旧父节点的数据,可以确保最后的parents就是每个连通组件的结果，但是删除时间太久了。所以保留
                parentToChildren[rootU].clear(); // 清空已合并的子节点
            }
            else
            { // 如果秩相等，新的树的高度增加 1
                parent[rootV] = rootU;
                parentToChildren[rootU].insert(parentToChildren[rootU].end(), parentToChildren[rootV].begin(), parentToChildren[rootV].end());
                // parentToChildren.erase(rootV); // 删除旧父节点的数据
                parentToChildren[rootV].clear(); // 清空已合并的子节点
                rank[rootU]++;
            }
        }
    }

    // 获取父亲节点对应的孩子节点
    vector<int> getChildrenOfParent(int parent)
    {
        int root = find(parent);
        return parentToChildren[root];
    }
};

struct ShellOrderInfo
{
    DSU dsu;                         // 组件状态
    vector<int> delete_shell_order;  // 删除顺序  等价于属性：shellStorage
    vector<int> id2order;            // 节点在 delete_shell_order 的第几个
    vector<int> id2layerNum;         // 节点在的层级
    vector<bool> delete_info_isTrue; // 节点的删除状态，true为删除
    vector<int> layerEnd_loca;       // 层级，每一层开始的位置。
    // vector<int> foll_upperValue;     // 跟随者的上限值

    int layerNum = 0; // 层数

    unordered_map<int, vector<int>> components; // 当前组件的连通性

    void clear()
    {
        dsu.clear();
        delete_shell_order.clear(); // 删除顺序  等价于属性：shellStorage
        id2order.clear();           // 节点在 delete_shell_order 的第几个
        id2layerNum.clear();        // 节点在的层级
        delete_info_isTrue.clear(); // 节点的删除状态，true为删除
        layerEnd_loca.clear();      // 层级，每一层开始的位置。
        // foll_upperValue.clear();    // 跟随者的上限值
        components.clear();
    }
};

Graph G; // 图

/**
 * 锚定和跟随者时计算的信息
 */
vector<bool> anchor_tag; // 标记节点是否为锚定节点
vector<bool> isAffected; // 是否是受影响(跟随者)节点
vector<bool> k_1shell;   // 是否是(k-1,l)shell
vector<bool> l_1shell;   // 是否是(k,l-1)shell
/***
 * 重用跟随者上界
 * */

bool previousAnchoredNode_inSHell = true;            // 上一轮锚定顶点的状态,   ture:在上一个shell中， false:是外部顶点
int previousAV = -1;                                 // 上一轮的候选锚点
vector<int> previous_cA_MaxFNum_Set;                 // 上一轮最大跟随者数量
vector<set<int>> previous_cA_upper_Set;              // 上一轮最大跟随者数量
vector<vector<int>> previous_cA_Nv_set;              // 上一轮候选邻居集合
unordered_map<int, int> previous_outNVnode2orderSet; // 内外部跟随者所在候选锚定点cAnchore_Set 中的位置，v对应的vOrder
int previous_KL_1_SUM = -1;                          // 前一轮的shell的长度。
vector<int> previous_cAnchore_Set;
unordered_map<int, vector<int>> previous_Anchore_Follow; // （候选锚，实际跟随者）记录上轮部分已经得到的实际跟随者的锚点及其信息，
// unordered_map<int, vector<int>> Anchore_Follow;
vector<bool> previous_delete_info_isTrue; // 上一轮中的节点是都是shell中的
DSU dsuPrevious;

vector<vector<int>> previous_cA_cAoutNV; // 上一轮（候选锚vorder，外部邻居nv）
vector<vector<int>> cA_cAoutNV;          // （候选锚vorder，候选外部邻居锚点nv）

vector<int> previous_dsuRootSetOut; // 上轮锚定的外部节点，存储的外部节点影响的组件

vector<int> dsuRootSetOut; // 外部候选锚点影响的组件

/**读取或打印*/
void readGraphFromFile(const string &filename, unordered_map<int, int> &nodeMapping);
void readGraphFromFile(const string &filename, const string outfilename, unordered_map<int, int> &nodeMapping);

void print_Shell_Core(); // 打印shell_core

/**共用基础函数*/
vector<int> intersection_hash();         // 求解shell的交集，用于避免无效的存储
void initializeItem(int maxK, int maxL); // 初始化元素项目

// hash求交集
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

void readGraphFromFile(const string &filename, const string outfilename, unordered_map<int, int> &nodeMapping)
{
    ifstream infile(filename);
    if (!infile)
    {
        cerr << "Error opening file." << endl;
        exit(1);
    }

    std::ofstream outfile(outfilename, std::ios::app); // 打开文件用于追加
    if (!outfile.is_open())
    {
        std::cout << "文件创建失败" << std::endl;
    }
    std::cout << "文件创建成功" << std::endl;
    vector<pair<int, int>> edges;
    unordered_set<string> edgeSet; // 用字符串存储边，方便查重
    unordered_map<int, int> originalToNew;
    int nodeCount = 0;
    int u, v;
    int flag = 0;
    outfile << "id1" << "," << "id2" << endl;
    while (infile >> v >> u)
    {
        originalToNew[v] = (originalToNew.find(v) == originalToNew.end()) ? nodeCount++ : originalToNew[v];
        originalToNew[u] = (originalToNew.find(u) == originalToNew.end()) ? nodeCount++ : originalToNew[u];
        // 构造唯一标识（例如 "u-v"）
        string edgeKey = to_string(originalToNew[v]) + "-" + to_string(originalToNew[u]);

        // 如果边不存在，则加入 edges 和 edgeSet
        outfile << v << "," << u << endl;
        if (edgeSet.find(edgeKey) == edgeSet.end())
        {
            edgeSet.insert(edgeKey);
            edges.push_back({originalToNew[v], originalToNew[u]});
        }
        else
        { // 有 重复的 输出一下让我看看
            flag = 1;
            // cout << edgeKey << endl;
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

    // Create reverse mapping for output purposes
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
    outfile.close();
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
    unordered_set<string> edgeSet; // 用字符串存储边，方便查重
    unordered_map<int, int> originalToNew;
    int nodeCount = 0;
    int u, v;
    int flag = 0;
    while (infile >> v >> u)
    {
        originalToNew[v] = (originalToNew.find(v) == originalToNew.end()) ? nodeCount++ : originalToNew[v];
        originalToNew[u] = (originalToNew.find(u) == originalToNew.end()) ? nodeCount++ : originalToNew[u];
        // 构造唯一标识（例如 "u-v"）
        string edgeKey = to_string(originalToNew[v]) + "-" + to_string(originalToNew[u]);

        // 如果边不存在，则加入 edges 和 edgeSet
        if (edgeSet.find(edgeKey) == edgeSet.end())
        {
            edgeSet.insert(edgeKey);
            edges.push_back({originalToNew[v], originalToNew[u]});
        }
        else
        { // 有 重复的 输出一下让我看看
            flag = 1;
            // cout << edgeKey << endl;
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

    // Create reverse mapping for output purposes
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

/***
 * @brief 求解每个core元素，并用shell_layer记录每个元素所在的core 和层级。
 * @param flag:true向下，false向左
 * @param deleteK_info_isTrue:true当前被删除
 *
 */
// 分解过程
void pruneCore(int k, int l, vector<int> &outDegree, vector<int> &inDegree, vector<bool> &inCore)
{

    queue<int> q;

    for (int i = 0; i < G.V; ++i)
    {

        if (anchor_tag[i])
            continue;
        if (inCore[i] && (outDegree[i] < k || inDegree[i] < l))
        {

            q.push(i); // 记录结点
            inCore[i] = false;
        }
    }

    while (!q.empty())
    {

        int v = q.front();
        q.pop();
        // 出度节点进行操作
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
        // 入度节点进行操作
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
    // inCore.resize(G.V, true);
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
            q.push(i); // 记录结点
            inCore[i] = false;
        }
    }

    while (!q.empty())
    {

        int v = q.front();
        q.pop();
        // 出度节点进行操作
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
        // 入度节点进行操作
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
    // 算出了k-1core，那么现在要算k-1shell
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
    // inCore.resize(G.V, true);
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
            q.push(i); // 记录结点
            inCore[i] = false;
        }
    }

    while (!q.empty())
    {

        int v = q.front();
        q.pop();
        // 出度节点进行操作
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
        // 入度节点进行操作
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
    // 算出了l-1core，那么现在要算l-1shell
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
// 计算k-1，l-1.的顺序
// 分析：layerEnd_loca[0]是第一层的节点数量，layerEnd_loca[1]是第二层和第一层的节点数量
// 分析：layerNum是最高层，比如现在shell有两层，那么layerNum为2
vector<int> pruneCore1(int k, int l, vector<int> outDegree, vector<int> inDegree, vector<bool> inCore, ShellOrderInfo &shell_KL_1_info)
{

    DSU dsu(G.V);
    shell_KL_1_info.dsu = dsu;
    // shell_KL_1_info.delete_shell_order = order;
    // shell_KL_1_info.layerEnd_loca = layerEnd_loca;
    // shell_KL_1_info.layerNum = layer_num;
    shell_KL_1_info.layerNum = 0;
    shell_KL_1_info.id2layerNum.resize(G.V, -1);
    // shell_KL_1_info.id2order = id2orderTemp;
    shell_KL_1_info.id2order.resize(G.V);
    shell_KL_1_info.delete_info_isTrue.resize(G.V, false);

    queue<int> q;

    int layer_loca = 0; // 当前层级节点数量

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
        return shell_KL_1_info.delete_shell_order;
    }

    shell_KL_1_info.layerNum++; // 层级加1

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
            if (shell_KL_1_info.delete_info_isTrue[u]) // 已经在第一轮删除了
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
            if (shell_KL_1_info.delete_info_isTrue[u]) // 已经在第一轮删除了
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

    // inCoreStorage[maxK][maxL] = inCore;
    inCoreStorageMaxKMaxL = inCore;

    return shell_KL_1_info.delete_shell_order;
}

vector<int> orderKL;
ShellOrderInfo shell_KL_1_info;
void bliudSC()
{
    orderKL.clear();
    shell_KL_1_info.clear();
    // 初始化(initK,initL)
    tempInitialOutDegree_init = G.initialOutDegree;
    tempInitialInDegree_init = G.initialInDegree;
    // inCoreStorage[initK][initL].resize(G.V, true);

    // inCoreStorage[maxK][maxL].resize(G.V, true);
    inCoreStorageInitKInitL.resize(G.V, true);
    inCoreStorageMaxKMaxL.resize(G.V, true);

    pruneCore(initK, initL, tempInitialOutDegree_init, tempInitialInDegree_init, inCoreStorageInitKInitL); // 计算klcore

    // tempInitialOutDegree_init[nodeMapping.at(171770)] = INITMAX;
    // tempInitialInDegree_init[nodeMapping.at(171770)] = INITMAX;

    orderKL = pruneCore1(maxK, maxL, tempInitialOutDegree_init, tempInitialInDegree_init, inCoreStorageInitKInitL, shell_KL_1_info); // 返回的是删除节点的顺序，并且计算出inCoreStorageMaxKMaxL
    pruneCorek_1(maxK, maxL);
    pruneCorel_1(maxK, maxL);
    // for (auto v : orderKL)
    // {
    //     cout << v << " ";
    // }
    // cout << endl;
}

vector<int> shell_order; // shell中的顺序

vector<vector<int>> adjOrRevAdj;

vector<bool> incore;

/***为计算上层shell做准备 */
int maxCA = -1;                    // 当前最大跟随者的锚点
vector<int> max_F_real_set;        // 当前最大跟随者的锚点的真实跟随者
vector<int> maxFollowerSetState;   // 最大跟随者集合z状态，-2不行。-1未遍历，>-1成功
vector<int> isMaxfollowerSetState; // 影响K向临时跟随者集合; >=0是跟随者集合
vector<bool> isVisitedF;           // 在当前b中是已经求得元素的跟随者。
vector<bool> inCoreStoragePrevi;   // 上一轮的maxK,maxL

/**
 * 下面是为计算候选锚点和候选跟随者做准备
 */
vector<int> cAnchore_Set;                   // 候选锚点集合，对应v； kl:0,  k-1(L):1， l-1(K):2。
vector<bool> IscAnchore_Set;                // 是否是候选锚点集合，初始为false 对应v ， kl:0,  k-1(L):1， l-1(K):2。
vector<int> cA_MaxFNum_Set;                 // 候选锚对应的最大跟随者数量，对应vOrder
vector<set<int>> cA_upper_Set;              // 候选锚对应的最大跟随者“集合”，对应vOrder
unordered_map<int, int> outNVnode2orderSet; // 内外部跟随者所在候选锚定点cAnchore_Set 中的位置，v对应的vOrder
vector<vector<int>> cA_Nv_set;              // 候选锚的 候选跟随者邻居，，对应vOrder，和nv
vector<vector<int>> cF_num_to_ver;          // 每个跟随者数量下 有哪些候选锚点
int remainFollSum = 0;                      // 记录3个shell 所有锚点中最大的跟随数量
int KL_1_SUM = 0;                           // 记录(k-1，l-1)-shell中的节点数量

int tempCanFollSize = 0;  // 临时记录每个v的最大跟随者数量
int max_FollowerNum = -1; // 当前最大跟随者数量

void computeUpNum(int vOrder) // 去重版本
{

    for (auto isAddV : cA_Nv_set[vOrder]) // 判断节点v 是不是 比他小的order的邻居
    {
        cA_upper_Set[vOrder].insert(cA_upper_Set[outNVnode2orderSet.at(isAddV)].begin(), cA_upper_Set[outNVnode2orderSet.at(isAddV)].end());
        cA_upper_Set[vOrder].insert(isAddV);
    }
    cA_MaxFNum_Set[vOrder] = cA_upper_Set[vOrder].size();
    // cout << vOrder << "上层顶点数：" << upvn << " 计算顶点数：" << cA_MaxFNum_Set[vOrder] << endl;
}

/**  开始计算上界
 *
 * @param IscAnchoreSet(G.V):是否是候选锚点，对应v
 * @param cAnchoreSet(0) :候选锚点集合 push，对应v
 * @param cA_max_FNum_set(0)    :候选锚对应的最大跟随者数量，对应vOrder
 * @param cA_FNvSet(0)，cA_Nv_set    :候选锚的 候选跟随者邻居，remainFollSumnv
 * @param outNVnode2orderSet 外部邻居顶点集合出现的顺序 unordered_map<int, int>，v对应的vOrder
 */
void computeUpShell(int &maxFollSum)
{
    shell_order.clear();
    adjOrRevAdj.clear();
    incore.clear();

    // 初始化
    shell_order = shell_KL_1_info.delete_shell_order; // 删除的顺序
    int orderLen = KL_1_SUM;                          // shell中节点数量
    int tempMaxFv = 0;                                // 临时记录最大跟随者数量，maxFollSum=tempMaxFv
    int vOrder = -1;                                  // 节点v的order顺序
    int nvOrder = -1;
    int out_CAnchoreSize = 0; // 外部候选锚点的数量

    cA_MaxFNum_Set.resize(orderLen, 0);
    cA_upper_Set.resize(orderLen);
    cA_Nv_set.resize(orderLen, vector<int>(0)); // 这是内部节点，后续还要push外部节点
    cA_cAoutNV.resize(orderLen, vector<int>(0));
    IscAnchore_Set.resize(G.V, false); // 锚点标记
    for (auto it = shell_order.begin(); it != shell_order.end(); it++)
    {
        cAnchore_Set.push_back(*it);                                     // 这是内部节点，后续还要push外部节点
        outNVnode2orderSet.insert({*it, shell_KL_1_info.id2order[*it]}); // 外部邻居 出现的位置
    }

    incore = inCoreStorageInitKInitL; // k-1，l-1core

    if (previousAnchoredNode_inSHell) // 锚定的是内部节点。可以重用
    {
        // cout << "上一轮锚定的是内部的节点：" << reverseMapping.at(previousAV) << endl;
        // cout << "本轮涉及的节点如下：" << endl;
        int rootPerviousAV = dsuPrevious.find(previousAV); // 上一轮锚点的组件的根

        for (auto it = shell_order.rbegin(); it != shell_order.rend(); it++)
        {

            int v = *it;
            vOrder = shell_KL_1_info.id2order[v]; // 点v的所在的顺序的位置（下标）。
            IscAnchore_Set[v] = true;
            int vLayerNum = shell_KL_1_info.id2layerNum[v]; // 节点v所在的层级

            // 条件0,  最后一层级没有跟随者数量，所以直接跳过
            if (vLayerNum == shell_KL_1_info.layerNum) // 只有后面层级有可能成为v的跟随者
            {
                continue;
            }
            int perVorder = previous_outNVnode2orderSet.at(v); // 上一轮节点v所在的顺序。

            int vPreviousRoot = dsuPrevious.find(v);                              // v在上一轮中的根。
            if (rootPerviousAV != vPreviousRoot && perVorder < previous_KL_1_SUM) // 不在一个组件中，且不是上一轮的外部邻接点，（因为外部连接点可能链接到了受影响的组件）那么可以重用上轮的结果呀
            {
                cA_MaxFNum_Set[vOrder] = previous_cA_MaxFNum_Set[perVorder];
                cA_upper_Set[vOrder] = previous_cA_upper_Set[perVorder];
                cA_Nv_set[vOrder] = previous_cA_Nv_set[perVorder];
                tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]); // 记录拥有最大的跟随者数的数量。
            }
            else // 在一个shell中或者影响了需要重新计算上界。
            {
                // IscAnchore_Set[v] = true;
                for (auto nv : G.adj[v]) // 邻居节点
                {
                    if (inCoreStorageMaxKMaxL[nv] || anchor_tag[nv] || isAffected[nv])
                    {
                        continue;
                    }

                    if (shell_KL_1_info.delete_info_isTrue[nv]) // 是否存在于本shell中。  注释掉是因为，在同一个shell中，v的邻居u一定和v在同一个组件里面
                    {

                        if (vLayerNum < shell_KL_1_info.id2layerNum[nv]) // 其邻居会因其锚定而增加度数。  或者   v所在的层级的最后一个点的位置，比邻居节点的层级低。
                        {

                            // cout << "\t候选节点：" << reverseMapping.at(nv) << endl;
                            cA_Nv_set[vOrder].push_back(nv); // 记录节点的跟随者集合 的order顺序
                            // cout << reverseMapping.at(nv) << " ";
                        }
                    }
                }

                for (auto nv : G.revAdj[v]) // 邻居节点
                {

                    if (inCoreStorageMaxKMaxL[nv] || anchor_tag[nv] || isAffected[nv])
                    {
                        continue;
                    }

                    if (shell_KL_1_info.delete_info_isTrue[nv]) // 是否存在于本shell中。  注释掉是因为，在同一个shell中，v的邻居u一定和v在同一个组件里面
                    {
                        // nvOrder = shell_KL_1_info.id2order[nv];

                        if (vLayerNum < shell_KL_1_info.id2layerNum[nv]) // 其邻居会因其锚定而增加度数。  或者   v所在的层级的最后一个点的位置，比邻居节点的层级低。
                        {

                            // if (find(cA_Nv_set[vOrder].begin(), cA_Nv_set[vOrder].end(), nv) == cA_Nv_set[vOrder].end())
                            if (find(cA_Nv_set[vOrder].begin(), cA_Nv_set[vOrder].end(), nv) == cA_Nv_set[vOrder].end())
                            {
                                // cout << "\t候选节点：" << reverseMapping.at(nv) << endl;
                                // cout << reverseMapping.at(nv) << " ";
                                cA_Nv_set[vOrder].push_back(nv); // 记录节点的跟随者集合 的order顺序
                                                                 // cout << "跟随者数:" << cA_MaxFNum_Set[vOrder] << "(跟随者邻居" << cA_Nv_set[vOrder].size() << ")" << "跟随者：" << reverseMapping.at(nv);
                            }
                        }
                    }
                }

                computeUpNum(vOrder);                               // 计算上层数值
                tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]); // 记录拥有最大的跟随者数的数量。
                // cout << "新计算节点:" << reverseMapping.at(v);
                // cout << "上限为:" << cA_MaxFNum_Set[vOrder] << endl;

                // cout << "-" << reverseMapping.at(v) << "的上限为：" << cA_MaxFNum_Set[vOrder] << "-" << endl;
                // cout << reverseMapping.at(v) << " ";
            }
        }

        vector<int> temp_cA_Nv_set;                                            // 临时结果，如果没有，那就不需要添加
        for (int i = previous_KL_1_SUM; i < previous_cAnchore_Set.size(); i++) // 上一轮的外部节点和当前轮次几乎咩有新的变化
        {
            int oV = previous_cAnchore_Set[i]; // 外部节点oV
            // int pVOrder = previous_outNVnode2orderSet.at(oV); // 外部节点先前节点oVorder

            temp_cA_Nv_set.clear();

            for (auto cnv : previous_cA_Nv_set[i])
            {

                if (!inCoreStorageMaxKMaxL[cnv]) // 外部节点v的邻居cnv不在kl中才能添加
                {

                    int cnvOrder = shell_KL_1_info.id2order[cnv];
                    cA_cAoutNV[cnvOrder].push_back(previous_cAnchore_Set[i]);
                    temp_cA_Nv_set.push_back(cnv);
                }
            }
            if (temp_cA_Nv_set.size() == 0)
            {
                continue;
            }

            // 满足条件了那就添加吧。
            IscAnchore_Set[oV] = true;
            cA_Nv_set.push_back(temp_cA_Nv_set);
            cAnchore_Set.push_back(oV);
            cA_MaxFNum_Set.push_back(0);
            cA_upper_Set.push_back(std::set<int>());
            outNVnode2orderSet.insert({oV, orderLen + out_CAnchoreSize}); // 外部邻居 出现的位置
            // cout << "temp_cA_Nv_set.size:" << temp_cA_Nv_set.size() << " ---- " << cA_Nv_set[orderLen + out_CAnchoreSize].size() << endl;

            computeUpNum(orderLen + out_CAnchoreSize);
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[orderLen + out_CAnchoreSize]);
            // cout << "vOrder:" << vOrder << "  " << reverseMapping.at(cAnchore_Set[i]) << "的上限为：" << cA_MaxFNum_Set[i] << endl;

            // cout << reverseMapping.at(oV) << " ";
            out_CAnchoreSize++;
        }
    }
    else if (maxCA == -1) // 第一次锚定
    {

        for (auto it = shell_order.rbegin(); it != shell_order.rend(); it++)
        {

            int v = *it;
            // cout << "---------------候选锚点：" << reverseMapping.at(v) << "可能加入的跟随者邻居----------" << endl;

            IscAnchore_Set[v] = true;

            vOrder = shell_KL_1_info.id2order[v]; // 点v的所在的顺序的位置（下标）。

            int vLayerNum = shell_KL_1_info.id2layerNum[v]; // 节点v所在的层级
            if (anchor_tag[v] || isAffected[v])             // 已经锚定了，或者已经是跟随者了
            {
                continue;
            }

            // 条件0,  最后一层级没有跟随者数量，所以直接跳过
            if (vLayerNum == shell_KL_1_info.layerNum)
            {
                continue;
            }

            for (auto nv : G.adj[v]) // 邻居节点
            {

                // cout << "11111111________" << reverseMapping.at(nv) << endl;
                if (inCoreStorageMaxKMaxL[nv] || anchor_tag[nv] || isAffected[nv])
                {

                    continue;
                }

                if (shell_KL_1_info.delete_info_isTrue[nv]) // 是否存在于本shell中。  注释掉是因为，在同一个shell中，v的邻居u一定和v在同一个组件里面
                {

                    if (vLayerNum < shell_KL_1_info.id2layerNum[nv]) // 其邻居会因其锚定而增加度数。  或者   v所在的层级的最后一个点的位置，比邻居节点的层级低。
                    {

                        // cout << "\t候选节点：" << reverseMapping.at(nv) << endl;
                        cA_Nv_set[vOrder].push_back(nv); // 记录节点的跟随者集合 的order顺序
                        // cout << reverseMapping.at(nv) << " ";
                    }
                }

                else if (!incore[nv]) // 表示不出现在(k-1  OR  l-1)-core中的   【外部】候选节点
                {

                    // cout << "\t\t外部点：" << reverseMapping.at(nv) << endl;

                    if (!IscAnchore_Set[nv]) // 没有遍历过的候选锚定
                    {
                        if (find(G.revAdj[v].begin(), G.revAdj[v].end(), nv) != G.revAdj[v].end())
                        { // 要求它是出度入度都有的邻居
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()}); // 外部邻居 出现的位置

                            cAnchore_Set.push_back(nv); // 现在增加的是 外部的节点

                            cA_MaxFNum_Set.push_back(0); // 现在初始化的是 外部节点的最大跟随者数量。
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }
                        else if (k_1shell[v]) // k-1shell的情况下就可以
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()}); // 外部邻居 出现的位置

                            cAnchore_Set.push_back(nv); // 现在增加的是 外部的节点

                            cA_MaxFNum_Set.push_back(0); // 现在初始化的是 外部节点的最大跟随者数量。
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }

                        // out_CAnchoreNum++; // 现在增加外部节点
                    }
                    else // 被记为候选锚点了直接添加邻居信息
                    {
                        cA_cAoutNV[vOrder].push_back(nv);
                        // cout << orderLen << "总大小。、" << cA_Nv_set.size() << " , 第i个：" << outNVnode2orderSet.at(nv) << endl;
                        nvOrder = outNVnode2orderSet.at(nv);
                        // if (find(cA_Nv_set[nvOrder].begin(), cA_Nv_set[nvOrder].end(), v) == cA_Nv_set[nvOrder].end())

                        cA_Nv_set[nvOrder].push_back(v);
                    }
                }
            }

            for (auto nv : G.revAdj[v]) // 邻居节点
            {
                // cout << "2222222________" << reverseMapping.at(nv) << endl;

                if (anchor_tag[nv] || isAffected[nv] || inCoreStorageMaxKMaxL[nv])
                {

                    continue;
                }

                if (shell_KL_1_info.delete_info_isTrue[nv]) // 是否存在于本shell中。  注释掉是因为，在同一个shell中，v的邻居u一定和v在同一个组件里面
                {
                    // nvOrder = shell_KL_1_info.id2order[nv];

                    if (vLayerNum < shell_KL_1_info.id2layerNum[nv]) // 其邻居会因其锚定而增加度数。  或者   v所在的层级的最后一个点的位置，比邻居节点的层级低。
                    {

                        if (find(cA_Nv_set[vOrder].begin(), cA_Nv_set[vOrder].end(), nv) == cA_Nv_set[vOrder].end())
                        {
                            // cout << "\t候选节点：" << reverseMapping.at(nv) << endl;
                            // cout << reverseMapping.at(nv) << " ";
                            cA_Nv_set[vOrder].push_back(nv); // 记录节点的跟随者集合 的order顺序
                                                             // cout << "跟随者数:" << cA_MaxFNum_Set[vOrder] << "(跟随者邻居" << cA_Nv_set[vOrder].size() << ")" << "跟随者：" << reverseMapping.at(nv);
                        }
                    }
                }
                else if (!incore[nv]) // 表示不出现在(k-1  OR  l-1)-core中的   【外部】候选节点
                {

                    // cout << "\t\t外部点：" << reverseMapping.at(nv) << endl;
                    if (!IscAnchore_Set[nv]) // 没有遍历过的候选锚定
                    {
                        if (l_1shell[v]) // 是l-1shell
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()}); // 外部邻居 出现的位置

                            cAnchore_Set.push_back(nv); // 现在增加的是 外部的节点

                            cA_MaxFNum_Set.push_back(0); // 现在初始化的是 外部节点的最大跟随者数量。
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }

                        // out_CAnchoreNum++; // 现在增加外部节点
                    }
                    else // 被记为候选锚点了直接添加邻居信息
                    {
                        if (find(cA_cAoutNV[vOrder].begin(), cA_cAoutNV[vOrder].end(), nv) == cA_cAoutNV[vOrder].end())
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                        }

                        nvOrder = outNVnode2orderSet.at(nv);
                        // if (find(cA_Nv_set[nvOrder].begin(), cA_Nv_set[nvOrder].end(), v) == cA_Nv_set[nvOrder].end())
                        if (cA_Nv_set[nvOrder].back() != v) // 在v的出度时，没有加入v，就直接加入。
                        {
                            cA_Nv_set[nvOrder].push_back(v);
                        }
                    }
                }
            }

            computeUpNum(vOrder);                               // 计算上层数值
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]); // 记录拥有最大的跟随者数的数量。
            // if (reverseMapping.at(cAnchore_Set[vOrder]) == 1647230)
            //     cout << "-" << reverseMapping.at(cAnchore_Set[vOrder]) << "的上限为：" << cA_MaxFNum_Set[vOrder] << "-" << endl;
            // cout << "-" << reverseMapping.at(v) << "的上限为：" << cA_MaxFNum_Set[vOrder] << "-" << endl;
        }

        for (int i = orderLen; i < cAnchore_Set.size(); i++)
        {
            // cout << "---------------候选锚点：" << reverseMapping.at(cAnchore_Set[i]) << "可能加入的跟随者邻居----------" << endl;
            // for (auto iiiiii : cA_Nv_set[i])
            //     cout << reverseMapping.at(iiiiii) << " ";
            computeUpNum(i); // 计算上层数值
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[i]);
            // if (reverseMapping.at(cAnchore_Set[i]) == 1647230)
            //     cout << "-" << reverseMapping.at(cAnchore_Set[i]) << "的上限为：" << cA_MaxFNum_Set[i] << "-" << endl;
            // cout << "vOrder:" << vOrder << "  " << reverseMapping.at(cAnchore_Set[i]) << "的上限为：" << cA_MaxFNum_Set[i] << endl;
        }
    }
    else // 锚定的是外部顶点
    {
        for (auto it = shell_order.rbegin(); it != shell_order.rend(); it++)
        {

            int v = *it;
            // cout << "---------------候选锚点：" << reverseMapping.at(v) << "可能加入的跟随者邻居----------" << endl;

            IscAnchore_Set[v] = true;

            vOrder = shell_KL_1_info.id2order[v]; // 点v的所在的顺序的位置（下标）。

            int vLayerNum = shell_KL_1_info.id2layerNum[v]; // 节点v所在的层级
            if (anchor_tag[v] || isAffected[v])             // 已经锚定了，或者已经是跟随者了
            {
                continue;
            }

            // 条件0,  最后一层级没有跟随者数量，所以直接跳过
            if (vLayerNum == shell_KL_1_info.layerNum)
            {
                continue;
            }

            int vPreviousRoot = dsuPrevious.find(v); // 候选锚点上一轮的根节点。

            if (previous_delete_info_isTrue[v] &&
                find(previous_dsuRootSetOut.begin(),
                     previous_dsuRootSetOut.end(), vPreviousRoot) == previous_dsuRootSetOut.end())
            // 候选v在上一轮节点shell中，
            // 且不在上轮锚点的跟随者的组件中，所以不受影响
            {

                int perVorder = previous_outNVnode2orderSet.at(v); // 上一轮节点v所在的顺序。
                cA_MaxFNum_Set[vOrder] = previous_cA_MaxFNum_Set[perVorder];
                cA_upper_Set[vOrder] = previous_cA_upper_Set[perVorder];
                cA_Nv_set[vOrder] = previous_cA_Nv_set[perVorder];
                // 上层节点限制
                // int upvn = INITMAX;
                // if (vOrder >= orderKL.size())
                // {
                //     upvn = orderKL.size();
                // }
                // else
                // {
                //     int originvvID = shell_KL_1_info.delete_shell_order[vOrder];
                //     upvn = shell_KL_1_info.layerEnd_loca[shell_KL_1_info.layerNum - 1] -
                //            shell_KL_1_info.layerEnd_loca[shell_KL_1_info.id2layerNum[originvvID]];
                // }
                // if (upvn < cA_MaxFNum_Set[vOrder])
                // {
                //     cA_MaxFNum_Set[vOrder] = upvn;
                // }

                tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]); // 记录拥有最大的跟随者数的数量。

                for (auto caOV : previous_cA_cAoutNV[perVorder]) // 之前影响的外部节点的邻居
                {

                    cA_cAoutNV[vOrder].push_back(caOV);
                    if (!IscAnchore_Set[caOV])
                    {

                        IscAnchore_Set[caOV] = true;
                        outNVnode2orderSet.insert({caOV, cAnchore_Set.size()}); // 外部邻居 出现的位置

                        cAnchore_Set.push_back(caOV); // 现在增加的是 外部的节点

                        cA_MaxFNum_Set.push_back(0); // 现在初始化的是 外部节点的最大跟随者数量。
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

            for (auto nv : G.adj[v]) // 邻居节点
            {

                // cout << "11111111________" << reverseMapping.at(nv) << endl;
                if (inCoreStorageMaxKMaxL[nv] || anchor_tag[nv] || isAffected[nv])
                {

                    continue;
                }

                if (shell_KL_1_info.delete_info_isTrue[nv]) // 是否存在于本shell中。  注释掉是因为，在同一个shell中，v的邻居u一定和v在同一个组件里面
                {

                    if (vLayerNum < shell_KL_1_info.id2layerNum[nv]) // 其邻居会因其锚定而增加度数。  或者   v所在的层级的最后一个点的位置，比邻居节点的层级低。
                    {

                        // cout << "\t候选节点：" << reverseMapping.at(nv) << endl;
                        cA_Nv_set[vOrder].push_back(nv); // 记录节点的跟随者集合 的order顺序
                        // cout << reverseMapping.at(nv) << " ";
                    }
                }

                else if (!incore[nv]) // 表示不出现在(k-1  OR  l-1)-core中的   【外部】候选节点
                {

                    // cout << "\t\t外部点：" << reverseMapping.at(nv) << endl;

                    if (!IscAnchore_Set[nv]) // 没有遍历过的候选锚定
                    {

                        if (find(G.revAdj[v].begin(), G.revAdj[v].end(), nv) != G.revAdj[v].end())
                        { // 要求它是出度入度都有的邻居
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()}); // 外部邻居 出现的位置

                            cAnchore_Set.push_back(nv); // 现在增加的是 外部的节点

                            cA_MaxFNum_Set.push_back(0); // 现在初始化的是 外部节点的最大跟随者数量。
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }
                        else if (k_1shell[v]) // k-1shell的情况下就可以
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()}); // 外部邻居 出现的位置

                            cAnchore_Set.push_back(nv); // 现在增加的是 外部的节点

                            cA_MaxFNum_Set.push_back(0); // 现在初始化的是 外部节点的最大跟随者数量。
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }

                        // out_CAnchoreNum++; // 现在增加外部节点
                    }
                    else // 被记为候选锚点了直接添加邻居信息
                    {
                        cA_cAoutNV[vOrder].push_back(nv);
                        nvOrder = outNVnode2orderSet.at(nv);
                        // if (find(cA_Nv_set[nvOrder].begin(), cA_Nv_set[nvOrder].end(), v) == cA_Nv_set[nvOrder].end())

                        cA_Nv_set[nvOrder].push_back(v);
                    }
                }
            }

            for (auto nv : G.revAdj[v]) // 邻居节点
            {
                // cout << "2222222________" << reverseMapping.at(nv) << endl;

                if (anchor_tag[nv] || isAffected[nv] || inCoreStorageMaxKMaxL[nv])
                {

                    continue;
                }

                if (shell_KL_1_info.delete_info_isTrue[nv]) // 是否存在于本shell中。  注释掉是因为，在同一个shell中，v的邻居u一定和v在同一个组件里面
                {
                    // nvOrder = shell_KL_1_info.id2order[nv];

                    if (vLayerNum < shell_KL_1_info.id2layerNum[nv]) // 其邻居会因其锚定而增加度数。  或者   v所在的层级的最后一个点的位置，比邻居节点的层级低。
                    {

                        if (find(cA_Nv_set[vOrder].begin(), cA_Nv_set[vOrder].end(), nv) == cA_Nv_set[vOrder].end())
                        {
                            // cout << "\t候选节点：" << reverseMapping.at(nv) << endl;
                            // cout << reverseMapping.at(nv) << " ";
                            cA_Nv_set[vOrder].push_back(nv); // 记录节点的跟随者集合 的order顺序
                                                             // cout << "跟随者数:" << cA_MaxFNum_Set[vOrder] << "(跟随者邻居" << cA_Nv_set[vOrder].size() << ")" << "跟随者：" << reverseMapping.at(nv);
                        }
                    }
                }
                else if (!incore[nv]) // 表示不出现在(k-1  OR  l-1)-core中的   【外部】候选节点
                {

                    // cout << "\t\t外部点：" << reverseMapping.at(nv) << endl;
                    if (!IscAnchore_Set[nv]) // 没有遍历过的候选锚定
                    {
                        if (l_1shell[v]) // 是l-1shell
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                            IscAnchore_Set[nv] = true;
                            outNVnode2orderSet.insert({nv, cAnchore_Set.size()}); // 外部邻居 出现的位置

                            cAnchore_Set.push_back(nv); // 现在增加的是 外部的节点

                            cA_MaxFNum_Set.push_back(0); // 现在初始化的是 外部节点的最大跟随者数量。
                            cA_upper_Set.push_back(std::set<int>());
                            cA_Nv_set.push_back({v});
                        }

                        // out_CAnchoreNum++; // 现在增加外部节点
                    }
                    else // 被记为候选锚点了直接添加邻居信息
                    {
                        if (find(cA_cAoutNV[vOrder].begin(), cA_cAoutNV[vOrder].end(), nv) == cA_cAoutNV[vOrder].end())
                        {
                            cA_cAoutNV[vOrder].push_back(nv);
                        }

                        nvOrder = outNVnode2orderSet.at(nv);
                        // if (find(cA_Nv_set[nvOrder].begin(), cA_Nv_set[nvOrder].end(), v) == cA_Nv_set[nvOrder].end())
                        if (cA_Nv_set[nvOrder].back() != v) // 在v的出度时，没有加入v，就直接加入。
                        {
                            cA_Nv_set[nvOrder].push_back(v);
                        }
                    }
                }
            }

            computeUpNum(vOrder);                               // 计算上层数值
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[vOrder]); // 记录拥有最大的跟随者数的数量。
        }

        for (int i = orderLen; i < cAnchore_Set.size(); i++)
        {

            computeUpNum(i); // 计算上层数值
            tempMaxFv = max(tempMaxFv, cA_MaxFNum_Set[i]);
        }
    }

    // }
    maxFollSum = tempMaxFv;
}

int temp_FollowerNum = 0;      // 临时跟随者数量
vector<int> tempFollowerSet;   // 临时跟随者集合
vector<int> isTempFollowerSet; // 是否是临时跟随者 -1不是 ,0-G.V表示插入的位置, -2表示失效的节点
vector<int> tempInDegree;      // 临时入度
vector<int> tempOutDegree;     // 临时出度

int tempF_real_num = 0; // 临时跟随者  真实的跟随者数量

queue<int> deleteUnavlueFollower;     // 从cF中删除的节点集合
queue<int> deleteUnavlueFollowerLoca; // 从cF中删除的节点集合的order位置
/***
 * 计算跟随者
 * @param removeFromF // 删除因为其他节点受影响的跟随者，不满足度数的节点
 * @param rmfLocal 记录removeFromF中节点的顺序值
 */
void deleteF(vector<int> sl_out, vector<int> sl_in)
{
    // if (outOrIn) // 是删除节点v的出度邻居nv， 因此是nv的入度数-1
    {
        for (auto nv : sl_out) // 受影响的节点
        {

            if (anchor_tag[nv] || isAffected[nv])
            {
                continue;
            }

            else if (isTempFollowerSet[nv] > -1) // 被处理过且在跟随者集合中
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
    // else // 是v的入度邻居nv，v邻居节点nv的出度受影响-1。
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

    /***
     * 下面是为了避免重复的声明
     */
    int cAorder = -1;                              // 记录cA所在？节点的顺序
    int vOrder = -1;                               // 上层节点的顺序
    int currentMaxF = -1;                          // 当前剩余最大跟随数量
    int cAlayer = shell_KL_1_info.id2layerNum[cA]; // cA所在的层级（初始化为-1）， 其跟随者一定是要比cA的层级高。

    if (IscAnchore_Set[cA]) // 是00候选锚点集合
    {

        // 找候选跟随者，并且判断他们的邻居是不是满足hindex。
        //     如果满足就遍历
        //         如果不满足，就候选跟随者删除，
        //             并且跟随者的候选数量也同时减少。
        cAorder = outNVnode2orderSet.at(cA);
        currentMaxF = cA_MaxFNum_Set[cAorder]; // 上界跟随数量

        /***
         * initK initL 向节点出度和入度指向的位置。
         */
        int tempKL_OutNum = 0;       // 临时maxKmaxL or 锚点 跟随者 的中出度数
        int tempKL_InNum = 0;        // 临时maxKmaxL or 锚点 跟随者 的中入度数
        int tempAffect_OutNum = 0;   // 临时受当前跟随者影响出的数量
        int tempAffect_InNum = 0;    // 临时受当前跟随者影响入的数量
        int tempUnexplor_outNum = 0; // 临时未探索的出度数量
        int tempUnexplor_inNum = 0;  // 临时未探索的入度数量

        // 从锚定节点 cA 开始  检测上层跟随者

        vector<vector<int>> unVisitedSet(G.V); // 没有探索过的节点。初始为锚点的上层邻居

        vector<vector<int>> slOUT(0); // 同层受影响的出度节点
        vector<vector<int>> slIN(0);  // 同层受影响的入度节点
        vector<int> slOUT_temp;       // 同层受影响的出度节点
        vector<int> slIN_temp;        // 同层受影响的入度节点

        int cFSize = 0; // 加入q的跟随者位置

        tempFollowerSet.push_back(cA); // 第一个是锚点
        isTempFollowerSet[cA] = 0;
        anchor_tag[cA] = true; // 后续如果不是锚点需要改变

        unVisitedSet[cA] = cA_Nv_set[outNVnode2orderSet.at(cA)];
        slOUT.push_back(unVisitedSet[cA]);
        slIN.push_back(unVisitedSet[cA]);

        //     cout << "---候选点" << reverseMapping.at(cA) << "涉及的所有可能的节点：----" << endl;

        for (int iv = 0; iv < tempFollowerSet.size(); iv++)
        {
            int tfv = tempFollowerSet[iv];

            //     cout << "遍历过的点：" << reverseMapping.at(tfv) << endl;

            for (auto v : unVisitedSet[tfv]) // 初始为锚点的上层邻居，cA_Nv_set,其他的就不包括了
            {
                vOrder = outNVnode2orderSet.at(v);
                slOUT_temp.clear();
                slIN_temp.clear();

                tempKL_OutNum = 0;       // 临时出度数
                tempKL_InNum = 0;        // 临时入度数
                tempAffect_OutNum = 0;   // 临时受跟随者影响出的数量
                tempAffect_InNum = 0;    // 临时受跟随者影响入的数量
                tempUnexplor_inNum = 0;  // 临时
                tempUnexplor_outNum = 0; //

                if (anchor_tag[v] || isAffected[v]) // 是已经被锚定的， 或者已经是跟随者了，不能成为新的跟随着
                {
                    continue;
                }
                if (isTempFollowerSet[v] != -1) // 临时已经被锚定了,或者已经丢弃了，不需要处理
                {
                    continue;
                }

                for (int nv : G.adj[v])
                {

                    //     cout << "出?" << reverseMapping.at(nv) << "?";
                    if (nv == cA || inCoreStorageMaxKMaxL[nv]) // 是锚点，是maxK，maxL中的节点所以一定增加
                    {
                        tempKL_OutNum++;

                        //     cout << "O ";
                    }
                    else if (inCoreStorageInitKInitL[nv]) // 是initK initK中的节点
                    {
                        if (isTempFollowerSet[nv] > -1) // >-1是当前候选跟随者中的节点
                        {
                            tempAffect_OutNum++;
                            slOUT_temp.push_back(nv);

                            //     cout << "√ ";
                        }
                        else if (isTempFollowerSet[nv] == -1 && shell_KL_1_info.id2layerNum[nv] > cAlayer) // = -1是没有探索过的节点，且层级要大于cA的层级
                        {
                            unVisitedSet[v].push_back(nv);
                            slOUT_temp.push_back(nv);
                            tempUnexplor_outNum++;

                            //     cout << "X ";
                        }
                    }
                }

                //     cout << endl;

                for (int nv : G.revAdj[v]) // 出度邻居检测，是否满足 maxk maxl
                {

                    //     cout << "入?" << reverseMapping.at(nv) << "?";

                    if (nv == cA || inCoreStorageMaxKMaxL[nv])
                    {
                        tempKL_InNum++;

                        //     cout << "O ";
                    }
                    else if (inCoreStorageInitKInitL[nv])
                    {
                        if (isTempFollowerSet[nv] > -1) // 已经探索 临时存在
                        {
                            slIN_temp.push_back(nv);
                            tempAffect_InNum++;

                            //     cout << "√ ";
                        }
                        else if (isTempFollowerSet[nv] == -1 && shell_KL_1_info.id2layerNum[nv] > cAlayer) // 未探索
                        {

                            unVisitedSet[v].push_back(nv);

                            slIN_temp.push_back(nv);
                            tempUnexplor_inNum++;

                            //     cout << "X ";
                        }
                    }
                }

                // cout << endl;

                if ((tempKL_OutNum + tempAffect_OutNum + tempUnexplor_outNum) >= maxK &&
                    (tempKL_InNum + tempAffect_InNum + tempUnexplor_inNum) >= maxL) // 满足kl约束条件了，就添加到受影响的节点

                {

                    //     cout << reverseMapping.at(v) << "被加入了" << endl;
                    cFSize++; //  =0是表示锚点
                    tempInDegree[v] = tempKL_InNum + tempAffect_InNum + tempUnexplor_inNum;
                    tempOutDegree[v] = tempKL_OutNum + tempAffect_OutNum + tempUnexplor_outNum;

                    tempFollowerSet.push_back(v);
                    tempF_real_num++;
                    isTempFollowerSet[v] = cFSize;

                    slOUT.push_back(slOUT_temp);
                    slIN.push_back(slIN_temp);
                }
                else // 不满足条件不加入，同时同层因其 影响的节点也删除掉
                {

                    //     cout << reverseMapping.at(v) << "不成功 为-2" << endl;
                    unVisitedSet[v].clear();
                    isTempFollowerSet[v] = -2; // 不满足条件被删除的节点

                    // currentMaxF -= cA_MaxFNum_Set[vOrder] + 1;
                    // if (currentMaxF < max_FollowerNum)
                    // {
                    //     anchor_tag[cA] = false; // 再复原

                    // // 其实是没有复原这个deleteUnavlueFollower
                    //     return false;
                    // }

                    // cout << " trm.size();: " << trm.size() << endl;
                    // if (deleteUnavlueFollower.size() > 0)
                    // {
                    //     cout << "好小子出问题了！！！！！！！" << endl;
                    // }

                    // deleteF(slOUT_temp, true);
                    // deleteF(slIN_temp, false);

                    deleteF(slOUT_temp, slIN_temp);

                    while (!deleteUnavlueFollower.empty())
                    {
                        // if (currentMaxF - cA_MaxFNum_Set[vOrder] < max_FollowerNum)
                        // {
                        //     anchor_tag[cA] = false; // 再复原
                        //     return false;
                        // }
                        int vF = deleteUnavlueFollower.front();
                        deleteUnavlueFollower.pop();

                        int vFOrder = deleteUnavlueFollowerLoca.front();
                        deleteUnavlueFollowerLoca.pop();

                        // deleteF(slOUT[vFOrder], true);
                        // deleteF(slIN[vFOrder], false);
                        deleteF(slOUT[vFOrder], slIN[vFOrder]);
                        slOUT[vFOrder].clear();
                        slIN[vFOrder].clear();
                    }
                }
            }
        }

        anchor_tag[cA] = false; // 再复原
        temp_FollowerNum = tempF_real_num;
        return true;
    }

    return false;
}

void initializeItem()
{

    // 由于 n 和 G.V 不会改变，所有固定大小的容器已经在构造函数中初始化。
    // 因此，这里只需重置容器内容。

    // 使用 std::fill 重置容器内容
    std::fill(inCoreStorageInitKInitL.begin(), inCoreStorageInitKInitL.end(), true);
    std::fill(inCoreStorageMaxKMaxL.begin(), inCoreStorageMaxKMaxL.end(), true);
    std::fill(tempInitialOutDegree_init.begin(), tempInitialOutDegree_init.end(), 0);
    std::fill(tempInitialOutDegree_max.begin(), tempInitialOutDegree_max.end(), 0);
    std::fill(tempInitialInDegree_init.begin(), tempInitialInDegree_init.end(), 0);
    std::fill(tempInitialInDegree_max.begin(), tempInitialInDegree_max.end(), 0);
    std::fill(IscAnchore_Set.begin(), IscAnchore_Set.end(), false);
    std::fill(isVisitedF.begin(), isVisitedF.end(), false);

    // 其他初始化逻辑
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
void pruneCore(const Graph &G, int k, int l, vector<int> &outDegree, vector<int> &inDegree, vector<bool> &inCore)
{
    queue<int> q;
    for (int i = 0; i < G.V; ++i)
    {
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

void findKLCore(const Graph &G, int maxK, int maxL, unordered_map<int, int> &reverseMapping, string outfilename)
{
    ofstream fout(outfilename);
    fout << "id,k,l" << endl;

    vector<int> initialOutDegree(G.V, 0);
    vector<int> initialInDegree(G.V, 0);
    vector<bool> initialInCore(G.V, true);

    for (int u = 0; u < G.V; ++u)
    {
        initialOutDegree[u] = G.adj[u].size();
        initialInDegree[u] = G.revAdj[u].size();
    }

    for (int k = 0; k <= maxK; ++k)
    {

        vector<int> outDegree = initialOutDegree;
        vector<int> inDegree = initialInDegree;
        // vector<bool> inCore(G.V, true);
        vector<bool> inCore = initialInCore;

        for (int l = 0; l <= maxL; ++l)
        {
            pruneCore(G, k, l, outDegree, inDegree, inCore);

            // Find the connected components of the remaining vertices
            function<void(int, vector<bool> &, vector<int> &)> dfs = [&](int v, vector<bool> &visited, vector<int> &component)
            {
                visited[v] = true;
                component.push_back(v);
                for (int u : G.adj[v])
                {
                    if (inCore[u] && !visited[u])
                    {
                        dfs(u, visited, component);
                    }
                }
                for (int u : G.revAdj[v])
                {
                    if (inCore[u] && !visited[u])
                    {
                        dfs(u, visited, component);
                    }
                }
            };

            vector<bool> visited(G.V, false);
            vector<vector<int>> components;

            for (int i = 0; i < G.V; ++i)
            {
                if (inCore[i] && !visited[i])
                {
                    vector<int> component;
                    dfs(i, visited, component);
                    components.push_back(component);
                }
            }
            map<int, set<string>> nodeCores; // 节点id -> (k,l)集合

            cout << "The (" << k << "," << l << ")-core connected subgraphs are:" << endl;
            for (const auto &component : components)
            {
                if (!component.empty())
                {
                    for (int v : component)
                    {
                        cout << reverseMapping[v] << " ";
                        string kl = "(" + to_string(k) + "," + to_string(l) + ")";
                        nodeCores[reverseMapping[v]].insert(kl);
                    }
                    cout << endl;
                }
            }

            // for (auto &p : nodeCores)
            // {
            //     fout << p.first << ",\"[";
            //     bool first = true;
            //     for (auto &kl : p.second)
            //     {
            //         if (!first)
            //             fout << ",";
            //         fout << kl;
            //         first = false;
            //     }
            //     fout << "]\"" << endl;
            // }
            for (auto &p : nodeCores)
            {
                for (auto &kl : p.second)
                {
                    // kl 原来是 "(k,l)" 的字符串，我们需要拆开
                    int k_val, l_val;
                    if (sscanf(kl.c_str(), "(%d,%d)", &k_val, &l_val) == 2)
                    {
                        fout << p.first << "," << k_val << "," << l_val << "\n";
                    }
                }
            }
        }
    }
    fout.close();
}

// 多个参数组合,计算时间太长
int main(int argc, char *argv[])
{
    // struct rusage usage;

    const string headerk = R"(E:\code\neo4j-connect\demo\src\)";
    const string filename = headerk + R"(dataset-original\caseStudy.txt)";
    const string outfilename = headerk + R"(dataset-Change\edges.csv)";
    const string outfilenameCoreness = headerk + R"(dataset-Change\coreness.csv)";

    double begin_time = clock();
    // readGraphFromFile(filename, nodeMapping); // 对节点重新排序

    readGraphFromFile(filename, outfilename, nodeMapping); // 对节点重新排序

    double end_time = clock();
    int follower_size = 0;
    cout << "finish reading graph, time: " << (end_time - begin_time) / CLOCKS_PER_SEC << endl;

    int maxk = 1;
    int maxl = 4;

    int bmax = 1;
    int l = maxl;
    int k = maxk;
    std::ofstream outfile(headerk + "dataset-Change/AF.csv", std::ios::app);

    if (!outfile.is_open())
    {
        std::cout << "文件创建失败" << std::endl;
    }

    maxK = k;
    maxL = l;
    b = bmax; // 155
    initK = max(maxK - 1, 0);
    initL = max(maxL - 1, 0);
    n = G.V;
    m = G.edgeNum;
    cout << "点数：" << n << " 边数：" << m << endl;
    anchor_tag.assign(G.V, false);
    isAffected.assign(G.V, false); // 受影响的节点
    k_1shell.assign(G.V, false);
    l_1shell.assign(G.V, false);
    auto now = std::chrono::system_clock::now();
    std::time_t now_time = std::chrono::system_clock::to_time_t(now);
    double begin_time1 = clock();
    inCoreStorageInitKInitL.assign(n, true);
    inCoreStorageMaxKMaxL.assign(n, true);

    tempInitialOutDegree_init.assign(n, 0);
    tempInitialOutDegree_max.assign(n, 0);
    tempInitialInDegree_init.assign(n, 0);
    tempInitialInDegree_max.assign(n, 0);
    IscAnchore_Set.assign(G.V, false);
    isVisitedF.assign(G.V, false);
    vector<bool> dsustate(n, false); // 初始化外部候选锚点跟随者的根组件，false没有， true有。
                                     //     is_initialized = true;

    findKLCore(G, maxK, maxL, reverseMapping, outfilenameCoreness);
    maxCA = -1;
    srand(static_cast<unsigned int>(time(0)));
    while (b--)
    {
        double t1 = clock();
        cout << "-------------剩余次数:" << b << "---------------" << endl;

        // if是有执行的前后顺序的，所以不用担心，maxCA=-1是，数组越界
        if (maxCA == -1) // maxCA=-1没计算过，第一次锚定
        {

            cout << "第一次锚定呀" << endl;
            previousAnchoredNode_inSHell = false; // 锚定的是内部的节点，所以需要重用上一轮的信息。
        }
        else if (shell_KL_1_info.delete_info_isTrue[maxCA]) // 在order中所以是内部的。
        {
            // previous_Anchore_Follow.clear();
            previous_cA_MaxFNum_Set.clear();
            previous_cA_upper_Set.clear();
            previous_cA_Nv_set.clear(); // 上一轮候选邻居集合
            previous_outNVnode2orderSet.clear();
            previous_cAnchore_Set.clear();
            dsuPrevious.clear();
            previous_cA_cAoutNV.clear();
            cout
                << "锚定的是内部的节点呀" << endl;
            previousAnchoredNode_inSHell = true; // 锚定的是内部的节点，所以需要重用上一轮的信息。

            previous_cA_MaxFNum_Set = cA_MaxFNum_Set;
            previous_cA_upper_Set = cA_upper_Set;
            previous_cA_Nv_set = cA_Nv_set;                   // 上一轮候选邻居集合
            previous_outNVnode2orderSet = outNVnode2orderSet; // 节点v 的外部邻居。
            previous_KL_1_SUM = KL_1_SUM;
            previousAV = maxCA;
            previous_cAnchore_Set = cAnchore_Set;
            dsuPrevious = shell_KL_1_info.dsu;
            previous_delete_info_isTrue = shell_KL_1_info.delete_info_isTrue;
        }
        else // 外部的节点重用需要慎重。
        {
            // previous_Anchore_Follow.clear();
            previous_cA_MaxFNum_Set.clear();
            previous_cA_upper_Set.clear();
            previous_cA_Nv_set.clear(); // 上一轮候选邻居集合
            previous_outNVnode2orderSet.clear();
            previous_cAnchore_Set.clear();
            dsuPrevious.clear();
            previous_cA_cAoutNV.clear();
            cout << "锚定的是外部的节点呀" << endl;
            previousAnchoredNode_inSHell = false; // 锚定的是外部的节点，所以需要重用上一轮的信息。
            // previous_Anchore_Follow = Anchore_Follow;
            previous_cA_MaxFNum_Set = cA_MaxFNum_Set;
            previous_cA_upper_Set = cA_upper_Set;
            previous_cA_Nv_set = cA_Nv_set;                   // 上一轮候选邻居集合
            previous_outNVnode2orderSet = outNVnode2orderSet; // 节点v 的外部邻居。
            previous_KL_1_SUM = KL_1_SUM;
            previousAV = maxCA;
            previous_cAnchore_Set = cAnchore_Set;
            dsuPrevious = shell_KL_1_info.dsu;
            previous_delete_info_isTrue = shell_KL_1_info.delete_info_isTrue;
            // 不同之处-----------------------------------
            previous_dsuRootSetOut = dsuRootSetOut;
            previous_cA_cAoutNV = cA_cAoutNV;
        }

        initializeItem(); // 初始化

        begin_time = clock();

        bliudSC(); // 计算初始klcore，求出在k-1,l-1core的基础上分解求解klcore时删除节点的顺序
        inCoreStoragePrevi = inCoreStorageMaxKMaxL;
        // inCoreStorageMaxKMaxL全是true，为什么呢？？？？？

        if (orderKL.size() == 0)
        {

            for (int i = 0; i < G.V; i++)
            {
                if (inCoreStorageInitKInitL[i] == false)
                {
                    cout << i << endl;
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
            KL_1_SUM = shell_KL_1_info.delete_shell_order.size(); // 其实和orderKL是同一个东西

            computeUpShell(remainFollSum); // kl:0,  l-1(L):1， k-1(K):2。
            double t3 = clock();
            cout << "计算shell和上界的时间：Elapsed time:\t" << (t3 - t2) / CLOCKS_PER_SEC << " s" << std::endl;
            cout << "shell：\t" << orderKL.size() << endl;
            cout << "L：\t" << cAnchore_Set.size() << endl;

            /***
             * cF_num_to_ver
             * 每个跟随者数量下 有哪些候选的跟随者节点。
             */
            cout << remainFollSum << " " << KL_1_SUM << endl;
            remainFollSum = min(remainFollSum, KL_1_SUM);

            cF_num_to_ver.resize(remainFollSum + 1); // 开辟 最大可能的跟随者数量的大小。

            for (int i = 0; i < cAnchore_Set.size(); i++)
            {

                tempCanFollSize = cA_MaxFNum_Set[i]; // 三个shell候选锚点的跟随者数量总和

                cF_num_to_ver[tempCanFollSize].push_back(cAnchore_Set[i]);
                // cout << reverseMapping.at(cAnchore_Set[i]) << " 的最大跟随者数 ****** " << tempCanFollSize << endl;
            }

            /**
             * 从 从高到低的候选锚点集合，找出最优的锚点
             * 如果节点是已经遍历过的候选节点的跟随者，那么他一定不会成为跟随者。 vector<int> isVisitedF; // 历史遍历过的节点。
             *
             */
            double t7 = clock();
            cout << "计算排序：Elapsed time:\t" << (t7 - t3) / CLOCKS_PER_SEC << " s" << std::endl;
            int cot = 0;
            int dian = 0;
            vector<int> tempSet;
            while (remainFollSum)
            {

                // cout << remainFollSum << endl;
                // 剩余的跟随着数量 比 当前的最大跟随着大，那么就继续判断
                if (max_FollowerNum < remainFollSum)
                {
                    // cout << cF_num_to_ver[remainFollSum].size() << endl;
                    for (auto cA : cF_num_to_ver[remainFollSum]) // 获取候选锚点
                    {
                        cot++;

                        if (isVisitedF[cA]) // 是遍历过的跟随者，说明这些跟随者都比现在锚点带来的收益小
                        {
                            continue; // 跳过不再计算
                        }

                        auto it = previous_Anchore_Follow.find(cA);
                        if (it != previous_Anchore_Follow.end() && dsuPrevious.find(previousAV) != dsuPrevious.find(cA)) // 找到了之前的跟随者记录
                        {
                            // if (nodeMapping.at(983) == cA)
                            // {
                            //     cout << "a有了" << it->second.size() << endl;
                            // }
                            // cout << "a有了" << it->first << endl;
                            int sizeN = it->second.size();
                            if (sizeN > max_FollowerNum) // 锚点cA的跟随者，大于当前的最大跟随者，那么就替换
                            {
                                // cout << "我重用了已经计算过的跟随者，提速了啊~~~~01" << endl;
                                maxCA = cA;
                                max_F_real_set = it->second;
                                max_FollowerNum = sizeN - 1;

                                if (sizeN >= remainFollSum) // 当前遍历的预估的大小和已经取得的最大跟随者大小一样，那么后续就不需要遍历了
                                {

                                    previous_Anchore_Follow.erase(cA); // 已经是锚点了，所以清空了吧

                                    break;
                                }

                                // 否则，因为cA跟随者中的点v不可能最大跟随者的锚点，并标记
                                for (auto v : it->second)
                                {
                                    isVisitedF[v] = true;
                                }
                            }

                            continue;
                        }

                        temp_FollowerNum = 0;

                        if (computeFollower(cA)) // 可以锚定
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
                            if (shell_KL_1_info.delete_info_isTrue[cA]) // 锚点是内部节点可以重用 ，锚点是外部节点不重用，因为后续逻辑判断一大堆
                            {

                                previous_Anchore_Follow.insert({cA, tempSet});
                            }
                            if (max_FollowerNum < temp_FollowerNum)
                            {
                                max_F_real_set.clear();

                                maxCA = cA;
                                max_FollowerNum = temp_FollowerNum; // 当前最大跟随者数量

                                for (auto v : tempFollowerSet)
                                {
                                    if (isTempFollowerSet[v] > -1)
                                    {
                                        max_F_real_set.push_back(v);

                                        if (!isVisitedF[v])
                                        {
                                            isVisitedF[v] = true;
                                        }
                                    }
                                }

                                if (max_FollowerNum >= remainFollSum) // 当前遍历的预估的大小和已经取得的最大跟随者大小一样，那么后续就不需要遍历了
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
            // 遍历到只有0个元素的了，那就随便选一个作为锚点返回。
            if (max_FollowerNum == -1)
            {
                max_F_real_set.clear();

                // maxFollowerSetState.clear();
                std::srand(std::time(nullptr)); // 使用当前时间作为随机种子

                // int a = std::rand() % 100; // 生成 [0, 99] 范围内的随机数

                maxCA = cAnchore_Set[std::rand() % cAnchore_Set.size()]; // 随机从候选锚点中选

                // maxCA = shell_KL_1_info.delete_shell_order[KL_1_SUM - 1];//从shell中选
                anchor_tag[maxCA] = true;

                isAffected[maxCA] = true;
                // maxFollowerSetState.push_back(maxCA);

                max_F_real_set.push_back(maxCA);
                cout << "---呦吼,没有随机挑选，所以肯定存在出入，莫要在意，  是对的" << endl;
                max_FollowerNum = 0;
            }
            double t4 = clock();
            cout << "计算锚点时间：Elapsed time:\t" << (t4 - t3) / CLOCKS_PER_SEC << " s" << std::endl;
            cout << "\n\n";
            cout << "@@@锚点：" << reverseMapping.at(maxCA) << "跟随者数量：" << max_F_real_set.size() << " 跟随者：";
            follower_size += max_FollowerNum; // 记录跟随者数量
            for (auto v : max_F_real_set)
            {
                isAffected[v] = true;
                cout << reverseMapping.at(v) << " ";
            }
            cout << endl;

            int rootMaxCA = shell_KL_1_info.dsu.find(maxCA); // 锚点的组件的根

            int outvorder = outNVnode2orderSet.at(maxCA); // 候选锚点的vorderf
            if (outvorder >= orderKL.size())              // 锚定的是外部节点,那么就删除其跟随者的组件中已经存储的信息 previous_Anchore_Follow
            {

                std::fill(dsustate.begin(), dsustate.end(), false);
                dsuRootSetOut.clear();
                int root;

                for (auto upV : cA_Nv_set[outvorder]) // 是上升节点，
                {

                    root = shell_KL_1_info.dsu.find(upV);

                    if (!dsustate[root]) // 是根节点
                    {
                        // previous_Anchore_Follow.erase(upV);
                        dsustate[root] = true;
                        dsuRootSetOut.push_back(root);

                        for (auto vdsu : shell_KL_1_info.dsu.parentToChildren[root]) // 删除受影响的组件中已经存储的节点信息
                        {
                            previous_Anchore_Follow.erase(vdsu);
                        }
                    }
                }
                cout << endl;
            }
            else
            {                                                                     // 内部节点则删除同一个dsu下的节点
                for (auto vdsu : shell_KL_1_info.dsu.parentToChildren[rootMaxCA]) // 删除受影响的组件中已经存储的节点信息
                {
                    previous_Anchore_Follow.erase(vdsu);
                }
            }
        }

        anchor_tag[maxCA] = true;

        end_time = clock();
        outfile << "type," << "id_list" << endl;
        outfile << "anchor," << reverseMapping.at(maxCA) << endl;
        // outfile << "follower：\t" << follower_size << endl;
        outfile << "follower,";
        for (auto v : max_F_real_set)
        {
            if (maxCA == v)
                continue;
            outfile << reverseMapping.at(v) << " ";
        }
        double end_time1 = clock();
    }

    double end_time1 = clock();
    cout << "computeUpShell, time: " << (end_time1 - begin_time1) / CLOCKS_PER_SEC << endl;
    cout << "\n\n";
    outfile.close();

    return 0;
}
