#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define ordered_set tree<int, null_type,less<int>, rb_tree_tag,tree_order_statistics_node_update>
using namespace std;

using ll = long long int;
using ld = long double;
#define vi vector<int>
#define vl vector<ll>
#define vd vector<ld>
#define pi pair<int, int>
#define pl pair<ll, ll>
#define pd pair<ld, ld>
#define vpi vector<pi>
#define vpl vector<pl>
#define vvi vector<vi>
#define vvl vector<vl>

const int N = 1e5+2, MOD = 1e9+7, MOD1 = 998244353;
const ll inf = 1e18;
const double eps = 1e-9;
const double PI = acos(-1.0);

#define for(i, a, b) for (int i=a; i<b; i++)
#define FOR(i, a) for (int i=0; i<a; i++)
#define ford(i,a,b) for (int i=b; i>a; i--)
#define FORD(i,a) for (int i=a; i>0; i--)
#define trav(a,x) for (auto& a : x)

#define sz(x) (int)x.size()
#define emp emplace
#define mp make_pair
#define pb push_back
#define pf push_front
#define dq deque
#define f first
#define s second
#define all(x) x.begin(), x.end()
#define sort(x) sort(all(x))
#define rev(x) reverse(all(x))
#define endl "\n"

bool ckmax(int &a, int b) {return b > a ? a = b, 1 : 0;}
bool ckmin(int &a, int b) {return b < a ? a = b, 1 : 0;}

ll mod(ll x)
{
    return ((x%MOD + MOD)%MOD);
}
ll add(ll a, ll b)
{
    return mod(mod(a)+mod(b));
}
ll mul(ll a, ll b)
{
    return mod(mod(a)*mod(b));
}

ll gcd(ll a, ll b){
    if (a==0)  return b;
    return gcd(b%a, a);
}

ll lcm(ll a, ll b){
    return a*b/gcd(a, b);
}

vl factorial;
void fact(ll n){
    factorial.clear();
    factorial.resize(n+1);
    factorial[0] = 1;
    for(ll i=1; i<=n; i++)  factorial[i] = (factorial[i - 1] * i) % MOD;
}

//Returns a^n mod MOD
ll FastExp(ll a, ll n, ll MOD){
    if(n == 0)  return 1;
    ll b = FastExp(a, n/2, MOD);

    if(n%2 != 0)  return (((b*b)%MOD)*a)%MOD;
    else  return (b*b)%MOD;
}

// Returns n^(-1) mod MOD
ll modInverse(ll n){
    return FastExp(n, MOD-2, MOD);
}

ll nCr(ll n, ll r){
    return (factorial[n] * modInverse(factorial[r]) % MOD * modInverse(factorial[n - r]) % MOD) % MOD;
}

//Returns C = A*B
void MatMul(vvl &A, vvl &B, vvl &C){
    for(int i=0; i<2; i++){
        for(int j=0; j<2; j++){
            C[i][j] = 0;
            for(int k=0; k<2; k++){
                C[i][j] += (A[i][k] * B[k][j])%MOD;
                C[i][j] %= MOD;
            }
        }
    }
}

//Returns B = A^n
void MatExp(vvl &A, ll n, vvl &B){
    if(n == 0)  B = {{1, 0}, {0, 1}};
    else if(n == 1)  B = A;
    else{
        vvl C(2, vl(2, 0)), D(2, vl(2, 0));
        MatExp(A, n/2, C);
        MatMul(C, C, D);

        if(n%2 != 0){
            MatMul(D, A, B);
        }
        else  B = D;
    }
}

//DFS Tree
vector<vector<ll>> children;
vector<ll> parent;  //    parent.assign(n+1, -1);

void DFS_tree(ll v){
    for(auto &ch: children[v]){
        if(ch != parent[v]){
            parent[ch] = v;
            //Pre Order
            DFS_tree(ch);
            //Post Order
        }
    }
}

//DFS
vector<vector<int>> g;
vector<bool> visited;

void DFS(int v){
    if(visited[v])  return;
    visited[v]=true;
    for(auto &ch: g[v]){
        if(!visited[ch]){
            DFS(ch);
            visited[ch]=true;
        }
    }
}

//BFS
vector<vector<int>> g;
vector<bool> visited;
//vector<int> dist, par;  //    dist.assign(n+1, 0); par.assign(n+1, -1);

void BFS(int v){
    if(visited[v])  return;
    visited[v]=true;
    queue<int> q;
    q.push(v);
    while(!q.empty()){
        int u = q.front();
        q.pop();
        for(auto &ch: g[u]){
            if(!visited[ch]){
                q.push(ch);
                visited[ch]=true;
                //dist[ch] = dist[u]+1;
                //par[ch]=u;
            }
        }
    }
}

//Dijkstra's Algorithm
vector<vector<pair<int, int>>> g(N);
vector<ll> dist(N, inf);

void dijkstra(int src){
    dist.assign(N, inf);
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> pq;
    pq.push({0, src});
    dist[src]=0;
    while(!pq.empty()){
        auto [d, u] = pq.top();
        pq.pop();
        for(auto [v, w]: g[u]){
            if(dist[v] > d+w){
                dist[v] = d+w;
                pq.push({dist[v], v});
            }
        }
    }
}

//Topological Sort
vector<vector<int>> g(N);
vector<int> indeg(N, 0);
vector<int> top;

void TopoSort(int n)
{
    queue<int> q;
    for(int i=0; i<n; i++){
        if(indeg[i]==0)  q.push(i);
    }
    while(!q.empty()){
        int u = q.front();
        q.pop();
        top.push_back(u);
        for(auto &v: g[u]){
            //Procesa node
            indeg[v]--;
            if(indeg[v]==0)  q.push(v);
        }
    }
}

//Bellman Ford
vector<vector<int>> edges;  // {u, v, w}
vector<ll> dist(N, inf);
void BellmanFord(int src, int n){
    dist[src]=0;

    for(int i=0; i<n-1; i++){
        for(auto &e: edges){
            int u = e[0], v = e[1], w = e[2];
            if(dist[v] > dist[u] + w){
                dist[v] = dist[u] + w;
            }
        }
    }

    for(auto &e: edges){
        int u = e[0], v = e[1], w = e[2];
        if(dist[v] > dist[u] + w){
            cout<<"Negative weight cycle detected"<<endl;
            break;
        }
    }
}

//DSU
vector<int> par, rnk;
void makeSet(int v){
    par[v] = v;
    rnk[v] = 0;
}

int findSet(int v){
    if(par[v] == v)  return v;
    return par[v] = findSet(par[v]);
}

void unionSet(int u, int v){
    u = findSet(u);
    v = findSet(v);
    if(rnk[u] < rnk[v]) {
        par[u] = v;
    }
    else if(rnk[u] > rnk[v]) {
        par[v] = u;
    }
    else{
        par[v] = u;
        rnk[u]++;
    }
}

//Kruskal's MST
vector<vector<int>> edges;  // {w, u, v}
vector<pair<int, int>> mst;
ll kruskal(int n){
    ll minWt = 0;
    mst.clear();
    par.assign(n, 0);
    rnk.assign(n, 0);

    for(int i=0; i<n; i++){
        makeSet(i);
    }

    sort(edges.begin(), edges.end());

    for(auto &e: edges){
        int w = e[0], u = e[1], v = e[2];
        if(findSet(u) != findSet(v)){
            minWt += w;
            mst.push_back({u, v});
            unionSet(u, v);
        }
    }

    return minWt;
}

//Segment Tree
vector<ll> segmentTree(4*N);
void build(int node, vector<int> &arr, int start, int end){
    if(start == end){
        segmentTree[node] = arr[start];
    }
    else{
        int mid = (start + end)/2;
        build(2*node, arr, start, mid);
        build(2*node+1, arr, mid+1, end);
        segmentTree[node] = segmentTree[2*node] + segmentTree[2*node+1];  //change function here
    }
}

ll query(int node, int start, int end, int l, int r){
    if(start>r || end<l)  return 0;  //change identity here
    if(l <= start && r >= end)  return segmentTree[node];

    int mid = (start+end)/2;
    return query(2*node, start, mid, l, r) + query(2*node+1, mid+1, end, l, r);  //change function here
}

void update(int node, int start, int end, int pos, int val){
    if(start == end)  segmentTree[node] = val;
    else{
        int mid = (start + end)/2;
        if(pos <= mid)  update(2*node, start, mid, pos, val);
        else  update(2*node+1, mid+1, end, pos, val);
        segmentTree[node] = segmentTree[2*node] + segmentTree[2*node+1];  //change function here
    }
}

void solve()
{

}

int main()
{
    cin.tie(0)->sync_with_stdio(0);
    cin.exceptions(cin.failbit);

    int t=1;
    cin>>t;
    while(t--)
    {
        solve();
    }
    return 0;
}
