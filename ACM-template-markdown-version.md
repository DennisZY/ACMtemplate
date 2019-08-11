[TOC]

## 1 Base algorithm

### 1.1 Bisection method

search for $min(b),b\in\{a[k]\geq x\}$

``` cpp
while(l<r){
	int mid = (l + r) >> 1;
	if(a[mid] >= x) r = mid;
	else l = mid + 1;
}
return a[l];
```

search for $max(b),b\in\{a[k]\leq x\}$

```cpp
while(l<r){
	int mid = (l + r + 1) >> 1;
	if(a[mid] <= x) l = mid;
	else r = mid - 1;
}
return a[l];
```

## 2 String

### 2.1 SAM

```cpp
struct SAM{
    static const int N = 1000010;
    static const int CHAR_SET_SIZE=26;
    int ch[N<<1][CHAR_SET_SIZE],fa[N<<1],len[N<<1],siz[N<<1];
    int tot,last;
    int newnode(){
        ++tot;
        memset(ch[tot],0,sizeof ch[tot]);
        fa[tot]=0;
        return tot;
    }
    void init(){
        tot=1;
        last=1;
        len[1]=0;
        memset(ch[1],0,sizeof ch[1]);
        memset(siz,0,sizeof siz);
    }
    void add(int x){
        int pos = last,newpos=newnode();
        last = newpos;
        siz[newpos]=1;
        len[newpos]=len[pos]+1;
        while(pos&&!ch[pos][x]){ch[pos][x]=newpos;pos=fa[pos];}
        if(!pos)fa[newpos]=1;
        else{
            int oldpos=ch[pos][x];
            if(len[oldpos]==len[pos]+1)fa[newpos]=oldpos;
            else{
                int anp=newnode();
                memcpy(ch[anp],ch[oldpos],sizeof ch[anp]);
                fa[anp]=fa[oldpos];
                len[anp]=len[pos]+1;
                fa[oldpos]=fa[newpos]=anp;
                while(pos&&ch[pos][x]==oldpos){
                    ch[pos][x]=anp;
                    pos=fa[pos];
                }
            }
        }   
    }
}sam;
```



## 3 Graph Theory and Network Algorithms

### 3.1 Maxflow

#### 3.1.1 Dinic

```cpp
class dinic {
  private:
    static const int N = 10010;//endpoint_num
    static const int M = 200010;//edge_num
    static const int INF = 0x3f3f3f3f;
    int tot,n,m,s,t;
    int carc[N];//curarc
    int Head[N],nxt[M],ver[M],flow[M];//base
    int d[N];//depth
  public:
    void init(int _n,int _m,int _s,int _t) {
        tot=1;
        n=_n,m=_m,s=_s,t=_t;
        fill(Head,Head+n+1,0);
    }
    void addedge(int u,int v,int w) {
        ver[++tot]=v;
        flow[tot]=w;
        nxt[tot]=Head[u];
        Head[u]=tot;

        ver[++tot]=u;
        flow[tot]=0;
        nxt[tot]=Head[v];
        Head[v]=tot;
    }
    bool bfs() {
        fill(d,d+n+1,0);
        queue<int>q;
        d[s]=1;
        q.push(s);
        while(q.size()) {
            int u = q.front();
            q.pop();
            for(int i = Head[u]; i; i=nxt[i]) {
                int v = ver[i];
                if(d[v]==0&&flow[i]) {
                    d[v]=d[u]+1;
                    q.push(v);
                }
            }
        }
        return d[t]!=0;
    }
    int dfs(int u,int minn);
    int maxflow() {
        int ans=0;
        while(bfs()) {
            copy(Head+1,Head+n+1,carc+1);
            ans+=dfs(s,INF);
        }
        return ans;
    }
} flow;
int dinic::dfs(int u,int minn) {
    if(u==t)return minn;
    int ret=0;
    for(int i = carc[u]; minn&&i; i=nxt[i]) {
        carc[u]=i;
        int v = ver[i];
        if(flow[i]&&d[v]==d[u]+1) {
            int final=dfs(v,min(flow[i],minn));
            if(final>0) {
                flow[i]-=final;
                flow[i^1]+=final;
                minn-=final;
                ret+=final;
            } else d[v]=-1;
        }
    }
    return ret;
}
```



#### 3.1.2 ISAP

```cpp
class ISAP {
	static const int N = 10010;//endpoint_num
	static const int M = 240010;//edge_num
	static const int INF = 0x3f3f3f3f;
	int tot,n,m,s,t;
	int carc[N],gap[N];//curarc and gap
	int pre[N];
	int Head[N],nxt[M],ver[M],flow[M];//base
	int d[N];//depth
	int visit[N];
	bool visited[N];
  public:
	void init(int _n,int _m,int _s,int _t) {
		tot=1;
		n=_n,m=_m,s=_s,t=_t;
		fill(Head,Head+n+1,0);
		fill(visit,visit+n+1,0);
	}
	void addedge(int u,int v,int w) {
		ver[++tot]=v;
		flow[tot]=w;
		nxt[tot]=Head[u];
		Head[u]=tot;

		ver[++tot]=u;
		flow[tot]=0;
		nxt[tot]=Head[v];
		Head[v]=tot;
	}
	bool bfs() {// calculate the depth
		fill(visited,visited+n+1,0);
		queue<int>q;
		visited[t]=1;class ISAP {
	static const int N = 10010;//endpoint_num
	static const int M = 240010;//edge_num
	static const int INF = 0x3f3f3f3f;
	int tot,n,m,s,t;
	int carc[N],gap[N];//curarc and gap
	int pre[N];
	int Head[N],nxt[M],ver[M],flow[M];//base
	int d[N];//depth
	int visit[N];
	bool visited[N];
  public:
	void init(int _n,int _m,int _s,int _t) {
		tot=1;
		n=_n,m=_m,s=_s,t=_t;
		fill(Head,Head+n+1,0);
		fill(visit,visit+n+1,0);
	}
	void addedge(int u,int v,int w) {
		ver[++tot]=v;
		flow[tot]=w;
		nxt[tot]=Head[u];
		Head[u]=tot;

		ver[++tot]=u;
		flow[tot]=0;
		nxt[tot]=Head[v];
		Head[v]=tot;
	}
	bool bfs() {// calculate the depth
		fill(visited,visited+n+1,0);
		queue<int>q;
		visited[t]=1;
		d[t]=0;
		q.push(t);
		while(q.size()) {-
			int u = q.front();
			q.pop();
			for(int i = Head[u]; i; i=nxt[i]) {
				int v = ver[i];
				if(i&1&&!visited[v]) {
					visited[v]=true;
					d[v]=d[u]+1;
					q.push(v);
				}
			}
		}
		return visited[s];
	}
	int aug() {
		int u=t,df=INF;
		while(u!=s) {// calculate the flow
			df=min(df,flow[pre[u]]);
			u=ver[pre[u]^1];
		}
		u=t;

		while(u!=s) {
			flow[pre[u]]-=df;
			flow[pre[u]^1]+=df;
			u=ver[pre[u]^1];
		}
		return df;
	}
	int maxflow();
} flow;
int ISAP :: maxflow() {
	int ans=0;
	fill(gap,gap+n+1,0);
	for(int i=1; i<=n; i++) carc[i]=Head[i];//copy the head for ignore the useless edge
	bfs();
	for(int i=1; i<=n; i++)gap[d[i]]++;//Using array gap to store how many endpoint's depth is k. When we found some gap is 0 or d[source]>n mean there are no another augmenting path.
	int u = s;
	while(d[s]<=n) {
		if(u==t) {
		ans+=aug();
		u=s;
		}
		bool advanced=false;
		for(int i=carc[u]; i; i=nxt[i]) {
			if(flow[i]&&d[u]==d[ver[i]]+1) {
				advanced=true;
				pre[ver[i]]=i;
				carc[u]=i;//carc
				u=ver[i];
				break;
			}
		}
		if(!advanced) {
			int mindep=n-1;
			for(int i=Head[u]; i; i=nxt[i]) {
				if(flow[i]) {
					mindep=min(mindep,d[ver[i]]);
				}
			}
			if(--gap[d[u]]==0)break;
			gap[d[u]=mindep+1]++;

			carc[u]=Head[u];
			if(u!=s)u=ver[pre[u]^1];
		}
	}
	return ans;
}
		d[t]=0;
		q.push(t);
		while(q.size()) {
			int u = q.front();
			q.pop();
			for(int i = Head[u]; i; i=nxt[i]) {
				int v = ver[i];
				if(i&1&&!visited[v]) {
					visited[v]=true;
					d[v]=d[u]+1;
					q.push(v);
				}
			}
		}
		return visited[s];
	}
	int aug() {
		int u=t,df=INF;
		while(u!=s) {// calculate the flow
			df=min(df,flow[pre[u]]);
			u=ver[pre[u]^1];
		}
		u=t;

		while(u!=s) {
			flow[pre[u]]-=df;
			flow[pre[u]^1]+=df;
			u=ver[pre[u]^1];
		}
		return df;
	}
	int maxflow();
} flow;
int ISAP :: maxflow() {
	int ans=0;
	fill(gap,gap+n+1,0);
	for(int i=1; i<=n; i++) carc[i]=Head[i];//copy the head for ignore the useless edge
	bfs();
	for(int i=1; i<=n; i++)gap[d[i]]++;//Using array gap to store how many endpoint's depth is k. When we found some gap is 0 or d[source]>n mean there are no another augmenting path.
	int u = s;
	while(d[s]<=n) {
		if(u==t) {
		ans+=aug();
		u=s;
		}
		bool advanced=false;
		for(int i=carc[u]; i; i=nxt[i]) {
			if(flow[i]&&d[u]==d[ver[i]]+1) {
				advanced=true;
				pre[ver[i]]=i;
				carc[u]=i;//carc
				u=ver[i];
				break;
			}
		}
		if(!advanced) {
			int mindep=n-1;
			for(int i=Head[u]; i; i=nxt[i]) {
				if(flow[i]) {
					mindep=min(mindep,d[ver[i]]);
				}
			}
			if(--gap[d[u]]==0)break;
			gap[d[u]=mindep+1]++;

			carc[u]=Head[u];
			if(u!=s)u=ver[pre[u]^1];
		}
	}
	return ans;
}
```



## 4 Algebraic Algorithms

## 5 Number Theory

### 5.1 Common number theory

#### 5.1.1 Modular

$$
(p-1)！=p-1 \pmod{p}
$$

#### 5.1.2 Combinatorics

$$
C_n^m = C _{n-1}^{m-1}+C _{n-1}^{m}
$$

$$
mC_n^m = nC _{n-1}^{m-1}
$$

$$
C_n^0+C_n^1+C_n^2+……+C_n^n = 2^n
$$

$$
1C_n^1+2C_n^2+3C_n^3+……+nC_n^n =n2^{n-1}
$$

$$
1^2C_n^1+2^2C_n^2+3^2C_n^3+……+n^2C _n^n =n(n+1)2^{n-2}
$$

$$
\frac{C_n^1}{1}-\frac{C_n^2}{2}+\frac{C_n^3}{3}+……+(-1)^{n-1}\frac{C _n^n}{n} =1 + \frac{1}{2}+ \frac{1}{3}+……+ \frac{1}{n}
$$

$$
(C_n^0)^2+(C_n^1)^2+(C_n^2)^2+……+(C _n^n)^2 = C_{2n}^n
$$

#### 5.1.3 Fibonacci

$$
f_n=\frac{1}{\sqrt{5}}((\frac{1+\sqrt{5}}{2})^n-(\frac{1-\sqrt{5}}{2})^n)
$$

$$
S_n=f_{n+2}-1=\sum_{i=1}^{n}f_i
$$

$$
f_{2n}=f_{n+1}*f_{n}+f_n*f_{n-1}=f_{n+1}*f_{n}+f_n*(f_{n+1}-f_{n})
$$

$$
f_{2n+1}=f_{n+1}*f_{n+1}+f_n*f_n
$$

#### 5.1.4 Inverse element

```cpp
a[i] = (p - (p / i)) * a[p % i] % p;
```

### 5.2 Mobius

```cpp
void primejudge(int lim) {
    memset(v, 0, sizeof v);
    pr = 0;
    mu[1] = 1;
    for (int i = 2; i <= lim; ++i) {
        if (!v[i]) {
            prime[pr++] = i;
            v[i] = i;
            mu[i] = -1;
        }
        for (int j = 0; j < pr && lim / i >= prime[j]; j++) {
            v[i * prime[j]] = prime[j];
            if (v[i] <= prime[j])break;
            mu[i * prime[j]] = -mu[i];
        }
    }
}
```

## 6 Data structure

## 7 Computational geometry

## 8 Classic Problems

### 8.1 kth-number

#### 8.1.1 Dynamic range dynamic kth

##### version1 segment tree in BIT

```cpp
const int N = 100010;
struct sgmt {
    int l, r, sz;
} tr[50000010];
struct rec {
    int op, x, y, z;
} q[N];
int root[N], zxs[N];
int tot, n, m, p;
int a[N], b[N << 1];
int get(int val) {
    return lower_bound(b + 1, b + p + 1, val) - b;
}
int newnode() {
    ++tot;
    tr[tot].l = tr[tot].r = tr[tot].sz = 0;
    return tot;
}
int build(int l, int r) {
    int rt = newnode();
    if (l != r) {
        int mid = (l + r) >> 1;
        tr[rt].l = build(l, mid);
        tr[rt].r = build(mid + 1, r);
    }
    return rt;
}
int update(int rt, int val, int cnt) {
    int tmp = newnode();
    int nrt = tmp;
    int l = 1, r = p;
    tr[nrt].sz = tr[rt].sz + cnt;
    while (l < r) {
        int mid = (l + r) >> 1;
        if (val <= mid) {
            tr[nrt].l = newnode();
            tr[nrt].r = tr[rt].r;
            nrt = tr[nrt].l;
            rt = tr[rt].l;
            r = mid;
        } else {
            tr[nrt].r = newnode();
            tr[nrt].l = tr[rt].l;
            nrt = tr[nrt].r;
            rt = tr[rt].r;
            l = mid + 1;
        }
        tr[nrt].sz = tr[rt].sz + cnt;
    }
    return tmp;
}
int lowbit(int x) {
    return x & (-x);
}
void add(int x, int y, int z) {
    for (; x <= n; x += lowbit(x)) {
        zxs[x] = update(zxs[x], y, z);
    }
}
int cnt1, cnt2, use1[N], use2[N];
void genlist(int x, int *a, int &p) {
    p = 0;
    for (; x; x -= lowbit(x)) {
        a[++p] = zxs[x];
    }
}
int query(int st, int ed, int k) {
    int lr = root[st - 1], rr = root[ed];
    genlist(ed, use1, cnt1);
    genlist(st - 1, use2, cnt2);
    int l = 1, r = p;
    while (l < r) {
        int mid = (l + r) >> 1, c = tr[tr[rr].l].sz - tr[tr[lr].l].sz;
        for (int i = 1; i <= cnt1; i++)c += tr[tr[use1[i]].l].sz;
        for (int i = 1; i <= cnt2; i++)c -= tr[tr[use2[i]].l].sz;
        if (c >= k) {
            for (int i = 1; i <= cnt1; i++)use1[i] = tr[use1[i]].l;
            for (int i = 1; i <= cnt2; i++)use2[i] = tr[use2[i]].l;
            rr = tr[rr].l;
            lr = tr[lr].l;
            r = mid;
        } else {
            for (int i = 1; i <= cnt1; i++)use1[i] = tr[use1[i]].r;
            for (int i = 1; i <= cnt2; i++)use2[i] = tr[use2[i]].r;
            rr = tr[rr].r;
            lr = tr[lr].r;
            l = mid + 1;
            k -= c;
        }
    }
    return l;
}
int main() {
    //freopen("in.txt","r",stdin);
    //freopen("out.txt","w",stdout);
    tot = 0;
    scanf("%d%d", &n, &m);
    for (int i = 1; i <= n; i++) {
        scanf("%d", &a[i]);
        b[i] = a[i];
        root[i] = 0;
    }
    p = n;
    char op[2];
    for (int i = 1; i <= m; i++) {
        scanf("%s", op);
        if (op[0] == 'Q') {
            q[i].op = 1;
            scanf("%d%d%d", &q[i].x, &q[i].y, &q[i].z);
        } else {
            q[i].op = 0;
            scanf("%d%d", &q[i].x, &q[i].y);
            b[++p] = q[i].y;
        }
    }
    sort(b + 1, b + p + 1);
    p = unique(b + 1, b + p + 1) - (b + 1);
    root[0] = build(1, p);
    for (int i = 1; i <= n; i++) {
        a[i] = get(a[i]);
        zxs[i] = root[0];
        root[i] = update(root[i - 1], a[i], 1);
    }
    for (int i = 1; i <= m; i++) {
        if (q[i].op) {
            printf("%d\n", b[query(q[i].x, q[i].y, q[i].z)]);
        } else {
            q[i].y = get(q[i].y);
            add(q[i].x, a[q[i].x], -1);
            add(q[i].x, q[i].y, 1);
            a[q[i].x] = q[i].y;
        }
    }
    return 0;
}
```

#### version2 segment tree in BIT

```cpp
const int N = 100010;
struct sgmt {
    int l, r, sz;
} tr[50000010];
struct rec {
    int op, x, y, z;
} q[N];
int root[N];
int tot, n, m, p;
int a[N], b[N << 1];
int get(int val) {
    return lower_bound(b + 1, b + p + 1, val) - b;
}
int newnode() {
    ++tot;
    tr[tot].l = tr[tot].r = tr[tot].sz = 0;
    return tot;
}
void update(int &p, int l, int r, int val, int cnt) {
    if (!p)p = newnode();
    tr[p].sz += cnt;
    if (l == r)return ;
    int mid = (l + r) >> 1;
    if (val <= mid) {
        update(tr[p].l, l, mid, val, cnt);
    } else {
        update(tr[p].r, mid + 1, r, val, cnt);
    }
}
inline int lowbit(int x) {
    return x & (-x);
}
void add(int x, int y, int z) {
    for (; x <= n; x += lowbit(x)) {
        update(root[x], 1, p, y, z);
    }
}
int cnt1, cnt2, use1[N], use2[N];
void genlist(int x, int *a, int &p) {
    p = 0;
    for (; x; x -= lowbit(x)) {
        a[++p] = root[x];
    }
}
int query(int l, int r, int k) {
    while (l < r) {
        int mid = (l + r) >> 1, c = 0;
        for (int i = 1; i <= cnt1; i++)c += tr[tr[use1[i]].l].sz;
        for (int i = 1; i <= cnt2; i++)c -= tr[tr[use2[i]].l].sz;
        if (c >= k) {
            for (int i = 1; i <= cnt1; i++)use1[i] = tr[use1[i]].l;
            for (int i = 1; i <= cnt2; i++)use2[i] = tr[use2[i]].l;
            r = mid;
        } else {
            for (int i = 1; i <= cnt1; i++)use1[i] = tr[use1[i]].r;
            for (int i = 1; i <= cnt2; i++)use2[i] = tr[use2[i]].r;
            l = mid + 1;
            k -= c;
        }
    }
    return l;
}
int main() {
    tot = 0;
    scanf("%d%d", &n, &m);
    for (int i = 1; i <= n; i++) {
        scanf("%d", &a[i]);
        b[i] = a[i];
    }
    p = n;
    char op[2];
    for (int i = 1; i <= m; i++) {
        scanf("%s", op);
        if (op[0] == 'Q') {
            q[i].op = 1;
            scanf("%d%d%d", &q[i].x, &q[i].y, &q[i].z);
        } else {
            q[i].op = 0;
            scanf("%d%d", &q[i].x, &q[i].y);
            b[++p] = q[i].y;
        }
    }
    sort(b + 1, b + p + 1);
    p = unique(b + 1, b + p + 1) - (b + 1);
    for (int i = 1; i <= n; i++) {
        a[i] = get(a[i]);
        add(i, a[i], 1);
    }
    for (int i = 1; i <= m; i++) {
        if (q[i].op) {
            genlist(q[i].y, use1, cnt1);
            genlist(q[i].x - 1, use2, cnt2);
            printf("%d\n", b[query(1, p, q[i].z)]);
        } else {
            q[i].y = get(q[i].y);
            add(q[i].x, a[q[i].x], -1);
            add(q[i].x, q[i].y, 1);
            a[q[i].x] = q[i].y;
        }
    }
    return 0;
}
```

#### version 3 treap in segment tree

```cpp
const int N = 200006;
const int INF = 1e9;
mt19937 myrand(time(0));
char s[10];
struct query {
    int op, x, y, z;
} q[N];
struct treap {
    int l, r, rnd, num, sz;
} T[N * 20];
struct sgmt {
    int l, r, sz, root;
} tr[N << 3];
int a[N], b[N << 1];
int w, tot, n, m;
//treap
int newnode(int val) {
    ++tot;
    T[tot].sz = 1;
    T[tot].num = val;
    T[tot].rnd = myrand();
    return tot;
}
void pushup(int p) {
    T[p].sz = 1 + T[T[p].l].sz + T[T[p].r].sz;
}
void lrotate(int &p) {
    int t = T[p].r;
    T[p].r = T[t].l;
    T[t].l = p;
    pushup(p);
    pushup(t);
    p = t;
}
void rrotate(int &p) {
    int t = T[p].l;
    T[p].l = T[t].r;
    T[t].r = p;
    pushup(p);
    pushup(t);
    p = t;
}
void insert(int &p, int val) {
    if (!p) {
        p = newnode(val);
        return ;
    }
    if (val < T[p].num) {
        insert(T[p].l, val);
        if (T[p].rnd < T[T[p].l].rnd)rrotate(p);
    } else {
        insert(T[p].r, val);
        if (T[p].rnd < T[T[p].r].rnd)lrotate(p);
    }
    pushup(p);
}
void erase(int &p, int val) {
    if (!p) {
        return ;
    }
    if (val == T[p].num) {
        if (T[p].l == 0 || T[p].r == 0) {
            p = T[p].l + T[p].r;
            if (p == 0)return ;
        } else {
            if (T[T[p].l].rnd > T[T[p].r].rnd) {
                rrotate(p);
                erase(T[p].r, val);
            } else {
                lrotate(p);
                erase(T[p].l, val);
            }
        }
    } else if (val < T[p].num) {
        erase(T[p].l, val);
    } else {
        erase(T[p].r, val);
    }
    pushup(p);
}
int getrank(int p, int val) {
    int ans = 0;
    while (p) {
        if (T[p].num <= val) {
            ans += T[T[p].l].sz + 1;
            if (T[p].num == val)break;
            p = T[p].r;
        } else {
            p = T[p].l;
        }
    }
    return ans;
}
//sgmt
void build(int rt, int l, int r) {
    tr[rt].l = l;
    tr[rt].r = r;
    tr[rt].root = 0;
    tr[rt].sz = 0;
    if (l == r)return;
    int mid = (l + r) >> 1;
    build(rt << 1, l, mid);
    build(rt << 1 | 1, mid + 1, r);
}
void Add(int rt, int pos, int val) {
    insert(tr[rt].root, pos);
    tr[rt].sz++;
    if (tr[rt].l == tr[rt].r)return ;
    int mid = (tr[rt].l + tr[rt].r) >> 1;
    if (val <= mid) {
        Add(rt << 1, pos, val);
    } else {
        Add(rt << 1 | 1, pos, val);
    }
}
void del(int rt, int pos, int val) {

    erase(tr[rt].root, pos);
    tr[rt].sz--;
    if (tr[rt].l == tr[rt].r)return ;
    int mid = (tr[rt].l + tr[rt].r) >> 1;
    if (val <= mid) {
        del(rt << 1, pos, val);
    } else {
        del(rt << 1 | 1, pos, val);
    }
}
int query(int rt, int l, int r, int k) {
    while (tr[rt].l != tr[rt].r) {
        int c = getrank(tr[rt << 1].root, r) - getrank(tr[rt << 1].root, l - 1);
        if (c >= k) {
            rt = rt << 1;
        } else {
            k -= c;
            rt = rt << 1 | 1;
        }
    }
    return tr[rt].l;
}
int get(int val) {
    return lower_bound(b + 1, b + w + 1, val) - b;
}
int main() {
    srand(time(NULL));
    tot = 0;
    int p = 0;
    scanf("%d%d", &n, &m);
    for (int i = 1; i <= n; i++) {
        scanf("%d", &a[i]);
        b[++p] = a[i];
    }
    for (int i = 1; i <= m; i++) {
        scanf("%s", s);
        if (s[0] == 'Q') {
            q[i].op = 0;
            scanf("%d%d%d", &q[i].x, &q[i].y, &q[i].z);
        } else {
            q[i].op = 1;
            scanf("%d%d", &q[i].x, &q[i].y);
            b[++p] = q[i].y;
        }
    }
    sort(b + 1, b + p + 1);
    w = unique(b + 1, b + p + 1) - (b + 1);
    build(1, 1, w);
    for (int i = 1; i <= n; i++) {
        a[i] = get(a[i]);
        Add(1, i, a[i]);
    }
    for (int i = 1; i <= m; i++) {
        if (q[i].op == 1) {
            q[i].y = get(q[i].y);
            del(1, q[i].x, a[q[i].x]);
            Add(1, q[i].x, q[i].y);
            a[q[i].x] = q[i].y;
        } else {
            printf("%d\n", b[query(1, q[i].x, q[i].y, q[i].z)]);
        }
    }
    return 0;
}
```

#### version 4 offline

```cpp
const int N = 100005;
const int INF = 1e9;
struct rec {
    int op, x, y, z;
} q[N * 3], lq[N * 3], rq[N * 3];
int ans[N];
int a[N], c[N];
int n, m;
void add(int x, int y) {
    while (x <= n) {
        c[x] += y;
        x += x & (-x);
    }
}
int query(int x) {
    int ans = 0;
    while (x) {
        ans += c[x];
        x -= x & (-x);
    }
    return ans;
}
void solve(int lval, int rval, int st, int ed) {
    if (st > ed)return ;
    if (lval == rval) {
        for (int i = st; i <= ed; i++) {
            if (q[i].op > 0) {
                ans[q[i].op] = lval;
            }
        }
        return ;
    }
    int mid = (lval + rval) >> 1;
    int lt = 0, rt = 0;
    for (int i = st; i <= ed; i++) {
        if (q[i].op <= 0) {
            if (q[i].y <= mid) {
                add(q[i].x, q[i].z);
                lq[++lt] = q[i];
            } else {
                rq[++rt] = q[i];
            }
        } else {
            int t = query(q[i].y) - query(q[i].x - 1);
            if (t >= q[i].z)lq[++lt] = q[i];
            else {
                q[i].z -= t;
                rq[++rt] = q[i];
            }
        }
    }
    for (int i = ed; i >= st; i--) {
        if (q[i].op <= 0 && q[i].y <= mid) {
            add(q[i].x, -q[i].z);
        }
    }
    for (int i = 1; i <= lt; i++)q[i + st - 1] = lq[i];
    for (int i = 1; i <= rt; i++)q[st - 1 + lt + i] = rq[i];
    solve(lval, mid, st, st + lt - 1);
    solve(mid + 1, rval, st + lt, ed);
}
char s[10];
int main() {
    int t = 0, p = 0;
    scanf("%d%d", &n, &m);
    for (int i = 1; i <= n; i++) {
        scanf("%d", &a[i]);
        q[++t].op = 0, q[t].x = i, q[t].y = a[i], q[t].z = 1;
    }
    for (int i = 1; i <= m; i++) {
        scanf("%s", s);
        if (s[0] == 'Q') {
            q[++t].op = ++p;
            scanf("%d%d%d", &q[t].x, &q[t].y, &q[t].z);
        } else {
            int x, y;
            scanf("%d%d", &x, &y);
            q[++t].op = -1;
            q[t].x = x, q[t].y = a[x], q[t].z = -1;
            q[++t].op = 0;
            q[t].x = x, q[t].y = y, q[t].z = 1;
            a[x] = y;
        }
    }
    solve(0, INF, 1, t);
    for (int i = 1; i <= p; i++) {
        printf("%d\n", ans[i]);
    }
    return 0;
}
```

### 8.2 Three-dimensional partial order

```cpp
int n, k;
const int N = 100010;
struct rec {
    int x, y, z, ans, w;
    bool operator<(const rec& tmp)const {
        if (y != tmp.y)return y < tmp.y;
        else return z < tmp.z;
    }
    bool operator==(const rec& tmp)const {
        return x == tmp.x && y == tmp.y && z == tmp.z;
    }
} b[N], tmp[N];
bool cmpx(const rec& a, const rec& b) {
    if (a.x != b.x)return a.x < b.x;
    else if (a.y != b.y)return a.y < b.y;
    else return a.z < b.z;
}
int c[N << 1], ans[N];
void add(int x, int y) {
    for (; x <= k; x += x & (-x)) {
        c[x] += y;
    }
}
int sum(int x) {
    int ans = 0;
    while (x) {
        ans += c[x];
        x -= x & (-x);
    }
    return ans;
}
void solve(int l, int r) {
    if (l == r)return ;
    int mid = (l + r) >> 1;
    solve(l, mid);
    solve(mid + 1, r);
    int i, j;
    for (i = mid + 1, j = l; i <= r; i++) {
        while (j <= mid && b[j].y <= b[i].y) {
            add(b[j].z, b[j].w);
            j++;
        }
        b[i].ans += sum(b[i].z);
    }
    while (j > l) {
        --j;
        add(b[j].z, -b[j].w);
    }
    int pl = l, pr = mid + 1, p = l;
    while (pl <= mid && pr <= r) {
        if (b[pl] < b[pr]) {
            tmp[p++] = b[pl++];
        } else {
            tmp[p++] = b[pr++];
        }
    }
    while (pl <= mid)tmp[p++] = b[pl++];
    while (pr <= r)tmp[p++] = b[pr++];
    for (int i = l; i <= r; i++)b[i] = tmp[i];
}
int main() {
    scanf("%d%d", &n, &k);
    for (int i = 1; i <= n; i++) {
        scanf("%d%d%d", &b[i].x, &b[i].y, &b[i].z);
        b[i].ans = 0;
        b[i].w = 1;
    }int n, k;
const int N = 100010;
struct rec {
    int x, y, z, ans, w;
    bool operator<(const rec& tmp)const {
        if (y != tmp.y)return y < tmp.y;
        else return z < tmp.z;
    }
    bool operator==(const rec& tmp)const {
        return x == tmp.x && y == tmp.y && z == tmp.z;
    }
} b[N], tmp[N];
bool cmpx(const rec& a, const rec& b) {
    if (a.x != b.x)return a.x < b.x;
    else if (a.y != b.y)return a.y < b.y;
    else return a.z < b.z;
}
int c[N << 1], ans[N];
void add(int x, int y) {
    for (; x <= k; x += x & (-x)) {
        c[x] += y;
    }
}
int sum(int x) {
    int ans = 0;
    while (x) {
        ans += c[x];
        x -= x & (-x);
    }
    return ans;
}
void solve(int l, int r) {
    if (l == r)return ;
    int mid = (l + r) >> 1;
    solve(l, mid);
    solve(mid + 1, r);
    int i, j;
    for (i = mid + 1, j = l; i <= r; i++) {
        while (j <= mid && b[j].y <= b[i].y) {
            add(b[j].z, b[j].w);
            j++;
        }
        b[i].ans += sum(b[i].z);
    }
    while (j > l) {
        --j;
        add(b[j].z, -b[j].w);
    }
    int pl = l, pr = mid + 1, p = l;
    while (pl <= mid && pr <= r) {
        if (b[pl] < b[pr]) {
            tmp[p++] = b[pl++];
        } else {
            tmp[p++] = b[pr++];
        }
    }
    while (pl <= mid)tmp[p++] = b[pl++];
    while (pr <= r)tmp[p++] = b[pr++];
    for (int i = l; i <= r; i++)b[i] = tmp[i];
}
int main() {
    //freopen("in.txt","r",stdin);
    //freopen("out.txt","w",stdout);
    scanf("%d%d", &n, &k);
    for (int i = 1; i <= n; i++) {
        scanf("%d%d%d", &b[i].x, &b[i].y, &b[i].z);
        b[i].ans = 0;
        b[i].w = 1;
    }
    sort(b + 1, b + n + 1, cmpx);
    int top = 1;
    for (int i = 2; i <= n; i++) {
        if (b[i - 1] == b[i]) {
            b[top].w++;
        } else {
            b[++top] = b[i];
        }
    }
    solve(1, top);
    for (int i = 1; i <= top; i++) {
        ans[b[i].ans + b[i].w - 1] += b[i].w;
    }
    for (int i = 0; i < n; i++) {
        printf("%d\n", ans[i]);
    }
    return 0;
}
    sort(b + 1, b + n + 1, cmpx);
    int top = 1;
    for (int i = 2; i <= n; i++) {
        if (b[i - 1] == b[i]) {
            b[top].w++;
        } else {
            b[++top] = b[i];
        }
    }
    solve(1, top);
    for (int i = 1; i <= top; i++) {
        ans[b[i].ans + b[i].w - 1] += b[i].w;
    }
    for (int i = 0; i < n; i++) {
        printf("%d\n", ans[i]);
    }
    return 0;
}
```

