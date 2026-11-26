// sabituc.c — Her tepe b için: arka ucu b olan Hamilton yolları, yalnız ön uç
// backbite'larıyla (Pósa rotasyonları) tek bileşen mi? graph6 girdi.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXN 16
typedef uint64_t u64;
static int n; static unsigned adj[MAXN];
static int parse_g6(const char *s){const unsigned char*p=(const unsigned char*)s;int nn=p[0]-63;if(nn<1||nn>MAXN)return -1;n=nn;memset(adj,0,sizeof adj);p++;int k=0;for(int j=1;j<n;j++)for(int i=0;i<j;i++){int by=p[k/6]-63;if((by>>(5-k%6))&1){adj[i]|=1u<<j;adj[j]|=1u<<i;}k++;}return n;}
static u64 *paths; static size_t np, cap; static int stk[MAXN]; static int B;
static void push(void){u64 c=0;for(int i=0;i<n;i++)c=(c<<4)|(u64)stk[i];if(np==cap){cap=cap?cap*2:65536;paths=realloc(paths,cap*8);}paths[np++]=c;}
// yollar: stk[n-1]=B; önden geriye kur, sonra ters çevir -> stk[0] ön uç
static int tmp[MAXN];
static void dfs(int d, unsigned used){ // tmp[0]=B, tmp[d-1] son eklenen
    if(d==n){for(int i=0;i<n;i++)stk[i]=tmp[n-1-i];push();return;}
    unsigned c=adj[tmp[d-1]]&~used; while(c){int w=__builtin_ctz(c);c&=c-1;tmp[d]=w;dfs(d+1,used|(1u<<w));}
}
static int cmpu(const void*a,const void*b){u64 x=*(const u64*)a,y=*(const u64*)b;return x<y?-1:x>y;}
static long findc(u64 c){size_t lo=0,hi=np;while(lo<hi){size_t m=(lo+hi)/2;if(paths[m]<c)lo=m+1;else hi=m;}return(lo<np&&paths[lo]==c)?(long)lo:-1;}
static uint32_t *par; static uint32_t f(uint32_t x){while(par[x]!=x){par[x]=par[par[x]];x=par[x];}return x;}
int main(void){
    char line[256]; long graphs=0, bad=0;
    while(fgets(line,sizeof line,stdin)){
        line[strcspn(line,"\r\n")]=0; if(!line[0]||line[0]=='>')continue; if(parse_g6(line)<0)continue; graphs++;
        int worst=1; int worstb=-1;
        for(B=0;B<n;B++){
            np=0; tmp[0]=B; dfs(1,1u<<B); if(np==0)continue;
            qsort(paths,np,8,cmpu);
            par=realloc(par,np*4); for(size_t i=0;i<np;i++)par[i]=i;
            int q[MAXN],t[MAXN];
            for(size_t id=0;id<np;id++){
                u64 c=paths[id]; for(int i=n-1;i>=0;i--){q[i]=c&15;c>>=4;}
                for(int k=2;k<n;k++){ if(!((adj[q[0]]>>q[k])&1))continue;
                    int m=0; for(int i=k-1;i>=0;i--)t[m++]=q[i]; for(int i=k;i<n;i++)t[m++]=q[i];
                    u64 cc=0; for(int i=0;i<n;i++)cc=(cc<<4)|(u64)t[i];
                    long j=findc(cc); if(j<0){fprintf(stderr,"hata\n");return 2;}
                    uint32_t a=f(id),b=f((uint32_t)j); if(a!=b)par[a]=b; }
            }
            long comps=0; for(size_t i=0;i<np;i++) if(f(i)==i)comps++;
            if(comps>worst){worst=comps;worstb=B;}
        }
        if(worst>1){bad++; if(bad<=5)printf("SABIT_UC_BAGLANTISIZ %s b=%d bilesen=%d\n",line,worstb,worst);}
    }
    printf("OZET graf=%ld sabit_uc_baglantisiz=%ld\n",graphs,bad); return 0;
}
