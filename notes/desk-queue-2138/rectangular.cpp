#include <algorithm>
#include <array>
#include <bit>
#include <climits>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;using U=uint32_t;using H=uint64_t;
struct C{H a,b,c;};C operator|(C x,C y){return {x.a|y.a,x.b|y.b,x.c|y.c};}
bool operator==(C x,C y){return x.a==y.a&&x.b==y.b&&x.c==y.c;}
int n,m,k,lim,vis;U t;C full;string id,fn;vector<U> inputs;
struct G{U a,b,z; bool op;};vector<G> gates;
unordered_map<U,C> cache;H mix(H x){x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return x^(x>>31);}
using State=array<U,16>;
struct Hash {size_t operator()(State const& s)const{H h=0;for(U x:s)h=mix(h^x);return h;}};
unordered_set<State,Hash> dead;
C cut(U x){
 auto f=cache.find(x);if(f!=cache.end())return f->second;
 array<H,3> a{};int s=0;for(int i=0;i<n*m;i++)if((t>>i)&1)for(int j=0;j<n*m;j++)if(!(t>>j&1)){
 if((x>>i&1)&&!(x>>j&1))a[s/64]|=1ULL<<(s%64);s++;
 }
 return cache[x]=C{a[0],a[1],a[2]};
}
bool dfs(vector<U> const&w,int left){
 if(find(w.begin(),w.end(),t)!=w.end())return true;
 if(w.size()<2||left<1||vis>=lim)return false;
 State sig{};sig[0]=left;copy(w.begin(),w.end(),sig.begin()+1);
 sort(sig.begin()+1,sig.begin()+1+w.size());if(!dead.insert(sig).second)return false;
 vis++;
 vector<C> cw; for(auto a:w)cw.push_back(cut(a));
 int extra=left+1-w.size();
 for(int i=0;i<w.size();i++)for(int j=i+1;j<w.size();j++){
   vector<U> rest;C cover{};for(int h=0;h<w.size();h++)if(h!=i&&h!=j){rest.push_back(w[h]);cover=cover|cw[h];}
   for(bool op:{false,true}){
     U z=op?(w[i]|w[j]):(w[i]&w[j]);if(!z||find(w.begin(),w.end(),z)!=w.end())continue;
     C c=cover|cut(z);gates.push_back({w[i],w[j],z,op});rest.push_back(z);
     if(z==t)return true;
     if(c==full&&dfs(rest,left-1))return true;
     if(extra>=1){
       rest.push_back(w[i]);if((c|cw[i])==full&&dfs(rest,left-1))return true;
       if(extra>=2){rest.push_back(w[j]);if((c|cw[i]|cw[j])==full&&dfs(rest,left-1))return true;rest.pop_back();}
       rest.back()=w[j];if((c|cw[j])==full&&dfs(rest,left-1))return true;rest.pop_back();
     }
     rest.pop_back();gates.pop_back();
   }
 }
 return false;
}
void solve(){
 inputs.clear();cache.clear();dead.clear();gates.clear();vis=0;
 full=cut(t);
 for(int i=0;i<n+m;i++){U x=0;for(int q=0;q<n*m;q++)if(q/m==i||q%m+n==i)x|=1<<q;inputs.push_back(x);}
 for(int mask=1;mask<1<<(n+m);mask++)if(popcount((unsigned)mask)<=k+1){
   vector<U>w;C c{};for(int i=0;i<n+m;i++)if(mask>>i&1){w.push_back(inputs[i]);c=c|cut(inputs[i]);}
   if(!(c==full))continue;
   if(dfs(w,k)){
     ofstream f(fn+"-"+id+".txt");unordered_map<U,int> ids;for(int i=0;i<n+m;i++)ids[inputs[i]]=i;
     int next=n+m;for(auto g:gates){f<<(g.op?"or ":"and ")<<ids.at(g.a)<<" "<<ids.at(g.b)<<"\n";ids[g.z]=next++;}
     cout<<id<<" "<<t<<" size "<<gates.size()<<" nodes "<<vis<<endl;return;
   }
 }
 cerr<<id<<" "<<vis<<(vis>=lim?" timeout":" exhausted")<<endl;
}
int main(int argc,char**argv){fn=argv[1];ifstream f(fn);f>>n>>m;lim=stoi(argv[2]);while(f>>id>>t>>k)solve();}
