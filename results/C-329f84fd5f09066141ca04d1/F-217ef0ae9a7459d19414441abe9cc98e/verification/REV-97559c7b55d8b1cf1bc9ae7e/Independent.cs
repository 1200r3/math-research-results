using System;
using System.Collections.Generic;
class Independent {
static int[] w=new int[11], rank=new int[11]; static long[] fac=new long[12]; static long P,Q; static long[] B=new long[4]; static string[] pats={"112112","121112","111212","112121"}; static long partitions;
static void Gen(int i,int k){if(i==11){Leaf(k);return;}for(int x=0;x<=k;x++){w[i]=x;Gen(i+1,Math.Max(k,x+1));}}
static void Perm(int i,int h,int[] active,List<int[]> ts,long mult){if(i==h){bool p=false,q=false;foreach(var t in ts){int a=rank[t[0]],d=rank[t[1]],x=rank[t[2]];if(a<d&&d<x)p=true;if(a<x&&x<d)q=true;}if(!p)P+=mult;if(!q)Q+=mult;return;}for(int j=i;j<h;j++){int v=active[i];active[i]=active[j];active[j]=v;rank[active[i]]=i;Perm(i+1,h,active,ts,mult);v=active[i];active[i]=active[j];active[j]=v;}}
static void Leaf(int k){partitions++;var ts=new List<int[]>();bool[,,] seen=new bool[k,k,k];int mask=0;
for(int a=0;a<7;a++)for(int b=a+1;b<8;b++)if(w[a]==w[b])for(int c=b+1;c<9;c++)if(w[c]!=w[a])for(int d=c+1;d<10;d++)if(w[c]==w[d])for(int e=d+1;e<11;e++)if(w[e]!=w[a]&&w[e]!=w[c]&&!seen[w[a],w[c],w[e]]){seen[w[a],w[c],w[e]]=true;ts.Add(new int[]{w[a],w[c],w[e]});mask|=(1<<w[a])|(1<<w[c])|(1<<w[e]);}
var ac=new List<int>();for(int i=0;i<k;i++)if((mask&(1<<i))!=0)ac.Add(i);Perm(0,ac.Count,ac.ToArray(),ts,fac[k]/fac[ac.Count]);
for(int p=0;p<4;p++){int[] pre=new int[k];for(int u=0;u<k;u++)for(int v=0;v<k;v++)if(u!=v){int at=0;for(int j=0;j<11&&at<6;j++)if(w[j]==(pats[p][at]=='1'?u:v))at++;if(at==6)pre[u]|=1<<v;}long[] dp=new long[1<<k];dp[0]=1;for(int s=0;s<dp.Length;s++)if(dp[s]!=0)for(int x=0;x<k;x++)if((s&(1<<x))==0&&(pre[x]&s)==pre[x])dp[s|(1<<x)]+=dp[s];B[p]+=dp[dp.Length-1];}}
static void Main(){fac[0]=1;for(int i=1;i<12;i++)fac[i]=i*fac[i-1];Gen(0,0);Console.WriteLine("partitions,"+partitions);Console.WriteLine("11223,11,"+P);Console.WriteLine("11332,11,"+Q);for(int i=0;i<4;i++)Console.WriteLine(pats[i]+",11,"+B[i]);if(partitions!=678570||P!=1445533180||Q!=1445533200||B[0]!=1616420895||B[1]!=1616420896||B[2]!=1616424886||B[3]!=1616424885)throw new Exception("mismatch");}}
