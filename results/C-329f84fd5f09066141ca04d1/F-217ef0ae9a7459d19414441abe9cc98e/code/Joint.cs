using System;

// Joint prefix recognizers for 11223 and 11332.
internal static class Joint
{
    private const int INF = 15;
    private const ulong EmptyCandidates = 0xFFFFFFFFFFFFFFFFUL;
    private static int K, N, All;
    private static long P, Q;
    private static readonly long[,] Completion = new long[12,12];
    private static readonly long[,] Pop = new long[12,12];
    private static void Visit(int left, int seen, int miss, int aMin, ulong cand, int dMin, int qMask, int flags)
    {
        if (flags == 3)
        {
            long completions = Completion[left,miss];
            P += completions; Q += completions;
            return;
        }
        if (left == 0)
        {
            if (miss != 0) throw new Exception("invalid enumeration");
            if ((flags&1)!=0) P++;
            if ((flags&2)!=0) Q++;
            return;
        }
        int choices = left == miss ? (All ^ seen) : All;
        for (int x = 1; x <= K; ++x)
        {
            int bit = 1 << x;
            if ((choices&bit)==0) continue;
            bool had = (seen&bit)!=0;
            int nextFlags = flags;
            if (x > dMin) nextFlags |= 1;
            if ((qMask&bit)!=0) nextFlags |= 2;
            int nextD = dMin, nextQ = qMask;
            int shift = 4*x;
            int old = (int)((cand>>shift)&15);
            if (old != INF)
            {
                nextD = Math.Min(dMin,x);
                nextQ |= (1<<x) - (1<<(old+1));
            }
            ulong nextCand = cand;
            if (aMin < x && aMin < old)
                nextCand = (cand & ~(15UL<<shift)) | ((ulong)aMin<<shift);
            Visit(left-1,seen|bit,miss-(had?0:1),had?Math.Min(aMin,x):aMin,nextCand,nextD,nextQ,nextFlags);
        }
    }
    public static void Main()
    {
        Pop[0,0]=1;
        for(int n=1;n<=11;n++) for(int k=1;k<=n;k++) Pop[n,k]=k*(Pop[n-1,k]+Pop[n-1,k-1]);
        Console.WriteLine("n,k,hosts,avoid11223,avoid11332,difference");
        for(N=9;N<=11;N++)
        {
            long ap=0, aq=0;
            for(K=1;K<=N;K++)
            {
                P=Q=0;
                if(K>=3 && K<=N-2)
                {
                    All = (1<<(K+1))-2;
                    Array.Clear(Completion,0,Completion.Length);
                    Completion[0,0]=1;
                    for(int left=1;left<=N;left++)
                        for(int miss=0;miss<=K;miss++)
                            Completion[left,miss]=(K-miss)*Completion[left-1,miss]+(miss==0?0:miss*Completion[left-1,miss-1]);
                    if(Completion[N,K]!=Pop[N,K]) throw new Exception("population mismatch");
                    Visit(N,0,K,INF,EmptyCandidates,INF,0,0);
                }
                long a=Pop[N,K]-P, b=Pop[N,K]-Q;
                Console.WriteLine("{0},{1},{2},{3},{4},{5}",N,K,Pop[N,K],a,b,a-b);
                ap+=a; aq+=b;
            }
            Console.WriteLine("total,{0},{1},{2},{3}",N,ap,aq,ap-aq);
        }
    }
}