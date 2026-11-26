import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
from t_sec6_heavy import geng, has_sq_g6, job_conj_direct
from multiprocessing import Pool
if __name__ == '__main__':
    n, d = sys.argv[1], sys.argv[2]
    t0 = time.time()
    gs = geng(['-d' + d, n])
    with Pool(int(os.environ.get('NPROC', '18'))) as pool:
        flags = pool.map(has_sq_g6, gs, chunksize=256)
    nons = [g for g, f in zip(gs, flags) if not f]
    print("n=%s d>=%s: total=%d contain_square=%d not=%d  (%.0fs)" % (n, d, len(gs), sum(flags), len(nons), time.time() - t0), flush=True)
    open('non_square_%s_%s.txt' % (n, d), 'w').write('\n'.join(nons) + '\n')
    with Pool(int(os.environ.get('NPROC2', '12'))) as pool:
        res = pool.map(job_conj_direct, nons, chunksize=1)
    disc = [r for r in res if r[2] > 0 and r[3] != 1]
    print("n=%s d>=%s: directly checked=%d no_HP=%d disconnected=%d max_paths=%d (%.0fs)"
          % (n, d, len(res), sum(1 for r in res if r[2] == 0), len(disc), max(r[2] for r in res), time.time() - t0), flush=True)
    for r in disc: print("  DISCONNECTED", r)
