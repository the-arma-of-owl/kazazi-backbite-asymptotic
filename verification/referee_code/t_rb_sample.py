import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t_sec6_heavy import geng, job_rb
from multiprocessing import Pool
if __name__ == '__main__':
    procs = int(os.environ.get('NPROC', '18'))
    sparse = geng(['-d5', '10', '25:26'])
    allg = geng(['-d5', '10'])
    rng = random.Random(2026); sample = rng.sample(allg, int(sys.argv[1]))
    for name, gs in (('sparsest (25-26 edges)', sparse), ('random sample', sample)):
        with Pool(procs) as pool:
            res = pool.map(job_rb, gs, chunksize=2)
        fails = [r for r in res if r[2]]
        print("R_b n=10 d>=5 %s: graphs=%d failing=%d %s" % (name, len(res), len(fails), fails[:3]), flush=True)
