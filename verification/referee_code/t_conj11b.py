import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bb import *
from t_sec6_heavy import job_conj_direct
from multiprocessing import Pool

if __name__ == '__main__':
    nons = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    t0 = time.time(); done = 0; disc = []; mx = 0; nohp = 0
    with Pool(int(os.environ.get('NPROC2', '10'))) as pool:
        for r in pool.imap_unordered(job_conj_direct, nons, chunksize=1):
            done += 1; mx = max(mx, r[2]); nohp += (r[2] == 0)
            if r[2] > 0 and r[3] != 1:
                disc.append(r); print("DISCONNECTED", r, flush=True)
            if done % 10 == 0 or done == len(nons):
                print("done %d/%d disconnected=%d no_HP=%d max_paths=%d (%.0fs)"
                      % (done, len(nons), len(disc), nohp, mx, time.time() - t0), flush=True)
