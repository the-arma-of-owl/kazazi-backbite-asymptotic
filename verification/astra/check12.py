"""Enumerate edge-minimal graphs via their induced graph on degree-six vertices.

Usage: python check12.py path/to/geng path/to/minimal
"""

import subprocess
import sys

geng, checker = sys.argv[1:]
for high in range(6):
    low = 12 - high
    max_edges = (6 * low - 7 * high) // 2
    min_edges = ((6 - high) * low + 1) // 2
    if min_edges > max_edges:
        print(f"high={high}: no solutions (incompatible edge counts)", flush=True)
        continue
    cmd = [geng, "-q", f"-d{6 - high}", "-D6", str(low), f"{min_edges}:{max_edges}"]
    with subprocess.Popen(cmd, stdout=subprocess.PIPE) as producer:
        subprocess.run([checker, str(high)], stdin=producer.stdout, check=True)
        assert producer.wait() == 0
