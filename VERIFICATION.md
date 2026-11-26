# VERIFICATION — referee report on `paper/asymptotic_threshold.md` (Version 1, 26 Nov 2026)

Independent adversarial check. I re-derived every step of §1–§5 and asserted every backbite claim (exact resulting path order) with my own code. I also re-ran the computational claims of §6 with my own Python code, not the repository binaries. Line numbers refer to `paper/asymptotic_threshold.md`.

## 1. Verdicts

| Item | Verdict |
|---|---|
| Fact 2 (crossings) | CORRECT |
| Fact 3 (interval reversal) | CORRECT (tacitly needs $a\neq b$; see issue 5c) |
| Lemma 1 (forcing ⇒ connectivity) | CORRECT |
| Lemma 2 (blow-up is forcing) | CORRECT WITH MINOR FIXES (degenerate cases, issue 5) |
| Lemma 4 (vertex extension) | CORRECT |
| Lemma 5 (typical core) | CORRECT |
| §5 and **Theorem 1** | **CORRECT** |
| Remark 1 | ERROR (minor: the bound is doubly exponential, not tower-type) |
| Remark 3 | GAP (unused; the "same proof" needs one change, given below) |
| §6 item 6 ("3×m grid is forcing") | **ERROR**; contradicted by the authors' own data and by my check |
| §6 item 3 ("the 5 such graphs") | CORRECT WITH MINOR FIXES: the 5 codes are one graph up to isomorphism |
| §6 items 1, 2, 4, 5, 7 and the rest of 6 | Reproduced where feasible (§4 below) |

**Overall:** I found no mathematical error in the proof of Theorem 1. The errors are in §6 and in the remarks, and they do not affect the theorem.

## 2. Issues: location, problem, fix

1. **§6 item 6, line 281: ERROR.** "the 3×m grid" is listed among the graphs that are "forcing for all $n\le12$ tested". The authors' own `data/forcing_skeletons.txt` records `grid3 n=12 … DEGIL(ii)`, and I confirmed it independently.
   - Take $J=P_4\square P_3$, with vertex $3i+r$ for column $i\in\{0..3\}$ and row $r\in\{0,1,2\}$.
   - The ordering $(0,3,4,5,2,1,7,10,9,6,8,11)$ has $\beta=2$; its bad edges are $1$–$7$ and $6$–$8$.
   - Its forward closure under $J$-adding backbites has exactly **4** orderings: $(0,3,4,5,2,1,7,10,9,6,8,11)$, $(0,3,4,5,2,1,7,10,11,8,6,9)$, $(2,5,4,3,0,1,7,10,9,6,8,11)$ and $(2,5,4,3,0,1,7,10,11,8,6,9)$. None of them is a Hamiltonian path of $J$, so (ii) fails.
   - $R(P_4\square P_3)$ itself is connected (62 paths). The 3×3 grid is forcing.
   - **Fix:** "the 3×3 grid ($n=9$) is forcing; the 3×4 grid ($n=12$) is not (an unreachable ordering is …)".

2. **§6 item 3, line 263: misleading count.** "The graph6 codes of the 5 such graphs found in this family". All 5 codes in `data/hamiltonian_disconnected.txt` have the same `labelg` canonical form, `I?_XIUOWG`. Moreover, all 20 unreachable orderings $P$ of $C_{10}$ give isomorphic graphs $C_{10}\cup E(P)$. **Fix:** "up to isomorphism this family contains one graph; 5 labelled copies are listed". The example itself is correct (§4).

3. **Remark 1, line 244: ERROR (minor).** No regularity-type iteration occurs, so the bound is **doubly exponential, not tower-type**.
   - The proof takes $k$ with $k e^{-18\alpha^2k}<1/4$ and $e^{-32\alpha^2k}/\alpha^2<1/4$, i.e. $k=\Theta(\gamma^{-2}\log(1/\gamma))$.
   - Then $L=t+k=\Theta(k/\alpha)$.
   - Erdős gives $\mathrm{ex}(N,K^{(k)}(L,\dots,L))\le N^{k-L^{1-k}}$, so it needs $n\gtrsim (k^k/c)^{L^{k-1}}$ with $c=2^{-\binom k2}/4$.
   - Hence $n_0(\gamma)=\exp\exp\big(O(\gamma^{-2}\log^2(1/\gamma))\big)$. Numerically, for $\gamma=0.1$: $k\approx15{,}739$, $L\approx2.5\cdot10^6$, and $\log_{10}\log_2 n_0\approx1.0\cdot10^5$.
   - **Fix:** replace "tower-type" by "doubly exponential".

4. **Remark 3, line 246: GAP (the remark is unused).** The claim is that "$\sigma_2(H)\ge h+2$ and $d\ge(h+3)/2$ suffice, by the same proof".
   - **Why the proof as written fails.** Step 1 of "Every path reaches $\mathcal K$" uses $\delta(G)>(h+1)/2$ to apply Fact 2 in $G$, and $\sigma_2(H)\ge h+2$ does not give this.
   - **Example.** Let $H$ be $K_{h-1}$ plus a vertex $x$ joined to 4 clique vertices; then $\sigma_2(H)=h+2$. Let $v$, with $d=\lceil (h+3)/2\rceil$, be non-adjacent to $x$. A Hamiltonian path of $G$ with ends $v,x$ has $d(v)+d(x)-h\le0$ for $h\ge11$, so Fact 2 guarantees no crossing.
   - **Fix (the remark is then true).**
     - If $v$ is an end of $Q$, then $Q=(v,a,\dots,b)$ is already in the form of step 2. Go to step 3: Fact 2 in $H$ gives $\ge3$ crossings.
     - If $v$ is interior, both ends lie in $H$, and $d_G(x)+d_G(y)\ge h+2$ gives $\ge2$ crossings in $G$.
     - Elsewhere: (a) needs one crossing avoiding $e,f$, and 3 are available; (b) needs 2 eligible edges, and $2d-h-1\ge2$.

5. **Lemma 2(i), lines 95–114: degenerate cases that need a sentence each.** None affects correctness.
   - (a) The Claim is about trails with a fixed start and end. Say that both circuits are cut at a vertex of $W_1$ (cycle position 0). The realisations only reverse intervals strictly inside $(p,q)$, so the cut vertex never moves.
   - (b) Case 1 of the Claim can reverse the **whole** closed trail: this happens when $e$ is the last edge, traversed $y\to x$. That trail is not "proper". It is realised trivially, since it is the same cycle read backwards.
   - (c) Twin swap (lines 112–114). The first reversal (of $xUy$) applies Fact 3 with $a$ the last vertex of $V$ and $b$ the first vertex of $V$.
     - If $|V|=1$ then $a=b$, and Fact 3's proof breaks: $u_t$ would be the second vertex.
     - In that case reversing $xUy$ leaves the cycle unchanged.
     - My simulation hit this case 127–440 times per instance (for example 410 times for $J(1,2,3,3)$).
     - **Fix:** add "if $|V|=1$ the first reversal is trivial", and state $a\ne b$ in Fact 3.

6. **Attribution and references.**
   - (a) Line 53: "Kazazi's theorem [K, Thm 1.1] says that the square of a Hamiltonian path is forcing". Thm 1.1 states connectivity. Forcing is what its *proof* gives: [K, Cor. 3.4] with $J=K_n$ (allowed, since [K, §3] assumes only $E(P_n^2)\subseteq E(J)$), plus [K, Prop. 5.1]. In Cor. 3.4 the rotation must stop at the first bad edge. I checked computationally that $P_n^2$ is forcing for $n=6,\dots,10$.
   - (b) Lemma 2(ii) follows [K, §3] (Lemma 3.1 to Cor. 3.4) closely: the bad-edge potential $\beta$, free-endpoint advancing, then close-and-rotate. Say so explicitly.
   - (c) Fact 2 is the classical Ore/Pósa crossing argument. Dirac's and Ore's theorems are used but are not in the reference list.
   - (d) [FK] and [KPS] are listed but never cited in the text.

7. **Presentation.**
   - The numbering skips: Theorem 1, Lemma 1, Fact 2, Fact 3, Lemma 2, Lemma 4, Lemma 5, and there is no Lemma 3. Use one counter.
   - "property (F)" (line 275) is not defined in the text; write "forcing".
   - Remark 2: $K_{n/2,n/2}$ is bipartite, not "near-bipartite".
   - §6 item 6 says "for all $n\le12$ tested", but each skeleton was tested only at some $n$ (e.g. grid at 9 and 12). Say which.

## 3. Mathematical checks (index bookkeeping)

Notation: positions are 1-indexed from the active endpoint.

### Basics
- $\mathrm{bb}(w_1,w_k)\mapsto(w_{k-1},\dots,w_1,w_k,\dots,w_n)$.
- Inverse: in the result, $w_k$ is at position $k\ge3$ and its predecessor is $w_1$, so $\mathrm{bb}(w_{k-1},w_k)$ restores the path.
- Rotation: $C-xy=(x{=}w_1,\dots,w_n{=}y)$, and $\mathrm{bb}(w_1,w_n)$ deletes $w_{n-1}w_n$. ✓

### Fact 2
- $N(a)\subseteq\{w_2..w_h\}$ gives $|S|=d(a)$, and $N(b)\subseteq\{w_1..w_{h-1}\}$ gives $|T|=d(b)$.
- $ab\notin E$ gives $1\notin T$ and $h-1\notin S$.
- For $i\in S\cap T$:
  - $\mathrm{bb}(a,w_{i+1})$: position $i+1\ge3$. Result $(w_i,\dots,w_1,w_{i+1},\dots,w_h)$, with ends $w_i,b$ adjacent.
  - $\mathrm{bb}(b,w_i)$: position $h-i+1\ge3$. Result $(w_{i+1},\dots,w_h,w_i,\dots,w_1)$, with ends $w_{i+1},a$ adjacent.
  - Both delete $w_iw_{i+1}$. ✓
- The Ore corollary (line 38) holds. ✓

### Fact 3
- Take the cycle $(a,u_1,\dots,u_t,b,c_1,\dots,c_r)$ and delete $au_1$. Read from $a$, the path is $(a,c_r,\dots,c_1,b,u_t,\dots,u_1)$.
- $u_t$ is at position $r+3\ge3$ and its predecessor is $b$.
- $\mathrm{bb}(a,u_t)$ gives $(b,c_1,\dots,c_r,a,u_t,\dots,u_1)$. Closing with $u_1b$ gives the reversed cycle. ✓ (Needs $a\ne b$.)

### Lemma 1
✓ A $J$-adding backbite on a Hamiltonian path of $G$ is a backbite of $G$, and $R(J)\subseteq R(G)$.

### Lemma 2(ii)
- **Advancing.**
  - $x$ is at position 1, so every $y\in W_{i+1}$ has a predecessor, and predecessors are injective.
  - $s_{i+1}>s_i$ holds for every $i\le k-2$, including $s_{k-1}>s_{k-2}$. So some $y$ has its predecessor $z\notin W_i$. Hence $z\ne x$ and $y$ is at position $\ge3$.
  - $\mathrm{bb}(x,y)$ gives $(z,\dots,x,y,\dots)$, and the fixed end stays, even if $y$ is the fixed end.
  - $N_{T_k}(i+1)\subseteq\{i,\,i+2,\,k\ (\text{if }i+1=k-2)\}$ for $i\le k-2$, with minimum $i$, so $m>i$. At most $k-2$ steps. ✓
- **Closing.**
  - All targets in $L'\cup W_{k-2}$ are complete to $x\in L$, and $|L'|+s_{k-2}>|L|+s_{k-3}$.
  - If $y\in L'$, then $N(y)=W_{k-2}\cup L$, so $z\in W_{k-2}$. If $y\in W_{k-2}$, then $z\in W_{k-3}\cup L\cup L'$, so $z\in L'$.
  - The other end $x'\in L$ is never a target or a predecessor. The new ends $z,x'$ are adjacent. ✓
- **Descending.** A rotation (backbite at $p_n$ with target $p_1$) is the cyclic shift $(p_1..p_n)\mapsto(p_2,\dots,p_n,p_1)$ and deletes $p_1p_2$. Repeated rotations move the gap one way. Added edges are $e$ or earlier good deletions. The first bad deletion makes $\beta$ drop by exactly 1. ✓

### Lemma 2(i)
- **Multiplicities.** $m_{12}=2s_1$, $m_{i,i+1}=2s_i-m_{i-1,i}$ for $2\le i\le k-3$, and the triangle values come from the three pairwise sums. ✓ With Lemma 5's sizes, e.g. $m_{23}=2$. I compared these against random Hamiltonian cycles. ✓
- **Claim.** In case 3, the target suffix is one trail from $y$ on $E(A)\cup E(B)$, so it is connected and $V(A)\cap V(B)\neq\emptyset$. Reversing $A_2eB_1$ (a closed trail at $z$) turns $e$ around; then case 1 applies; then induct. ✓
- **Realisation.**
  - A closed subtrail between positions $p<q$ has distinct cycle vertices $C_p\ne C_q$ of the same class, unless $(p,q)=(0,n)$.
  - Reverse $C_{p+1..q-1}$. The new edges $C_pC_{q-1}$ and $C_{p+1}C_q$ exist by twinship, and Fact 3 applies. ✓
- **Twin swap.** Two Fact 3 reversals: $xUyV\to yU^RxV\to yUxV$. ✓ See issue 5 for the degenerate cases.

### Lemma 4
- **Same attachment point, other direction.**
  - $(v,a,b',\dots,b)$: from $b$, $a$ is at position $h\ge3$ with predecessor $b'$.
  - The result is $(v,a,b,\dots,b')$. ✓
- **Moving to $c\ne a$.**
  - $(v,a,A,c,B,b)$: $\mathrm{bb}(v,c)$ has $c$ at position $|A|+3$ and gives $(A^R,a,v,c,B,b)$.
  - Then $\mathrm{bb}(b,a)$: $a$ is at position $|B|+4$ with predecessor $v$, giving $(v,c,B,b,a,A)$. This traverses $D$ from $c$ and ends at $c$'s other $D$-neighbour. ✓
  - The case $c=b$: $(v,a,A,b)\to(A^R,a,v,b)\to(v,b,a,A)$. ✓ ($A$ and $B$ may be empty in the general case. If $A=\emptyset$, the second target $a$ is the other endpoint, at position $n$.)
- $D_{xy}-vy=(v,x,\dots,y)$ is an attachment. ✓
- **Eligible edges.** There are at most $h-d+1$ runs, so at least $2d-h-1\ge3$ eligible edges. ✓
- **(a)** Fact 2 in $H$ gives $\ge5$ crossings with distinct deleted edges. With $v$ placed in a retained edge, the crossing backbite has the same target and predecessor in $P_e$, and the prefix reversal carries $v$ along. The result is $P'_e$. ✓
- **(b)** The same argument. ✓
- **Every path reaches $\mathcal K$.**
  - Fact 2 in $G$ gives $\ge4$ crossings.
  - Rotate to $C-(\text{edge at }v)=(v,a,\dots,b)$.
  - A Fact 2 backbite in $H$ from the $b$-end ($w_i$ at position $h-i+1\ge3$) gives $(v,w_1..w_i,w_h..w_{i+1})$. This is an attachment to $D$.
  - $d>h/2$ gives consecutive $x,y\in N(v)$ on $D$, and $D_{xy}-g$ is a lift. ✓

### Lemma 5
- $(1/2+16\alpha)(k-1)\ge(1/2+15\alpha)k \iff \alpha k\ge 1/2+16\alpha$, which holds for $k\ge1/\alpha$ and $\alpha\le1/32$.
- Hoeffding exponents: $2(3\alpha k)^2/(k-1)\ge18\alpha^2k$ and $2(4\alpha k)^2/k=32\alpha^2k$. Markov: $e^{-32\alpha^2k}/\alpha^2$.
- $(n)_k/2\ge n^k/4$.
- **Box.** In the $k$-partite $k$-graph on $[n]\times[k]$, each edge meets each copy once. So the parts of any $K^{(k)}(L,\dots,L)$ lie in distinct copies: if part $P_1$ met two copies, two edges sharing the other $k-1$ vertices would place those vertices in two different sets of copies. Distinct coordinates then give disjoint $D_i$. ✓
- **$T_k\subseteq F$.** The common neighbour exists since $2\delta-k>0$. $F-\{b,c\}$ has $\delta\ge(k-2)/2$ on $k-2\ge3$ vertices, so Dirac applies. Path ending at $a$, then $b,c$, plus the edge $ac$. ✓
- **Remaining inequalities.**
  - $(t+1)/(t+k)\ge1-\alpha$ for $t\ge k/\alpha$.
  - $(1/2+12\alpha)(1-\alpha)\ge1/2+8\alpha$ and $(1/2+10\alpha)(1-\alpha)\ge1/2+8\alpha$.
  - $p(x)\ge(1-\pi_x)(1/2+12\alpha)$, and $\pi_x>2\alpha/(1/2+12\alpha)\ge2\alpha$ for $\alpha\le1/24$.
  - $\sum_x\pi_x=\mathbb E\,\#\{\text{atypical }x\}\le\alpha^2n$ because every transversal is good. ✓
  - All of these were checked in exact rational arithmetic over $\alpha=1/N$, $32\le N<5000$.

### §5
- $d_U(x)\ge(1/2+15\alpha)n$.
- (1) for $j=0$: $8\alpha s\ge6$.
- Conditional samples have size $j-1$ or $j$ and neighbour proportion $\ge1/2+14\alpha$ in $U\setminus\{x\}$. The empty-sample case is $j=1$: then $(1/2+8\alpha)s\ge(s+1)/2+2$.
- Margin $8\alpha s+14\alpha j-3\ge4\alpha(s+j)$ from $4\alpha s^*\ge3$, then $2u^2/q\ge32\alpha^2(s+j)^2/j\ge32\alpha^2(s+j)$. The union bound has $s+j+1$ events per $j$.
- (1) gives exactly the hypotheses of Lemma 4 for $H_j\to H_{j+1}$.
- Adding $B$: $(1/2+16\alpha)n-\alpha n/2\ge n/2+2$ for large $n$. ✓

### Cited theorems
- Hoeffding [H] (Thm 1, and §6/Thm 4 for sampling without replacement) is used correctly. Numerically, the exact hypergeometric lower tail never exceeded $e^{-2u^2/q}$ in 14,000 random cases.
- Erdős [E] is used correctly (ordered version via the reduction above).
- Dirac is used correctly.

### Novelty
The result is not implied by [K].
- A spanning $P_n^2$ forces $\alpha(G)\le\lceil n/3\rceil$, because an independent set meets each consecutive triple at most once.
- Example: $K_{a,a,n-2a}$ with $a=\lceil n/3\rceil+1$ has $\delta=n-a\approx 2n/3-1$, which is at least $(1/2+\gamma)n$ for $\gamma<1/6$. But its independence number is $a$, so it has no spanning $P_n^2$.
- Hence Theorem 1 is a genuine extension of [K, Cor. 1.2(a)] in the range $\gamma<1/6$. For $\gamma\ge1/6$, [K] already applies.
- The lower bound $\delta=\lfloor n/2\rfloor-3$ ([K, Thm 7.1]) and Conjecture 7.8 are quoted correctly.

## 4. Computations run (own code, `python3 -I`)

The code is in [`verification/referee_code/`](verification/referee_code/) (path updated when the report was added to the repository). The library is `bb.py`: backbites, Hamiltonian paths, union–find $R(G)$, graph6, square-path test. Graph lists come from nauty `geng`; `labelg` was used only for isomorphism.

| Check | Script | Result |
|---|---|---|
| §6.3: $C_{10}$ + edges of $0,1,7,8,9,4,3,2,6,5$ | `t_sec6_quick.py` | $=C_{10}+\{17,26,49\}$, $\delta=2$, Hamiltonian, 22 paths, $R(G)$ = 18 + 4 ✓. The 4-path component: (0,1,7,8,9,4,3,2,6,5), (0,1,7,8,9,4,5,6,2,3), (3,2,6,5,4,9,0,1,7,8), (5,6,2,3,4,9,0,1,7,8) |
| §6.3: the 5 graph6 codes | `t_sec6_quick.py`, `t_c10family.py`, `labelg` | each gives 18 + 4 ✓, but all 5 are isomorphic, and all 20 unreachable $P$ give one graph (issue 2) |
| §6.7: diam $R(P_n^2)$, $n=4..18$ | `t_sec6_quick.py` | 3,3,5,6,7,8,10,11,12,14,15,16,18,19,21 ✓; path counts 6,…,2448 ✓ |
| §6.6: $C_n$ forcing | `forcing.py` (own backward BFS over all orderings) | forcing for $n=3..9$; $n=10$: 1,814,380/1,814,400 reached, so **20** unreachable ✓, and the first one is the §6.3 ordering. $n=11$ (264) not re-run |
| §6.6: $J(1,2,3,3)$ | `forcing.py` | $R(J)$: 1800 paths, connected; (ii): 181,440/181,440 ✓ |
| §6.6: $J(1,2,4,4)$, $J(1,3,4,4)$ | `t_rj.py` | $R(J)$ connected (39,168 and 877,824 paths ✓). (ii) at $n=11,12$ is too large for Python BFS, so it was not re-run exhaustively |
| §6.6: skeletons | `t_skeletons.py`, `forcing.py` | ladder, prism, $d_{13}$, $c_{13}$ at $n=8,9,10$: forcing ✓ (path counts match the data); 3×3 grid forcing ✓; $P_n^2$, $n=6..10$: forcing ✓; **3×4 grid NOT forcing** (issue 1). $n=11,12$ not re-run |
| Lemma 2, literal proof | `t_lemma2.py` | 11 instances ($n=9$ to $80$, $k=4$ to $10$): 400 random orderings each, and every Advancing/Closing/Descending assertion holds ($\beta$ drops by exactly 1 per round; rounds $=\beta_0$). 800 cycle pairs each are made equal by Euler reversals, explicit Fact 3 backbites and twin swaps. 0 failures |
| Lemma 4, bookkeeping | `t_lemma4.py A` | 17,656 attachment moves and 15,765 lift/crossing backbites: exact path orders as claimed ✓ |
| Lemma 4, component claims (attachments in one component, $D_{xy}$, lifts in one component, (a), (b)) on random small graphs, **without** the degree hypothesis | `t_lemma4.py Bweak/Bsparse` | 662 + 2371 graphs ($h=5..9$), 161 with disconnected $R(G)$. About 14.3 M claim instances, 0 failures |
| Lemma 4, full statement ($h=6..8$) and Remark 3 hypotheses ($h=6..8$) | `t_lemma4.py Blemma4/Bremark3` | $R(G)$ connected in 40/40 and 80/80 random cases; all component claims hold (about 41 M further instances). This is a weak test, because at $h\le8$ the hypotheses force near-complete graphs |
| Fact 2 count and both backbites | `t_numeric.py` | 1,253 random paths ✓ |
| §4/§5 inequalities, Hoeffding, constants | `t_numeric.py` | 0 failures (exact rationals); Hoeffding never violated; $n_0$ doubly exponential |
| §6.1, $n\le9$, all $\delta\ge\lceil n/2\rceil$, direct | `t_sec6_heavy.py conj` | $n=4..9$: 3 + 3 + 19 + 29 + 424 + 1165 graphs, all connected ✓ |
| §6.1, $n=10$, $\delta\ge5$ | `t_sec6_heavy.py conj` | 108,376 graphs; 107,296 contain $P_{10}^2$; **1,080** checked directly, all connected; max 93,312 paths ✓ |
| §6.1, $n=11$, $\delta\ge6$ | `t_conj11.py`, `t_conj11b.py` | 868,311 graphs; 868,030 contain $P_{11}^2$; **281** checked directly — RESULT_N11 |
| §6.2, Ore, $n=5..9$ | `t_sec6_heavy.py ore` | 5, 21, 68, 503, 4942 graphs, all connected ✓ |
| §6.2, $n=9$, $\delta\ge3$ | `t_sec6_heavy.py conj` | 84,245 graphs; 33,502 contain $P_9^2$; 29 have no Hamiltonian path; 50,714 checked, all connected ✓ |
| §6.2, $n=10$, $\delta\ge4$ | `t_sec6_heavy.py conj_sample` | random sample of 3,000 graphs without $P_{10}^2$: all connected (only a sample; not the full 288,268) |
| §6.4, fixed endpoint $R_b$ | `t_sec6_heavy.py rb`, `t_rb_sample.py` | $n=4,5,6$ ($\delta\ge n/2$): no failures. $n=7,\delta\ge3$: 9 failures, all $\delta=3$ ✓. $n=8,\delta\ge3$: 136, all $\delta=3$. $n=9,\delta\ge4$: 12, all $\delta=4$ ✓. $n=10,\delta\ge5$: the 906 sparsest graphs (25–26 edges) plus 300 random graphs, no failures (only a sample) |
| §6.5, closure | `t_sec6_heavy.py closure`, `t_closure9.py` | $n=6$: 170/45 pairs, 0 violations. $n=7$, thr $n$: 1,728 pairs, **2** backward ✓; thr $n+1$: 684 pairs, 0 ✓. $n=8$, thr $n+1$: 12,807 pairs, **0** backward ✓; thr $n$: 32,400 pairs, 16 backward. $n=9$: all 8 listed instances confirmed ($d(u)+d(v)=10$, $R(G)$ has 2 components, $R(G+uv)$ connected; all have $\delta=1$) |
| Graph counts | `geng -u` | 108,376; 868,311; 1,249,973; 84,245; 150; 2,590; 15,471; 7,442 ✓ |

**Not independently reproduced** (too large for Python):
- $C_{11}$ (264 unreachable orderings);
- (ii) for $J(1,2,4,4)$ and $J(1,3,4,4)$;
- the skeletons at $n=11,12$, except that the 3×4 grid was refuted;
- the full $n=10,\delta\ge4$ class and the full $n=10$ fixed-endpoint class (sampled only).
