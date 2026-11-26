# Kazazi backbite note: Lean statements vs. paper claims

Paper: [`../paper/asymptotic_threshold.md`](../paper/asymptotic_threshold.md) (v1.1). Lean 4.37.0-rc1,
Mathlib v4.37.0-rc1. Everything lives in namespace `Kazazi`, in
`KazaziLean/*.lean`. There is no `sorry`, `admit`, `axiom` or `native_decide`.

Every theorem listed below depends only on `[propext, Classical.choice, Quot.sound]`
(see `Axioms.lean`).

Out of scope, not formalized: Theorem 1, Lemma 2, Lemma 4, §4–§5, and the §6 computations
other than item 3.

---

## 1. Definitions (§1), `Defs.lean`

Vertex type: any `V` with `[Fintype V] [DecidableEq V]`. This includes `Fin n`, which is
what the example uses. A graph is a `SimpleGraph V`. Decidable adjacency is required only
where degrees or `decide` are used.

**Paper.** "For a Hamiltonian path $P=w_1\cdots w_n$ and $3\le k\le n$ with
$w_1w_k\in E(G)$, write $\mathrm{bb}(w_1,w_k)$ for the backbite at the endpoint $w_1$ with
target $w_k$. By definition $\mathrm{bb}(w_1,w_k)$ produces $w_{k-1}\cdots w_1w_k\cdots w_n$.
Backbites at the other end are symmetric."

```lean
def IsHamPath (G : SimpleGraph V) (l : List V) : Prop :=
  l.Nodup ∧ l.length = Fintype.card V ∧ l.IsChain G.Adj
def IsOrdering (l : List V) : Prop := l.Nodup ∧ l.length = Fintype.card V
def bbFront (l : List V) (j : ℕ) : List V := (l.take j).reverse ++ l.drop j
def bbBack (l : List V) (j : ℕ) : List V := l.take (j + 1) ++ (l.drop (j + 1)).reverse
def BBFront (G : SimpleGraph V) (l l' : List V) : Prop :=
  ∃ j, ∃ hj : j < l.length, 2 ≤ j ∧ G.Adj (l[0]'(by omega)) l[j] ∧ l' = bbFront l j
def BBBack (G : SimpleGraph V) (l l' : List V) : Prop :=
  ∃ j, ∃ hj : j + 2 < l.length, G.Adj (l[l.length - 1]'(by omega)) (l[j]'(by omega)) ∧
    l' = bbBack l j
def BBStep (G : SimpleGraph V) (l l' : List V) : Prop := BBFront G l l' ∨ BBBack G l l'
```

Indices are 0-based, so `j = k - 1`. The paper's `k ≥ 3` becomes `2 ≤ j`. The symmetric
condition `k ≤ n - 2` at the other end becomes `j + 3 ≤ n`, i.e. `j + 2 < l.length`.
`bbBack_iff_front_reverse : BBBack G l l' ↔ BBFront G l.reverse l'.reverse` shows that the
back move is exactly the mirror image of the front move.

**Paper.** "Let $R(G)$ be the graph on the Hamiltonian paths of $G$ (a path and its reversal
being identified) in which two paths are adjacent when a single backbite carries one to the
other."

```lean
def HamPath (G : SimpleGraph V) : Type _ := {l : List V // IsHamPath G l}
instance revSetoid (G) : Setoid (HamPath G)   -- r p q := q.1 = p.1 ∨ q.1 = p.1.reverse
abbrev RVert (G : SimpleGraph V) : Type _ := Quotient (revSetoid G)
def StepRep (G) (p q : List V) : Prop :=
  ∃ p' ∈ [p, p.reverse], ∃ q' ∈ [q, q.reverse], BBStep G p' q'
def RRel (G) : RVert G → RVert G → Prop := Quotient.lift₂ (fun p q => StepRep G p.1 q.1) _
def RGraph (G : SimpleGraph V) : SimpleGraph (RVert G) := SimpleGraph.fromRel (RRel G)
def RConnected (G : SimpleGraph V) : Prop := (RGraph G).Preconnected
```

Differences:
* `fromRel` symmetrizes and removes loops. Symmetrizing changes nothing, because backbites
  are invertible (`bbFront_symm`, `bbStep_symm`, below). Loops play no role in connectivity.
* `RConnected` is `Preconnected`. A graph with no Hamiltonian path therefore counts as
  "connected"; the paper does not discuss that case. In the example, `¬ RConnected` is the
  stronger direction, so it is not affected. Lemma 1 and Lemma 3 conclude `RConnected`, and
  their hypotheses force Hamiltonian paths to exist.

Elementary facts from §1 (`Lemmas.lean`):

| Paper | Lean |
|---|---|
| "A backbite is invertible: $\mathrm{bb}(w_{k-1},w_k)$ undoes $\mathrm{bb}(w_1,w_k)$." | `bbFront_invol (l) (hj : j ≤ l.length) : bbFront (bbFront l j) j = l`; `bbFront_symm (hc : l.IsChain G.Adj) (h : BBFront G l l') : BBFront G l' l`; `bbStep_symm` |
| the result is again a Hamiltonian path | `isHamPath_of_step (hl : IsHamPath G l) (h : BBStep G l l') : IsHamPath G l'` |
| "never moves the other endpoint" | `bbFront_getElem_last` (`FactA.lean`): the last vertex is unchanged |
| **Cycles**: "all $n$ paths $C-e$ … lie in one component" | `reachable_rotate`, below |

```lean
def IsCyclic (G : SimpleGraph V) (c : List V) : Prop := ∀ z ∈ c.getLast?, ∀ y ∈ c.head?, G.Adj z y
theorem reachable_rotate {x y : List V} (hl : IsHamPath G (x ++ y)) (hlen : 3 ≤ (x ++ y).length)
    (hcyc : IsCyclic G (x ++ y)) :
    ∃ h' : IsHamPath G (y ++ x), (RGraph G).Reachable (cls (x ++ y) hl) (cls _ h') ∧
      IsCyclic G (y ++ x)
```

A Hamiltonian cycle is represented by a cyclic Hamiltonian path `c`, the deletion of the
closing edge. Its edge-deletions are its rotations `y ++ x`, read in either direction, and
the reversal is identified in `RVert`. So `reachable_rotate` is the claim that all $n$
edge-deletions lie in one component.

The fact "a backbite deletes exactly one edge and adds exactly one edge" is not stated
separately.

---

## 2. §6 item 3, "Hamiltonicity is not sufficient" (`Example.lean`)

**Paper.** "Take $C_{10}$ on $0,\dots,9$ together with the edges of the path
$0,1,7,8,9,4,3,2,6,5$. This graph is Hamiltonian with $\delta=2$, and $R(G)$ has two
components, with 18 and 4 paths."

```lean
def extraPath : List (Fin 10) := [0, 1, 7, 8, 9, 4, 3, 2, 6, 5]
def pathRel (l : List (Fin 10)) (a b : Fin 10) : Prop := (a, b) ∈ l.zip l.tail
def exG : SimpleGraph (Fin 10) := cycleGraph 10 ⊔ fromRel (pathRel extraPath)

theorem exG_adj_iff (a b : Fin 10) : exG.Adj a b ↔
    (a, b) ∈ [(0,1),(0,9),(1,2),(1,7),(2,3),(2,6),(3,4),(4,5),(4,9),(5,6),(6,7),(7,8),(8,9)] ∨
    (b, a) ∈ [(0,1),(0,9),(1,2),(1,7),(2,3),(2,6),(3,4),(4,5),(4,9),(5,6),(6,7),(7,8),(8,9)]
theorem exG_isHamiltonian : exG.IsHamiltonian            -- Mathlib's `SimpleGraph.IsHamiltonian`
theorem exG_not_RConnected : ¬ RConnected exG
theorem hamiltonian_not_sufficient :
    ∃ G : SimpleGraph (Fin 10), ∃ _ : DecidableRel G.Adj, G.IsHamiltonian ∧ ¬ RConnected G
```

`cycleGraph 10` is Mathlib's `C₁₀` (`a ~ b ↔ a - b = 1 ∨ b - a = 1` in `Fin 10`).

How the proof works:
* `compS` is an explicit list of 36 orderings: the 18 paths of the larger component and their
  reversals. They were found with a small Python enumeration, which matched the paper's
  18/4 split.
* `compS_ham` checks by `decide` that the 36 lists are distinct Hamiltonian paths of `exG`.
* `compS_rev`, `compS_front` and `compS_back` check that `compS` is closed under reversal and
  under every front and back backbite.
* By invertibility (`bbStep_symm`), membership in `compS` is invariant along walks of
  `RGraph exG` (`inS_of_reachable`).
* `[0,…,9] ∈ compS`, while the Hamiltonian path `extraPath` is not in `compS`.

All checks use `decide +kernel`, a kernel-checked `decide`; there is no `native_decide`.

Difference: the proof shows that `R(G)` is disconnected and that one union of components
holds exactly the 18 classes in `compS`. It does **not** prove that there are exactly two
components or that the other component has 4 paths. That would need a verified enumeration
of all 22 classes.

---

## 3. Forcing graphs, Lemma 1, Fact B (`Forcing.lean`)

**Paper.** "A graph $J$ is forcing if: (i) $R(J)$ is connected; and (ii) from every ordering
(permutation) of $V(J)$, regarded as a Hamiltonian path of the complete graph on $V(J)$, some
sequence of backbites, each adding an edge of $J$, reaches a Hamiltonian path of $J$."

```lean
def IsForcing (J : SimpleGraph V) : Prop :=
  RConnected J ∧
    ∀ l : List V, IsOrdering l → ∃ l', Relation.ReflTransGen (BBStep J) l l' ∧ IsHamPath J l'
```

On an arbitrary ordering, `BBStep J` is exactly a backbite in the complete graph (front:
`2 ≤ j`; back: `j + 3 ≤ n`) whose added edge `w₁w_k` (resp. `w_n w_k`) lies in `J`.

**Paper, Lemma 1.** "If $G$ contains a forcing graph $J$ as a spanning subgraph, then $R(G)$
is connected."

```lean
theorem lemma1 {J : SimpleGraph V} (hJG : J ≤ G) (hJ : IsForcing J) : RConnected G
```

"Spanning subgraph" is `J ≤ G` on the same vertex type.

**Paper, Fact B.** "Let a Hamiltonian cycle contain the segment $a,u_1,\dots,u_t,b$ with
$t\ge 2$ and $a\ne b$, and suppose $au_t,\,u_1b\in E(G)$. Then the cycle obtained by reversing
$u_1\cdots u_t$ is equivalent to the original."

```lean
theorem factB {a b u1 ut : V} {mid rest : List V}
    (hc : IsHamPath G (a :: ((u1 :: (mid ++ [ut])) ++ b :: rest)))
    (hcyc : IsCyclic G (a :: ((u1 :: (mid ++ [ut])) ++ b :: rest)))
    (h1 : G.Adj a ut) (h2 : G.Adj u1 b) :
    ∃ h' : IsHamPath G (a :: ((u1 :: (mid ++ [ut])).reverse ++ b :: rest)),
      (RGraph G).Reachable (cls _ hc) (cls _ h') ∧
      IsCyclic G (a :: ((u1 :: (mid ++ [ut])).reverse ++ b :: rest))
```

Differences:
* The cycle is written as a cyclic Hamiltonian path that starts at `a`. Every cycle and
  segment can be put in this form by rotating, which stays inside one component by
  `reachable_rotate`.
* `U = u1 :: (mid ++ [ut])`, so `t = |mid| + 2 ≥ 2`. `a ≠ b` follows from `Nodup`.
* "Equivalent" (edge-deletions in the same component of `R(G)`) is proved for the particular
  edge-deletions `cls c` and `cls c'`. All other edge-deletions follow by `reachable_rotate`.
* The degenerate case `rest = []` (so `b` is adjacent to `a` on the cycle) is allowed.

---

## 4. Fact A (crossings), `FactA.lean`

**Paper.** "Let $P=w_1\cdots w_h$ be a Hamiltonian path of a graph $F$ on $h$ vertices whose
endpoints $a=w_1$ and $b=w_h$ are non-adjacent. Then there are at least
$d_F(a)+d_F(b)-(h-1)$ indices $i$ with $aw_{i+1},\,bw_i\in E(F)$. For each such index,
$2\le i\le h-2$. The backbite $\mathrm{bb}(a,w_{i+1})$ deletes $w_iw_{i+1}$ and yields a path
with adjacent endpoints $w_i,b$."

```lean
def crossings (F : SimpleGraph V) [DecidableRel F.Adj] (l : List V) (a b : V) : Finset ℕ :=
  (range (l.length - 1)).filter (fun i => ∃ h : i + 1 < l.length, F.Adj a l[i + 1] ∧ F.Adj b l[i])

theorem factA (F : SimpleGraph V) [DecidableRel F.Adj] {l : List V} (hl : IsHamPath F l)
    (h0 : 0 < l.length) (hab : ¬ F.Adj (l[0]'h0) (l[l.length - 1]'(by omega))) :
    F.degree (l[0]'h0) + F.degree (l[l.length - 1]'(by omega)) ≤
      (crossings F l (l[0]'h0) (l[l.length - 1]'(by omega))).card + (Fintype.card V - 1)

theorem crossings_bounds (F : SimpleGraph V) [DecidableRel F.Adj] {l : List V} (hl : l.Nodup)
    (h0 : 0 < l.length) (hab : ¬ F.Adj (l[0]'h0) (l[l.length - 1]'(by omega))) {i : ℕ}
    (hi : i ∈ crossings F l (l[0]'h0) (l[l.length - 1]'(by omega))) :
    1 ≤ i ∧ i + 3 ≤ l.length

theorem crossing_front (F : SimpleGraph V) [DecidableRel F.Adj] {l : List V} (hl : IsHamPath F l)
    (h0 : 0 < l.length) (hab : ¬ F.Adj (l[0]'h0) (l[l.length - 1]'(by omega))) {i : ℕ}
    (hi : i ∈ crossings F l (l[0]'h0) (l[l.length - 1]'(by omega))) :
    BBFront F l (bbFront l (i + 1)) ∧ IsHamPath F (bbFront l (i + 1)) ∧
      IsCyclic F (bbFront l (i + 1))
```

Differences:
* Indices are 0-based. The paper's `i ∈ {1,…,h-1}` is Lean `i + 1` with `i ∈ range (h-1)`,
  and "$2\le i\le h-2$" becomes `1 ≤ i ∧ i + 3 ≤ h`.
* The bound is stated without truncated subtraction.
* `F` lives on all of `V`, so `h = Fintype.card V`.
* In `factA` the non-adjacency hypothesis `hab` is not needed: the inequality holds for
  every Hamiltonian path. The hypothesis is kept to match the paper.
* The symmetric statement for `bb(b, w_i)` is not stated separately. It is used inline in
  the proof of Lemma 3 (`reach_lift`, step 3).

A general counting lemma, also used for "eligible edges" in Lemma 3:

```lean
theorem eligible_card (P : List V) (N : Finset V) (hN : ∀ x ∈ N, x ∈ P) :
    2 * N.card ≤ (eligible P N).card + P.length + 1
```

Here `eligible P N` is the set of `i` with `P[i], P[i+1] ∈ N`. This is the paper's bound
"$P$ has at least $d-(h-d+1)=2d-h-1$ eligible edges".

---

## 5. Lemma 3 (vertex extension), fully proved (`Lemma3*.lean`)

**Paper.** "Let $H$ be a graph on $h$ vertices with $\delta(H)\ge h/2+2$ and $R(H)$
connected. Let $G$ be obtained by adding a vertex $v$ with
$d:=|N(v)\cap V(H)|\ge h/2+2$. Then $R(G)$ is connected."

```lean
theorem lemma3 (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hH : RConnected (G.induce ({v}ᶜ : Set V)))
    (hδ : ∀ x : ↥({v}ᶜ : Set V),
      Fintype.card ↥({v}ᶜ : Set V) + 4 ≤ 2 * (G.induce ({v}ᶜ : Set V)).degree x)
    (hd : Fintype.card ↥({v}ᶜ : Set V) + 4 ≤
      2 * ((G.neighborFinset v).filter (· ∈ ({v}ᶜ : Set V))).card) :
    RConnected G
```

Differences:
* "$G$ obtained by adding a vertex $v$ to $H$" is formalized the other way round. `G` is
  any graph with a distinguished vertex `v`, and `H := G.induce {v}ᶜ`. This is equivalent
  up to isomorphism.
* `h = |{v}ᶜ|`. The conditions $\delta(H)\ge h/2+2$ and $d\ge h/2+2$ are written exactly as
  `h + 4 ≤ 2·deg`. `N(v) ∩ V(H)` is the filter of `G.neighborFinset v`; it equals `N(v)`.

The proof follows the paper. The main named steps:

| Paper step | Lean |
|---|---|
| Attachment moves (same point/other direction; move to `c ≠ a`; case `c = b`) | `attach_flip`, `attach_move`, `attach_move_last` (`Lemma3Parts.lean`) |
| "All attachments to $D$ lie in one component" | `attachments_connected` |
| Lifts, eligible edges, "at least $2d-h-1 \ge 3$ eligible edges" | `liftAt`, `Elig`, `IsHamH` (`Lemma3Lift.lean`); `three_le_eligible` |
| (a) lifts of one $P$ in one component: cyclic case / Fact A case | `lifts_cyclic`, `lifts_same` (`Lemma3Conn.lean`) |
| (b) lifts of $R(H)$-adjacent paths joined (backbite commutes with lifting) | `commute_front`, `commute_back`, `commute_step`, `liftsConn_of_step` |
| "Since $R(H)$ is connected, (a) and (b) put all lifts in one component $\mathcal K$" | `liftsConn_of_reachable` (`Lemma3.lean`) |
| "Every path reaches $\mathcal K$", steps 1–5 | `reach_cyclic`, `reach_start_v`, `reach_lift_of_attach`, `reach_lift` (`Lemma3Reach.lean`) |

There is one small deviation inside the proof. For Fact A inside `H`
(`three_le_crossings_H`), Lean uses a general counting bound that gives at least **3**
crossing indices, not the paper's 5. Three is enough: the proof needs one crossing whose
deleted edge differs from two given eligible edges.

---

## Commands and times

Run from this `lean/` folder:

```
lake build                                  # ~17 s wall after Mathlib
lake env lean KazaziLean/Axioms.lean        # prints the axioms of every main theorem
lake env lean KazaziLean/<File>.lean        # 1.1–2.7 s per file
```

Per-module build times from `lake build`:

| Module | Time |
|---|---|
| Defs | 1.3 s |
| Lemmas | 1.2 s |
| Forcing | 1.4 s |
| FactA | 1.6 s |
| Example | 2.7 s |
| Lemma3Parts | 1.4 s |
| Lemma3Lift | 1.6 s |
| Lemma3Conn | 1.4 s |
| Lemma3Reach | 1.5 s |
| Lemma3 | 1.3 s |
| Axioms | 1.1 s |
