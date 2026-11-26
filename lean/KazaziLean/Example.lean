import KazaziLean.Lemmas

/-!
# Hamiltonicity is not sufficient (§6 item 3)

`G = C₁₀ ∪ (edges of the path 0,1,7,8,9,4,3,2,6,5)` on `Fin 10` is Hamiltonian, but `R(G)`
is disconnected.

Proof: `compS` is an explicit list of 36 vertex orderings (18 Hamiltonian paths together with
their reversals; the 18-path component). We check by `decide` that `compS` is closed under
reversal and under every backbite (front and back). By invertibility of backbites the set
of classes in `compS` is a union of components of `R(G)`. The Hamiltonian path
`0,1,7,8,9,4,3,2,6,5` is not in `compS`, while `0,1,…,9` is.
-/

namespace Kazazi.Example

open List SimpleGraph

/-- The ordering `0,1,7,8,9,4,3,2,6,5` whose edges are added to `C₁₀`. -/
def extraPath : List (Fin 10) := [0, 1, 7, 8, 9, 4, 3, 2, 6, 5]

/-- Edges of a path given as a list: `a ~ b` iff `(a, b)` is a pair of consecutive entries. -/
def pathRel (l : List (Fin 10)) (a b : Fin 10) : Prop := (a, b) ∈ l.zip l.tail

instance (l : List (Fin 10)) : DecidableRel (pathRel l) := fun a b => by
  unfold pathRel; infer_instance

/-- Boolean check of `IsChain`, by structural recursion (kernel-friendly). -/
def chainB (r : Fin 10 → Fin 10 → Prop) [DecidableRel r] : List (Fin 10) → Bool
  | a :: b :: l => decide (r a b) && chainB r (b :: l)
  | _ => true

theorem isChain_of_chainB (r : Fin 10 → Fin 10 → Prop) [DecidableRel r] :
    ∀ l, chainB r l = true → l.IsChain r
  | [], _ => .nil
  | [a], _ => .singleton a
  | a :: b :: l, h => by
    simp only [chainB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cons_cons h.1 (isChain_of_chainB r _ h.2)

/-- The graph of §6 item 3: the cycle `C₁₀` on `0,…,9` plus the edges of the path
`0,1,7,8,9,4,3,2,6,5`. -/
def exG : SimpleGraph (Fin 10) := cycleGraph 10 ⊔ fromRel (pathRel extraPath)

instance : DecidableRel exG.Adj := fun a b => by
  unfold exG; rw [sup_adj, fromRel_adj]; infer_instance

/-- Sanity check: the explicit edge list (13 edges, min degree 2). -/
theorem exG_adj_iff (a b : Fin 10) : exG.Adj a b ↔
    (a, b) ∈ [(0,1),(0,9),(1,2),(1,7),(2,3),(2,6),(3,4),(4,5),(4,9),(5,6),(6,7),(7,8),(8,9)] ∨
    (b, a) ∈ [(0,1),(0,9),(1,2),(1,7),(2,3),(2,6),(3,4),(4,5),(4,9),(5,6),(6,7),(7,8),(8,9)] := by
  revert a b; decide +kernel

/-- `G` is Hamiltonian (Mathlib's notion): it contains `C₁₀`. -/
theorem exG_isHamiltonian : exG.IsHamiltonian :=
  (isHamiltonian_cycleGraph (by norm_num)).mono le_sup_left

/-- The 18-path component, each path listed in both orientations. -/
def compS : List (List (Fin 10)) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
  [0, 1, 2, 3, 4, 9, 8, 7, 6, 5],
  [0, 9, 8, 7, 1, 2, 3, 4, 5, 6],
  [0, 9, 8, 7, 1, 2, 6, 5, 4, 3],
  [0, 9, 8, 7, 6, 5, 4, 3, 2, 1],
  [1, 0, 9, 8, 7, 6, 2, 3, 4, 5],
  [1, 0, 9, 8, 7, 6, 5, 4, 3, 2],
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 0],
  [2, 1, 0, 9, 8, 7, 6, 5, 4, 3],
  [2, 3, 4, 5, 6, 7, 1, 0, 9, 8],
  [2, 3, 4, 5, 6, 7, 8, 9, 0, 1],
  [3, 2, 1, 0, 9, 4, 5, 6, 7, 8],
  [3, 2, 1, 0, 9, 8, 7, 6, 5, 4],
  [3, 4, 5, 6, 2, 1, 0, 9, 8, 7],
  [3, 4, 5, 6, 2, 1, 7, 8, 9, 0],
  [3, 4, 5, 6, 7, 8, 9, 0, 1, 2],
  [4, 3, 2, 1, 0, 9, 8, 7, 6, 5],
  [4, 5, 6, 7, 8, 9, 0, 1, 2, 3],
  [5, 4, 3, 2, 1, 0, 9, 8, 7, 6],
  [5, 4, 3, 2, 6, 7, 1, 0, 9, 8],
  [5, 4, 3, 2, 6, 7, 8, 9, 0, 1],
  [5, 6, 7, 8, 9, 0, 1, 2, 3, 4],
  [5, 6, 7, 8, 9, 4, 3, 2, 1, 0],
  [6, 5, 4, 3, 2, 1, 0, 9, 8, 7],
  [6, 5, 4, 3, 2, 1, 7, 8, 9, 0],
  [6, 7, 8, 9, 0, 1, 2, 3, 4, 5],
  [7, 6, 5, 4, 3, 2, 1, 0, 9, 8],
  [7, 8, 9, 0, 1, 2, 3, 4, 5, 6],
  [7, 8, 9, 0, 1, 2, 6, 5, 4, 3],
  [8, 7, 6, 5, 4, 3, 2, 1, 0, 9],
  [8, 7, 6, 5, 4, 9, 0, 1, 2, 3],
  [8, 9, 0, 1, 2, 3, 4, 5, 6, 7],
  [8, 9, 0, 1, 7, 6, 2, 3, 4, 5],
  [8, 9, 0, 1, 7, 6, 5, 4, 3, 2],
  [9, 0, 1, 2, 3, 4, 5, 6, 7, 8],
  [9, 8, 7, 6, 5, 4, 3, 2, 1, 0]]

theorem compS_length : compS.length = 36 := by decide +kernel

/-- All 36 lists are distinct Hamiltonian paths of `G` (so `compS` lists 18 classes). -/
theorem compS_ham : compS.Nodup ∧ ∀ l ∈ compS, l.Nodup ∧ l.length = 10 ∧ chainB exG.Adj l = true := by
  decide +kernel

theorem compS_rev : ∀ l ∈ compS, l.reverse ∈ compS := by decide +kernel

theorem compS_front : ∀ l ∈ compS, ∀ j, ∀ hj : j < l.length, 2 ≤ j →
    exG.Adj (l[0]'(by omega)) l[j] → bbFront l j ∈ compS := by decide +kernel

theorem compS_back : ∀ l ∈ compS, ∀ j, ∀ hj : j < l.length - 2,
    exG.Adj (l[l.length - 1]'(by omega)) (l[j]'(by omega)) → bbBack l j ∈ compS := by
  decide +kernel

theorem compS_step {l l' : List (Fin 10)} (hl : l ∈ compS) (h : BBStep exG l l') :
    l' ∈ compS := by
  rcases h with ⟨j, hj, h2, hadj, rfl⟩ | ⟨j, hj, hadj, rfl⟩
  · exact compS_front l hl j hj h2 hadj
  · exact compS_back l hl j (by omega) hadj

/-- Membership of a class of `R(G)` in the 18-path component. -/
def inS : RVert exG → Prop :=
  Quotient.lift (fun p : HamPath exG => p.1 ∈ compS) (by
    rintro p q (h | h)
    · simp [h]
    · simp only [h, eq_iff_iff]
      exact ⟨compS_rev _, fun h' => by simpa using compS_rev _ h'⟩)

theorem mem_or_rev {l : List (Fin 10)} (h : l ∈ compS) {m : List (Fin 10)}
    (hm : m ∈ [l, l.reverse]) : m ∈ compS := by
  simp at hm; rcases hm with rfl | rfl
  · exact h
  · exact compS_rev _ h

theorem of_mem_or_rev {l m : List (Fin 10)} (hm : m ∈ [l, l.reverse]) (h : m ∈ compS) :
    l ∈ compS := by
  simp at hm; rcases hm with rfl | rfl
  · exact h
  · simpa using compS_rev _ h

theorem inS_of_adj {P Q : RVert exG} (h : (RGraph exG).Adj P Q) (hP : inS P) : inS Q := by
  induction P using Quotient.ind
  induction Q using Quotient.ind
  rename_i p q
  rw [RGraph, fromRel_adj] at h
  obtain ⟨_, h | h⟩ := h
  · obtain ⟨p', hp', q', hq', hs⟩ := h
    exact of_mem_or_rev hq' (compS_step (mem_or_rev hP hp') hs)
  · obtain ⟨q', hq', p', hp', hs⟩ := h
    have hc : q'.IsChain exG.Adj := by
      simp at hq'; rcases hq' with rfl | rfl
      · exact q.2.2.2
      · exact (isHamPath_reverse q.2).2.2
    exact of_mem_or_rev hq' (compS_step (mem_or_rev hP hp') (bbStep_symm hc hs))

theorem inS_of_reachable {P Q : RVert exG} (h : (RGraph exG).Reachable P Q) (hP : inS P) :
    inS Q := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hP
  | cons ha _ ih => exact ih (inS_of_adj ha hP)

theorem ham_id : IsHamPath exG [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  refine ⟨by decide +kernel, by simp, isChain_of_chainB _ _ (by decide +kernel)⟩

theorem ham_extra : IsHamPath exG extraPath := by
  refine ⟨by decide +kernel, by simp [extraPath], isChain_of_chainB _ _ (by decide +kernel)⟩

/-- **§6 item 3.** `R(G)` is disconnected. -/
theorem exG_not_RConnected : ¬ RConnected exG := by
  intro h
  have h1 : inS (cls _ ham_id) := show [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] ∈ compS by decide +kernel
  have h2 : inS (cls _ ham_extra) := inS_of_reachable (h _ _) h1
  change extraPath ∈ compS at h2
  revert h2
  decide +kernel

/-- **§6 item 3.** Hamiltonicity does not imply connectivity of `R(G)`. -/
theorem hamiltonian_not_sufficient :
    ∃ G : SimpleGraph (Fin 10), ∃ _ : DecidableRel G.Adj, G.IsHamiltonian ∧ ¬ RConnected G :=
  ⟨exG, inferInstance, exG_isHamiltonian, exG_not_RConnected⟩

end Kazazi.Example

