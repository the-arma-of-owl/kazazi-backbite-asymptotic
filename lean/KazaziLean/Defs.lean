import Mathlib

/-!
# Backbite moves and the reconfiguration graph `R(G)`

Definitions following §1 of `asymptotic_threshold.md` (an asymptotic version of
Kazazi's backbite conjecture).

* A Hamiltonian path of `G` is a list `w₁ … wₙ` containing every vertex exactly once
  (`Nodup` and length `= |V|`) with consecutive entries adjacent.
* `bbFront l j` is the backbite at the endpoint `w₁ = l[0]` with target `w_k = l[j]`
  (`j = k - 1`, so `k ≥ 3` is `2 ≤ j`): result `w_{k-1} … w₁ w_k … w_n`.
* `bbBack l j` is the symmetric backbite at the endpoint `w_n` with target `w_k = l[j]`,
  `k ≤ n - 2`: result `w₁ … w_k w_n … w_{k+1}`.
* `RGraph G` is a `SimpleGraph` on Hamiltonian paths modulo reversal.
-/

set_option linter.unusedSectionVars false

namespace Kazazi

open List

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A Hamiltonian path of `G`, as a list of vertices. -/
def IsHamPath (G : SimpleGraph V) (l : List V) : Prop :=
  l.Nodup ∧ l.length = Fintype.card V ∧ l.IsChain G.Adj

/-- An *ordering* of `V`: a list containing every vertex exactly once
(a Hamiltonian path of the complete graph). -/
def IsOrdering (l : List V) : Prop :=
  l.Nodup ∧ l.length = Fintype.card V

/-- Result of the backbite at the first endpoint `l[0]` with target `l[j]`. -/
def bbFront (l : List V) (j : ℕ) : List V := (l.take j).reverse ++ l.drop j

/-- Result of the backbite at the last endpoint with target `l[j]`. -/
def bbBack (l : List V) (j : ℕ) : List V := l.take (j + 1) ++ (l.drop (j + 1)).reverse

/-- `l'` arises from `l` by a backbite at the first endpoint `w₁` with target `w_k`, `k ≥ 3`
(0-based index `j = k-1 ≥ 2`), and `w₁ w_k ∈ E(G)`. -/
def BBFront (G : SimpleGraph V) (l l' : List V) : Prop :=
  ∃ j, ∃ hj : j < l.length, 2 ≤ j ∧ G.Adj (l[0]'(by omega)) l[j] ∧ l' = bbFront l j

/-- `l'` arises from `l` by a backbite at the last endpoint `w_n` with target `w_k`,
`k ≤ n-2` (0-based index `j = k-1`, `j + 3 ≤ n`), and `w_n w_k ∈ E(G)`. -/
def BBBack (G : SimpleGraph V) (l l' : List V) : Prop :=
  ∃ j, ∃ hj : j + 2 < l.length, G.Adj (l[l.length - 1]'(by omega)) (l[j]'(by omega)) ∧
    l' = bbBack l j

/-- One backbite, at either end. -/
def BBStep (G : SimpleGraph V) (l l' : List V) : Prop := BBFront G l l' ∨ BBBack G l l'

/-- Hamiltonian paths of `G`. -/
def HamPath (G : SimpleGraph V) : Type _ := {l : List V // IsHamPath G l}

theorem isHamPath_reverse {G : SimpleGraph V} {l : List V} (h : IsHamPath G l) :
    IsHamPath G l.reverse := by
  refine ⟨nodup_reverse.2 h.1, by simp [h.2.1], ?_⟩
  rw [isChain_reverse]
  exact h.2.2.imp (fun _ _ h => G.adj_symm h)

/-- A path is identified with its reversal. -/
instance revSetoid (G : SimpleGraph V) : Setoid (HamPath G) where
  r p q := q.1 = p.1 ∨ q.1 = p.1.reverse
  iseqv := by
    refine ⟨fun p => Or.inl rfl, ?_, ?_⟩
    · rintro p q (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, reverse_reverse])
    · rintro p q r (h | h) (h' | h')
      · exact Or.inl (h'.trans h)
      · exact Or.inr (by rw [h', h])
      · exact Or.inr (by rw [h', h])
      · exact Or.inl (by rw [h', h, reverse_reverse])

/-- Vertices of `R(G)`: Hamiltonian paths of `G`, a path and its reversal identified. -/
abbrev RVert (G : SimpleGraph V) : Type _ := Quotient (revSetoid G)

/-- `P ⟶ Q` if a single backbite carries some orientation of `P` to some orientation of `Q`. -/
def StepRep (G : SimpleGraph V) (p q : List V) : Prop :=
  ∃ p' ∈ [p, p.reverse], ∃ q' ∈ [q, q.reverse], BBStep G p' q'

theorem stepRep_rev_left {G : SimpleGraph V} {p q : List V} :
    StepRep G p.reverse q ↔ StepRep G p q := by
  simp [StepRep, or_comm]

theorem stepRep_rev_right {G : SimpleGraph V} {p q : List V} :
    StepRep G p q.reverse ↔ StepRep G p q := by
  simp [StepRep, or_comm]

/-- The relation "one backbite apart" on `RVert G`. -/
def RRel (G : SimpleGraph V) : RVert G → RVert G → Prop :=
  Quotient.lift₂ (fun p q : HamPath G => StepRep G p.1 q.1) (by
    rintro p₁ q₁ p₂ q₂ (h | h) (h' | h') <;>
      simp only [h, h', stepRep_rev_left, stepRep_rev_right])

/-- The backbite reconfiguration graph `R(G)`. Two (classes of) Hamiltonian paths are
adjacent when a single backbite carries one to the other (in either direction; see
`bbFront_invol` for invertibility). Loops are excluded, as in any simple graph. -/
def RGraph (G : SimpleGraph V) : SimpleGraph (RVert G) := SimpleGraph.fromRel (RRel G)

/-- `R(G)` is connected: any two Hamiltonian paths are joined by a backbite sequence.
(We use `Preconnected`, so a graph with no Hamiltonian path counts as connected.) -/
def RConnected (G : SimpleGraph V) : Prop := (RGraph G).Preconnected

/-- The class of a Hamiltonian path in `R(G)`. -/
def cls {G : SimpleGraph V} (l : List V) (h : IsHamPath G l) : RVert G :=
  Quotient.mk (revSetoid G) ⟨l, h⟩

end Kazazi
