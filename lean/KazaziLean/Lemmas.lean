import KazaziLean.Defs

/-!
# Elementary facts about backbites (§1 of the paper)

* backbites preserve Hamiltonian paths;
* a backbite is invertible (`bbFront_invol`, `bbStep_symm`);
* a backbite at the last endpoint is a backbite at the first endpoint of the reversal;
* rotations of a cyclic Hamiltonian path stay in one component of `R(G)`.
-/

set_option linter.unusedSectionVars false

namespace Kazazi

open List

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem bbFront_perm (l : List V) (j : ℕ) : bbFront l j ~ l := by
  unfold bbFront
  calc (l.take j).reverse ++ l.drop j ~ l.take j ++ l.drop j := (reverse_perm _).append_right _
    _ = l := take_append_drop j l

theorem bbBack_perm (l : List V) (j : ℕ) : bbBack l j ~ l := by
  unfold bbBack
  calc l.take (j + 1) ++ (l.drop (j + 1)).reverse ~ l.take (j + 1) ++ l.drop (j + 1) :=
        (reverse_perm _).append_left _
    _ = l := take_append_drop _ l

theorem bbFront_invol (l : List V) {j : ℕ} (hj : j ≤ l.length) :
    bbFront (bbFront l j) j = l := by
  unfold bbFront
  have h1 : ((l.take j).reverse).length = j := by simp; omega
  rw [take_left' h1, drop_left' h1, reverse_reverse, take_append_drop]

theorem bbBack_invol (l : List V) {j : ℕ} (hj : j + 1 ≤ l.length) :
    bbBack (bbBack l j) j = l := by
  unfold bbBack
  have h1 : (l.take (j + 1)).length = j + 1 := by simp; omega
  rw [take_left' h1, drop_left' h1, reverse_reverse, take_append_drop]

theorem isChain_symm_reverse {l : List V} (h : l.IsChain G.Adj) : l.reverse.IsChain G.Adj := by
  rw [isChain_reverse]; exact h.imp (fun _ _ h => G.adj_symm h)

theorem isChain_bbFront {l : List V} (hc : l.IsChain G.Adj) {j : ℕ} (hj : j < l.length)
    (hadj : G.Adj (l[0]'(by omega)) l[j]) : (bbFront l j).IsChain G.Adj := by
  have hc' := hc
  rw [← take_append_drop j l] at hc'
  unfold bbFront
  refine IsChain.append (isChain_symm_reverse hc'.left_of_append) hc'.right_of_append ?_
  intro x hx y hy
  have hj0 : 0 < j ∨ j = 0 := by omega
  rcases hj0 with hj0 | hj0
  · rw [getLast?_reverse, head?_take] at hx
    simp only [show j ≠ 0 by omega, ite_false, head?_eq_getElem?, getElem?_eq_getElem (by omega : 0 < l.length),
      Option.mem_def, Option.some.injEq] at hx
    rw [head?_drop, getElem?_eq_getElem hj, Option.mem_def, Option.some.injEq] at hy
    subst hx hy; exact hadj
  · subst hj0; simp at hx

theorem isHamPath_bbFront {l : List V} (hl : IsHamPath G l) {j : ℕ} (hj : j < l.length)
    (hadj : G.Adj (l[0]'(by omega)) l[j]) : IsHamPath G (bbFront l j) := by
  refine ⟨(bbFront_perm l j).nodup_iff.2 hl.1, ?_, isChain_bbFront hl.2.2 hj hadj⟩
  rw [(bbFront_perm l j).length_eq, hl.2.1]

/-- The back backbite is the front backbite on the reversed path, read backwards. -/
theorem bbBack_eq (l : List V) {j : ℕ} (hj : j + 1 ≤ l.length) :
    bbBack l j = (bbFront l.reverse (l.length - 1 - j)).reverse := by
  unfold bbBack bbFront
  rw [take_reverse, drop_reverse, reverse_append, reverse_reverse,
    show l.length - (l.length - 1 - j) = j + 1 by omega]
  simp

theorem bbBack_iff_front_reverse {l l' : List V} :
    BBBack G l l' ↔ BBFront G l.reverse l'.reverse := by
  constructor
  · rintro ⟨j, hj, hadj, rfl⟩
    refine ⟨l.length - 1 - j, by simp; omega, by omega, ?_, ?_⟩
    · simp only [getElem_reverse]
      convert hadj using 2
      all_goals (try simp)
      all_goals omega
    · rw [bbBack_eq l (by omega), reverse_reverse]
  · rintro ⟨i, hi, hi2, hadj, h⟩
    simp only [length_reverse] at hi
    refine ⟨l.length - 1 - i, by omega, ?_, ?_⟩
    · simp only [getElem_reverse] at hadj
      convert hadj using 2
    · rw [bbBack_eq l (by omega), show l.length - 1 - (l.length - 1 - i) = i by omega, ← h,
        reverse_reverse]

theorem isHamPath_of_step {l l' : List V} (hl : IsHamPath G l) (h : BBStep G l l') :
    IsHamPath G l' := by
  rcases h with ⟨j, hj, _, hadj, rfl⟩ | h
  · exact isHamPath_bbFront hl hj hadj
  · rw [bbBack_iff_front_reverse] at h
    obtain ⟨j, hj, _, hadj, h⟩ := h
    have := isHamPath_bbFront (isHamPath_reverse hl) hj hadj
    rw [← h] at this
    simpa using isHamPath_reverse this

/-- A backbite is invertible (paper: `bb(w_{k-1},w_k)` undoes `bb(w₁,w_k)`). -/
theorem bbFront_symm {l l' : List V} (hc : l.IsChain G.Adj) (h : BBFront G l l') :
    BBFront G l' l := by
  obtain ⟨j, hj, h2, _, rfl⟩ := h
  have hlen : (bbFront l j).length = l.length := (bbFront_perm l j).length_eq
  refine ⟨j, by omega, h2, ?_, (bbFront_invol l hj.le).symm⟩
  have e0 : (bbFront l j)[0]'(by omega) = l[j - 1] := by
    simp only [bbFront]
    rw [getElem_append_left (by simp; omega)]
    simp [Nat.min_eq_left hj.le]
  have ej : (bbFront l j)[j]'(by omega) = l[j] := by
    simp only [bbFront]
    rw [getElem_append_right (by simp)]
    simp [Nat.min_eq_left hj.le]
  rw [e0, ej]
  have := hc.getElem (j - 1) (by omega)
  simpa [show j - 1 + 1 = j by omega] using this

theorem bbStep_symm {l l' : List V} (hc : l.IsChain G.Adj) (h : BBStep G l l') :
    BBStep G l' l := by
  rcases h with h | h
  · exact Or.inl (bbFront_symm hc h)
  · rw [bbBack_iff_front_reverse] at h
    exact Or.inr (bbBack_iff_front_reverse.2 (bbFront_symm (isChain_symm_reverse hc) h))

/-! ### From list-level backbite sequences to walks in `R(G)` -/

theorem cls_reverse {l : List V} (hl : IsHamPath G l) :
    cls l.reverse (isHamPath_reverse hl) = cls l hl :=
  Quotient.sound (Or.inr (reverse_reverse l).symm)

theorem cls_eq_of_eq {l l' : List V} (hl : IsHamPath G l) (hl' : IsHamPath G l') (h : l = l') :
    cls l hl = cls l' hl' := by subst h; rfl

theorem reachable_of_step {l l' : List V} (hl : IsHamPath G l) (h : BBStep G l l') :
    (RGraph G).Reachable (cls l hl) (cls l' (isHamPath_of_step hl h)) := by
  by_cases he : cls l hl = cls l' (isHamPath_of_step hl h)
  · rw [he]
  · refine SimpleGraph.Adj.reachable ?_
    rw [RGraph, SimpleGraph.fromRel_adj]
    exact ⟨he, Or.inl ⟨l, by simp, l', by simp, h⟩⟩

theorem reachable_of_rtg {l l' : List V} (hl : IsHamPath G l)
    (h : Relation.ReflTransGen (BBStep G) l l') :
    ∃ hl' : IsHamPath G l', (RGraph G).Reachable (cls l hl) (cls l' hl') := by
  induction h with
  | refl => exact ⟨hl, SimpleGraph.Reachable.refl _⟩
  | tail _ hs ih =>
    obtain ⟨hb, hr⟩ := ih
    exact ⟨_, hr.trans (reachable_of_step hb hs)⟩

/-- Cyclic: the last vertex is adjacent to the first. -/
def IsCyclic (G : SimpleGraph V) (c : List V) : Prop :=
  ∀ z ∈ c.getLast?, ∀ y ∈ c.head?, G.Adj z y

/-- **Rotation** (paper, "Cycles"): for a Hamiltonian path `a, l` with adjacent endpoints,
moving the missing edge one step gives `l, a`, in the same component. -/
theorem reachable_rotate_one {a : V} {l : List V} (hl : IsHamPath G (a :: l))
    (hlen : 2 ≤ l.length) (hcyc : IsCyclic G (a :: l)) :
    ∃ h' : IsHamPath G (l ++ [a]), (RGraph G).Reachable (cls (a :: l) hl) (cls _ h') ∧
      IsCyclic G (l ++ [a]) := by
  have hne : l ≠ [] := by rintro rfl; simp at hlen
  have hstep : BBStep G (a :: l) (a :: l.reverse) := by
    refine Or.inr ⟨0, by simp; omega, ?_, ?_⟩
    · have := hcyc ((a :: l).getLast (by simp)) (by simp [getLast?_eq_some_getLast]) a (by simp)
      convert this using 1 <;> simp [getLast_eq_getElem]
    · simp [bbBack]
  have hrev := isHamPath_of_step hl hstep
  have h' : IsHamPath G (l ++ [a]) := by simpa using isHamPath_reverse hrev
  refine ⟨h', ?_, ?_⟩
  · have := reachable_of_step hl hstep
    have e : cls (a :: l.reverse) (isHamPath_of_step hl hstep) = cls (l ++ [a]) h' := by
      rw [← cls_reverse h']; exact cls_eq_of_eq _ _ (by simp)
    rwa [e] at this
  · intro z hz y hy
    simp at hz; subst hz
    obtain ⟨y0, l', rfl⟩ := exists_cons_of_ne_nil hne
    simp at hy; subst hy
    exact (isChain_cons_cons.1 hl.2.2).1

/-- All rotations of a cyclic Hamiltonian path lie in one component of `R(G)`. -/
theorem reachable_rotate {x y : List V} (hl : IsHamPath G (x ++ y)) (hlen : 3 ≤ (x ++ y).length)
    (hcyc : IsCyclic G (x ++ y)) :
    ∃ h' : IsHamPath G (y ++ x), (RGraph G).Reachable (cls (x ++ y) hl) (cls _ h') ∧
      IsCyclic G (y ++ x) := by
  induction x generalizing y with
  | nil => exact ⟨by simpa using hl, by simp, by simpa using hcyc⟩
  | cons a x ih =>
    obtain ⟨h1, r1, c1⟩ := reachable_rotate_one (a := a) (l := x ++ y) hl
      (by simp at hlen ⊢; omega) hcyc
    have e : x ++ y ++ [a] = x ++ (y ++ [a]) := by simp
    rw [e] at h1 c1
    obtain ⟨h2, r2, c2⟩ := ih (y := y ++ [a]) h1 (by simp at hlen ⊢; omega) c1
    refine ⟨by simpa using h2, ?_, by simpa using c2⟩
    refine r1.trans ?_
    convert r2 using 2; simp

end Kazazi
