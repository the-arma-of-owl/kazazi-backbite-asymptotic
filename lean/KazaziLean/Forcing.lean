import KazaziLean.Lemmas

/-!
# Forcing graphs, Lemma 1 and Fact B (§1 of the paper)
-/

set_option linter.unusedSectionVars false

namespace Kazazi

open List SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem cls_of_mem {l p : List V} (hl : IsHamPath G l) (hp : IsHamPath G p)
    (h : p ∈ [l, l.reverse]) : cls p hp = cls l hl := by
  simp only [mem_cons, not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · rfl
  · exact cls_reverse hl

theorem isHamPath_of_mem {l p : List V} (hl : IsHamPath G l) (h : p ∈ [l, l.reverse]) :
    IsHamPath G p := by
  simp only [mem_cons, not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact hl
  · exact isHamPath_reverse hl

theorem reachable_of_stepRep {l m : List V} (hl : IsHamPath G l) (hm : IsHamPath G m)
    (h : StepRep G l m) : (RGraph G).Reachable (cls l hl) (cls m hm) := by
  obtain ⟨p, hp, q, hq, hs⟩ := h
  have hpH := isHamPath_of_mem hl hp
  have r := reachable_of_step hpH hs
  rw [cls_of_mem hl hpH hp, cls_of_mem hm (isHamPath_of_step hpH hs) hq] at r
  exact r

/-- A graph `J` is **forcing** (paper, §1) if (i) `R(J)` is connected, and (ii) from every
ordering of `V(J)` (a Hamiltonian path of the complete graph) some sequence of backbites,
each adding an edge of `J`, reaches a Hamiltonian path of `J`.

`BBStep J` applied to an arbitrary ordering is exactly a backbite in the complete graph
whose added edge `w₁w_k` (resp. `w_n w_k`) is an edge of `J`. -/
def IsForcing (J : SimpleGraph V) : Prop :=
  RConnected J ∧
    ∀ l : List V, IsOrdering l → ∃ l', Relation.ReflTransGen (BBStep J) l l' ∧ IsHamPath J l'

theorem bbStep_mono {J : SimpleGraph V} (hJG : J ≤ G) {l l' : List V} (h : BBStep J l l') :
    BBStep G l l' := by
  rcases h with ⟨j, hj, h2, hadj, e⟩ | ⟨j, hj, hadj, e⟩
  · exact Or.inl ⟨j, hj, h2, hJG hadj, e⟩
  · exact Or.inr ⟨j, hj, hJG hadj, e⟩

theorem isHamPath_mono {J : SimpleGraph V} (hJG : J ≤ G) {l : List V} (h : IsHamPath J l) :
    IsHamPath G l := ⟨h.1, h.2.1, h.2.2.imp (fun _ _ h => hJG h)⟩

/-- `R(J)` embeds in `R(G)` for a spanning subgraph `J ≤ G`, preserving reachability. -/
theorem reachable_mono {J : SimpleGraph V} (hJG : J ≤ G) {l m : List V}
    (hl : IsHamPath J l) (hm : IsHamPath J m) (h : (RGraph J).Reachable (cls l hl) (cls m hm)) :
    (RGraph G).Reachable (cls l (isHamPath_mono hJG hl)) (cls m (isHamPath_mono hJG hm)) := by
  let f : RVert J → RVert G := Quotient.lift (s := revSetoid J)
    (fun p : HamPath J => (cls (G := G) p.1 (isHamPath_mono hJG p.2) : RVert G))
    (by
      rintro p q (h | h)
      · exact cls_eq_of_eq _ _ h.symm
      · simp only [h]; exact (cls_reverse (G := G) (isHamPath_mono hJG p.2)).symm)
  have key : ∀ P Q : RVert J, (RGraph J).Adj P Q → (RGraph G).Reachable (f P) (f Q) := by
    intro P Q hPQ
    induction P using Quotient.ind
    induction Q using Quotient.ind
    rename_i p q
    simp only [RGraph, fromRel_adj] at hPQ
    obtain ⟨_, h | h⟩ := hPQ
    · obtain ⟨p', hp', q', hq', hs⟩ := h
      exact reachable_of_stepRep _ _ ⟨p', hp', q', hq', bbStep_mono hJG hs⟩
    · obtain ⟨q', hq', p', hp', hs⟩ := h
      exact (reachable_of_stepRep _ _ ⟨q', hq', p', hp', bbStep_mono hJG hs⟩).symm
  obtain ⟨w⟩ := h
  have : ∀ {P Q : RVert J}, (RGraph J).Walk P Q → (RGraph G).Reachable (f P) (f Q) := by
    intro P Q w
    induction w with
    | nil => rfl
    | cons ha _ ih => exact (key _ _ ha).trans ih
  exact this w

/-- **Lemma 1.** If `G` contains a forcing graph `J` as a spanning subgraph, then `R(G)` is
connected. -/
theorem lemma1 {J : SimpleGraph V} (hJG : J ≤ G) (hJ : IsForcing J) : RConnected G := by
  -- every Hamiltonian path of `G` reaches (the image of) a Hamiltonian path of `J`
  have reach : ∀ p : HamPath G, ∃ l' : List V, ∃ hl' : IsHamPath J l',
      (RGraph G).Reachable (Quotient.mk _ p) (cls l' (isHamPath_mono hJG hl')) := by
    intro p
    obtain ⟨l', hr, hl'⟩ := hJ.2 p.1 ⟨p.2.1, p.2.2.1⟩
    have hrG : Relation.ReflTransGen (BBStep G) p.1 l' := by
      clear hl'
      induction hr with
      | refl => exact .refl
      | tail _ h ih => exact ih.tail (bbStep_mono hJG h)
    obtain ⟨_, hreach⟩ := reachable_of_rtg p.2 hrG
    exact ⟨l', hl', hreach⟩
  intro P Q
  induction P using Quotient.ind
  induction Q using Quotient.ind
  rename_i p q
  obtain ⟨lp, hlp, rp⟩ := reach p
  obtain ⟨lq, hlq, rq⟩ := reach q
  exact rp.trans ((reachable_mono hJG hlp hlq (hJ.1 _ _)).trans rq.symm)

/-- **Fact B (interval reversal).** Let a Hamiltonian cycle contain the segment
`a, u₁, …, u_t, b` with `t ≥ 2`, and suppose `a u_t, u₁ b ∈ E(G)`. Then the cycle obtained by
reversing `u₁ ⋯ u_t` is equivalent to the original.

A Hamiltonian cycle is represented by a cyclic Hamiltonian path starting at `a`
(`IsCyclic`); by `reachable_rotate` all its edge-deletions lie in the component of this
representative. Here `U = u₁ :: (mid ++ [u_t])`, so `t = |mid| + 2 ≥ 2`. -/
theorem factB {a b u1 ut : V} {mid rest : List V}
    (hc : IsHamPath G (a :: ((u1 :: (mid ++ [ut])) ++ b :: rest)))
    (hcyc : IsCyclic G (a :: ((u1 :: (mid ++ [ut])) ++ b :: rest)))
    (h1 : G.Adj a ut) (h2 : G.Adj u1 b) :
    ∃ h' : IsHamPath G (a :: ((u1 :: (mid ++ [ut])).reverse ++ b :: rest)),
      (RGraph G).Reachable (cls _ hc) (cls _ h') ∧
      IsCyclic G (a :: ((u1 :: (mid ++ [ut])).reverse ++ b :: rest)) := by
  set U := u1 :: (mid ++ [ut]) with hU
  -- delete the edge `a u₁`
  obtain ⟨hd, rd, _⟩ := reachable_rotate (x := [a]) (y := U ++ b :: rest) (by simpa using hc)
    (by simp [hU]; omega) (by simpa using hcyc)
  -- read from `a` and backbite with target `u_t`
  set d := U ++ b :: rest ++ [a] with hd_def
  have hdrev : d.reverse = (a :: (rest.reverse ++ [b])) ++ U.reverse := by simp [hd_def]
  have hlenj : (a :: (rest.reverse ++ [b])).length = rest.length + 2 := by simp
  have hj : rest.length + 2 < d.reverse.length := by rw [hdrev]; simp [hU]
  have hget0 : d.reverse[0]'(by omega) = a := by simp [hdrev]
  have hgetj : d.reverse[rest.length + 2]'hj = ut := by
    simp only [hdrev]
    rw [getElem_append_right (by simp)]
    simp [hU]
  have hstep : BBStep G d.reverse (b :: (rest ++ a :: U.reverse)) := by
    refine Or.inl ⟨rest.length + 2, hj, by omega, by rw [hget0, hgetj]; exact h1, ?_⟩
    rw [bbFront, hdrev, take_left' hlenj, drop_left' hlenj]
    simp
  have hdr := isHamPath_reverse hd
  have r2 := reachable_of_step hdr hstep
  rw [cls_reverse hd] at r2
  -- the new path is cyclic (endpoints `b`, `u₁`), rotate back to start at `a`
  have he := isHamPath_of_step hdr hstep
  have hcyc_e : IsCyclic G ((b :: rest) ++ (a :: U.reverse)) := by
    intro z hz y hy
    rw [show (b :: rest) ++ (a :: U.reverse) = (b :: rest ++ a :: ut :: mid.reverse) ++ [u1] by
      simp [hU]] at hz
    rw [getLast?_append] at hz
    simp at hz hy
    subst hz hy; exact h2
  obtain ⟨hf, rf, cf⟩ := reachable_rotate (x := b :: rest) (y := a :: U.reverse)
    (by simpa using he) (by simp [hU]; omega) hcyc_e
  refine ⟨hf, ?_, cf⟩
  refine (rd.trans r2).trans ?_
  convert rf using 2 <;> simp [hU]

end Kazazi
