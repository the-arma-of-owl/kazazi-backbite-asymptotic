import KazaziLean.Lemma3Lift

/-!
# Lemma 3, parts (a) and (b): all lifts lie in one component

Throughout, `H = G - v` and Hamiltonian paths of `H` are lists of vertices of `G` avoiding `v`
(`IsHamH`). Degree hypotheses (with `h = |V(H)| = |V| - 1`):
* `hdegH : ∀ x ≠ v, |V| + 3 ≤ 2 · |N_G(x) \ {v}|`   (i.e. `δ(H) ≥ h/2 + 2`);
* `hdegv : |V| + 3 ≤ 2 · |N_G(v)|`                   (i.e. `d ≥ h/2 + 2`).
-/

set_option linter.unusedSectionVars false

namespace Kazazi

open List SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem mem_of_isHamH {v : V} {P : List V} (hP : IsHamH G v P) {x : V} (hx : x ≠ v) : x ∈ P := by
  obtain ⟨hn, hv, hlen, _⟩ := hP
  have hsub : P.toFinset ⊆ Finset.univ.erase v := by
    intro y hy
    rw [List.mem_toFinset] at hy
    exact Finset.mem_erase.2 ⟨fun h => hv (h ▸ hy), Finset.mem_univ _⟩
  have hcard : (Finset.univ.erase v).card ≤ P.toFinset.card := by
    rw [List.toFinset_card_of_nodup hn, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  have := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← List.mem_toFinset, this]
  exact Finset.mem_erase.2 ⟨hx, Finset.mem_univ _⟩

theorem elig_iff_mem {v : V} {P : List V} {i : ℕ} :
    Elig G v P i ↔ i ∈ eligible P (G.neighborFinset v) := by
  simp only [Elig, eligible, Finset.mem_filter, Finset.mem_range, mem_neighborFinset]
  constructor
  · rintro ⟨h, h1, h2⟩; exact ⟨by omega, h, h1, h2⟩
  · rintro ⟨_, h, h1, h2⟩; exact ⟨h, h1, h2⟩

/-- At least three eligible edges (paper: `2d - h - 1 ≥ 3`). -/
theorem three_le_eligible {v : V} {P : List V} (hP : IsHamH G v P)
    (hdegv : Fintype.card V + 3 ≤ 2 * G.degree v) :
    3 ≤ (eligible P (G.neighborFinset v)).card := by
  have hcov : ∀ x ∈ G.neighborFinset v, x ∈ P := by
    intro x hx
    exact mem_of_isHamH hP (fun h => by subst h; exact G.irrefl ((mem_neighborFinset _ _ _).1 hx))
  have := eligible_card P (G.neighborFinset v) hcov
  rw [card_neighborFinset_eq_degree] at this
  have := hP.2.2.1
  omega

theorem exists_two_elig {v : V} {P : List V} (hP : IsHamH G v P)
    (hdegv : Fintype.card V + 3 ≤ 2 * G.degree v) :
    ∃ i₁ i₂, i₁ ≠ i₂ ∧ Elig G v P i₁ ∧ Elig G v P i₂ := by
  have h3 := three_le_eligible hP hdegv
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < (eligible P (G.neighborFinset v)).card by omega)
  exact ⟨a, b, hab, elig_iff_mem.2 ha, elig_iff_mem.2 hb⟩

theorem isHamH_bbFront {v : V} {P : List V} (hP : IsHamH G v P) {j : ℕ} (hj : j < P.length)
    (hadj : G.Adj (P[0]'(by omega)) P[j]) : IsHamH G v (bbFront P j) := by
  obtain ⟨hn, hv, hlen, hc⟩ := hP
  have hp := bbFront_perm P j
  exact ⟨hp.nodup_iff.2 hn, fun h => hv (hp.mem_iff.1 h), by rw [hp.length_eq]; exact hlen,
    isChain_bbFront hc hj hadj⟩

theorem isHamH_reverse {v : V} {P : List V} (hP : IsHamH G v P) : IsHamH G v P.reverse :=
  ⟨nodup_reverse.2 hP.1, by simpa using hP.2.1, by simpa using hP.2.2.1,
    isChain_symm_reverse hP.2.2.2⟩

theorem isHamH_of_step {v : V} {P Q : List V} (hP : IsHamH G v P) (h : BBStep G P Q) :
    IsHamH G v Q := by
  rcases h with ⟨j, hj, _, hadj, rfl⟩ | h
  · exact isHamH_bbFront hP hj hadj
  · rw [bbBack_iff_front_reverse] at h
    obtain ⟨j, hj, _, hadj, h⟩ := h
    have := isHamH_bbFront (isHamH_reverse hP) hj hadj
    rw [← h] at this
    simpa using isHamH_reverse this

/-- Step (b) for an arbitrary backbite, given two distinct eligible edges. -/
theorem commute_step {v : V} {P Q : List V} (h : BBStep G P Q) {i₁ i₂ : ℕ} (hne : i₁ ≠ i₂)
    (he₁ : Elig G v P i₁) (he₂ : Elig G v P i₂) :
    ∃ i i', Elig G v P i ∧ Elig G v Q i' ∧ BBStep G (liftAt v P i) (liftAt v Q i') := by
  rcases h with ⟨j, hj, hj2, hadj, rfl⟩ | ⟨j, hj, hadj, rfl⟩
  · by_cases h1 : i₁ + 1 = j
    · obtain ⟨i', he', hs⟩ := commute_front hj hj2 hadj he₂ (by omega)
      exact ⟨i₂, i', he₂, he', Or.inl hs⟩
    · obtain ⟨i', he', hs⟩ := commute_front hj hj2 hadj he₁ h1
      exact ⟨i₁, i', he₁, he', Or.inl hs⟩
  · by_cases h1 : i₁ = j
    · obtain ⟨i', he', hs⟩ := commute_back hj hadj he₂ (by omega)
      exact ⟨i₂, i', he₂, he', Or.inr hs⟩
    · obtain ⟨i', he', hs⟩ := commute_back hj hadj he₁ h1
      exact ⟨i₁, i', he₁, he', Or.inr hs⟩

/-- Swapping the two parts of a cyclic chain gives a cyclic chain. -/
theorem cyclic_swap {A B : List V} (hA : A ≠ []) (hB : B ≠ []) (hc : (A ++ B).IsChain G.Adj)
    (hcyc : IsCyclic G (A ++ B)) : (B ++ A).IsChain G.Adj ∧ IsCyclic G (B ++ A) := by
  obtain ⟨hcA, hcB, hlink⟩ := isChain_append.1 hc
  refine ⟨IsChain.append hcB hcA ?_, ?_⟩
  · intro x hx y hy
    apply hcyc x _ y _
    · rw [getLast?_append_of_ne_nil _ hB]; exact hx
    · rw [head?_append_of_ne_nil _ hA]; exact hy
  · intro z hz y hy
    apply hlink z _ y _
    · rwa [getLast?_append_of_ne_nil _ hA] at hz
    · rwa [head?_append_of_ne_nil _ hB] at hy

theorem isCyclic_liftAt {v : V} {P : List V} (hcyc : IsCyclic G P) {i : ℕ}
    (hi : i + 1 < P.length) : IsCyclic G (liftAt v P i) := by
  have hl := length_liftAt v P hi
  apply isCyclic_of_getElem (by omega)
  rw [getElem_liftAt_le v P (k := 0) (by omega) hi]
  have e : (liftAt v P i)[(liftAt v P i).length - 1]'(by omega) = P[P.length - 1] := by
    have := getElem_liftAt_gt v P (i := i) (k := P.length - 1) (by omega) (by omega)
    convert this using 2; omega
  rw [e]
  exact (isCyclic_iff_getElem (by omega)).1 hcyc

/-- **(a), cyclic case.** All lifts of a Hamiltonian path of `H` with adjacent endpoints lie in
one component (they are all in the attachment component of the cycle). -/
theorem lifts_cyclic {v : V} {P : List V} (hP : IsHamH G v P) (hcyc : IsCyclic G P)
    {i₁ i₂ : ℕ} (he₁ : Elig G v P i₁) (he₂ : Elig G v P i₂) :
    (RGraph G).Reachable (cls _ (isHamPath_liftAt hP he₁)) (cls _ (isHamPath_liftAt hP he₂)) := by
  -- each lift reaches the attachment `v :: P.rotate (i+1)`
  have key : ∀ i (he : Elig G v P i), ∃ h' : IsHamPath G (v :: P.rotate (i + 1)),
      (RGraph G).Reachable (cls _ (isHamPath_liftAt hP he)) (cls _ h') ∧
      IsCyclic G (P.rotate (i + 1)) := by
    intro i he
    have hi := he.1
    have hL := isHamPath_liftAt hP he
    have hLc := isCyclic_liftAt (v := v) hcyc hi
    obtain ⟨h', r, _⟩ := reachable_rotate (x := P.take (i + 1)) (y := v :: P.drop (i + 1)) hL
      (by rw [show P.take (i + 1) ++ v :: P.drop (i + 1) = liftAt v P i from rfl,
        length_liftAt v P hi]; have := hP.2.2.1; omega) hLc
    have hrot : P.rotate (i + 1) = P.drop (i + 1) ++ P.take (i + 1) :=
      rotate_eq_drop_append_take (by omega)
    refine ⟨by rw [hrot]; simpa using h', ?_, ?_⟩
    · convert r using 2
      all_goals first | rfl | (rw [hrot]; simp)
    · rw [hrot]
      refine (cyclic_swap (A := P.take (i + 1)) (B := P.drop (i + 1)) ?_ ?_ ?_ ?_).2
      · intro h; have := congrArg length h; simp only [length_take, length_nil] at this; omega
      · intro h; have := congrArg length h; simp only [length_drop, length_nil] at this; omega
      · rw [take_append_drop]; exact hP.2.2.2
      · rw [take_append_drop]; exact hcyc
  obtain ⟨h1, r1, c1⟩ := key i₁ he₁
  obtain ⟨h2, r2, _⟩ := key i₂ he₂
  have hlen : 2 ≤ P.length := by have := he₁.1; omega
  have ht : P.rotate (i₂ + 1) = (P.rotate (i₁ + 1)).rotate (P.length - (i₁ + 1) + (i₂ + 1)) := by
    rw [rotate_rotate, show i₁ + 1 + (P.length - (i₁ + 1) + (i₂ + 1)) = (i₂ + 1) + P.length by
      have := he₁.1; omega]
    conv_rhs => rw [← rotate_mod, Nat.add_mod_right, rotate_mod]
  have ht0 : 0 < (P.rotate (i₂ + 1)).length := by simp; omega
  have hv : G.Adj v ((P.rotate (i₂ + 1))[0]'ht0) := by
    have := he₂.2.2
    simpa [getElem_rotate, Nat.mod_eq_of_lt he₂.1] using this
  obtain ⟨h3, r3⟩ := attachments_connected h1 c1 (by simpa using hlen) (t := P.rotate (i₂ + 1))
    (Or.inl ⟨_, ht⟩) ht0 hv
  exact r1.trans (r3.trans r2.symm)

/-! ### Fact A inside `H` -/

/-- Fact A for a Hamiltonian path of `H = G - v` with non-adjacent endpoints, under
`δ(H) ≥ h/2 + 2`: at least `3` crossing indices (the paper gets `5` from the exact count; the
weaker general bound used here loses `2`, and `3` suffices for the proof). -/
theorem three_le_crossings_H {v : V} {P : List V} (hP : IsHamH G v P) (h0 : 0 < P.length)
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card) :
    3 ≤ (crossings G P (P[0]'h0) (P[P.length - 1]'(by omega))).card := by
  set a := P[0]'h0
  set b := P[P.length - 1]'(by omega)
  have hva : a ≠ v := fun h => hP.2.1 (h ▸ getElem_mem _)
  have hvb : b ≠ v := fun h => hP.2.1 (h ▸ getElem_mem _)
  set Na := (G.neighborFinset a).erase v
  set Nb := (G.neighborFinset b).erase v
  have hcov : ∀ N : Finset V, (∀ x ∈ N, x ≠ v) → ∀ x ∈ N, x ∈ P :=
    fun N hN x hx => mem_of_isHamH hP (hN x hx)
  have hNa : ∀ x ∈ Na, x ∈ P := hcov Na (fun x hx => (Finset.mem_erase.1 hx).1)
  have hNb : ∀ x ∈ Nb, x ∈ P := hcov Nb (fun x hx => (Finset.mem_erase.1 hx).1)
  set S := (Finset.range (P.length - 1)).filter (fun i => ∃ h : i + 1 < P.length, P[i + 1] ∈ Na)
  set T := (Finset.range (P.length - 1)).filter (fun i => ∃ h : i + 0 < P.length, P[i + 0] ∈ Nb)
  have hS : Na.card ≤ S.card + 1 := card_shift_ge P Na hNa 1 le_rfl
  have hT : Nb.card ≤ T.card + 1 := card_shift_ge P Nb hNb 0 (by omega)
  have hU : (S ∪ T).card ≤ P.length - 1 := by
    calc (S ∪ T).card ≤ (Finset.range (P.length - 1)).card :=
          Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
            (Finset.filter_subset _ _))
      _ = P.length - 1 := Finset.card_range _
  have hI : (S ∩ T).card ≤ (crossings G P a b).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [S, T, Finset.mem_inter, Finset.mem_filter, crossings, Nat.add_zero,
      Finset.mem_erase, mem_neighborFinset, Na, Nb] at hi ⊢
    obtain ⟨⟨hr, h1, _, ha⟩, _, _, _, hb⟩ := hi
    exact ⟨hr, h1, ha, hb⟩
  have := Finset.card_union_add_card_inter S T
  have h1 : Fintype.card V + 3 ≤ 2 * Na.card := hdegH a hva
  have h2 : Fintype.card V + 3 ≤ 2 * Nb.card := hdegH b hvb
  have := hP.2.2.1
  omega

/-- **(a), general case.** All lifts of one Hamiltonian path of `H` lie in one component. -/
theorem lifts_same {v : V} {P : List V} (hP : IsHamH G v P)
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card)
    {i₁ i₂ : ℕ} (he₁ : Elig G v P i₁) (he₂ : Elig G v P i₂) :
    (RGraph G).Reachable (cls _ (isHamPath_liftAt hP he₁)) (cls _ (isHamPath_liftAt hP he₂)) := by
  have h0 : 0 < P.length := by have := he₁.1; omega
  by_cases hc : G.Adj (P[P.length - 1]'(by omega)) (P[0]'h0)
  · exact lifts_cyclic hP (isCyclic_of_getElem h0 hc) he₁ he₂
  · have hab : ¬ G.Adj (P[0]'h0) (P[P.length - 1]'(by omega)) := fun h => hc (G.adj_symm h)
    have h3 := three_le_crossings_H hP h0 hdegH
    -- a crossing index different from `i₁` and `i₂`
    obtain ⟨c, hc1, hc2⟩ : ∃ c ∈ crossings G P (P[0]'h0) (P[P.length - 1]'(by omega)),
        c ≠ i₁ ∧ c ≠ i₂ := by
      by_contra hne
      push_neg at hne
      have : crossings G P (P[0]'h0) (P[P.length - 1]'(by omega)) ⊆ {i₁, i₂} := by
        intro c hc
        by_cases h : c = i₁
        · simp [h]
        · simp [hne c hc h]
      have := Finset.card_le_card this
      have := Finset.card_insert_le i₁ ({i₂} : Finset ℕ)
      simp at this
      omega
    obtain ⟨hb1, hb3⟩ := crossings_bounds G hP.1 h0 hab hc1
    have hc1' := hc1
    simp only [crossings, Finset.mem_filter, Finset.mem_range] at hc1'
    obtain ⟨_, hj, ha, hb⟩ := hc1'
    set P' := bbFront P (c + 1)
    have hP' : IsHamH G v P' := isHamH_bbFront hP hj ha
    have hcyc' : IsCyclic G P' := by
      have hlen : P'.length = P.length := (bbFront_perm P _).length_eq
      apply isCyclic_of_getElem (by omega)
      have e1 : P'[P'.length - 1]'(by omega) = P[P.length - 1] := bbFront_getElem_last P hj
      have e2 : P'[0]'(by omega) = P[c] := by
        have := bbFront_getElem_zero P (j := c + 1) (by omega) (by omega)
        simpa using this
      rw [e1, e2]; exact hb
    obtain ⟨i₁', he₁', hs₁⟩ := commute_front hj (by omega) ha he₁ (by omega)
    obtain ⟨i₂', he₂', hs₂⟩ := commute_front hj (by omega) ha he₂ (by omega)
    have r1 := reachable_of_step (isHamPath_liftAt hP he₁) (Or.inl hs₁)
    have r2 := reachable_of_step (isHamPath_liftAt hP he₂) (Or.inl hs₂)
    have r3 := lifts_cyclic hP' hcyc' he₁' he₂'
    exact r1.trans (r3.trans r2.symm)

/-- `P` and `Q` have all their lifts in one component. -/
def LiftsConn (G : SimpleGraph V) (v : V) (P Q : List V) : Prop :=
  ∀ (hP : IsHamH G v P) (hQ : IsHamH G v Q) (i : ℕ) (hi : Elig G v P i) (j : ℕ)
    (hj : Elig G v Q j),
    (RGraph G).Reachable (cls _ (isHamPath_liftAt hP hi)) (cls _ (isHamPath_liftAt hQ hj))

/-- **(b).** Lifts of `R(H)`-adjacent paths are joined. -/
theorem liftsConn_of_step {v : V} {P Q : List V}
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card)
    (hdegv : Fintype.card V + 3 ≤ 2 * G.degree v) (h : BBStep G P Q) : LiftsConn G v P Q := by
  intro hP hQ i hi j hj
  obtain ⟨i₁, i₂, hne, he₁, he₂⟩ := exists_two_elig hP hdegv
  obtain ⟨k, k', hk, hk', hs⟩ := commute_step h hne he₁ he₂
  have r := reachable_of_step (isHamPath_liftAt hP hk) hs
  exact (lifts_same hP hdegH hi hk).trans (r.trans (lifts_same hQ hdegH hk' hj))

theorem liftsConn_reverse {v : V} {P : List V}
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card) :
    LiftsConn G v P P.reverse := by
  intro hP hQ i hi j hj
  have hj1 := hj.1
  simp only [length_reverse] at hj1
  have he : Elig G v P (P.length - 2 - j) := by
    have := elig_reverse hj
    simpa using this
  have e : liftAt v P.reverse j = (liftAt v P (P.length - 2 - j)).reverse := by
    rw [liftAt_reverse v P (by omega)]; congr 1; omega
  have : cls (liftAt v P.reverse j) (isHamPath_liftAt hQ hj) =
      cls (liftAt v P (P.length - 2 - j)) (isHamPath_liftAt hP he) := by
    rw [← cls_reverse (isHamPath_liftAt hP he)]; exact cls_eq_of_eq _ _ e
  rw [this]
  exact lifts_same hP hdegH hi he

theorem liftsConn_trans {v : V} {P Q R : List V}
    (hdegv : Fintype.card V + 3 ≤ 2 * G.degree v) (hQ : IsHamH G v Q)
    (h1 : LiftsConn G v P Q) (h2 : LiftsConn G v Q R) : LiftsConn G v P R := by
  intro hP hR i hi j hj
  obtain ⟨k, _, _, hk, _⟩ := exists_two_elig hQ hdegv
  exact (h1 hP hQ i hi k hk).trans (h2 hQ hR k hk j hj)

theorem liftsConn_symm {v : V} {P Q : List V} (h : LiftsConn G v P Q) : LiftsConn G v Q P :=
  fun hQ hP i hi j hj => (h hP hQ j hj i hi).symm

end Kazazi
