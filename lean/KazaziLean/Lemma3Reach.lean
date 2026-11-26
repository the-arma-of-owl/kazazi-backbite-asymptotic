import KazaziLean.Lemma3Conn

/-!
# Lemma 3, "Every path reaches `𝒦`"

Every Hamiltonian path of `G` is joined in `R(G)` to a lift of a Hamiltonian path of `H`.
-/

set_option linter.unusedSectionVars false

namespace Kazazi

open List SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem cyclic_rotate {s : List V} (hc : s.IsChain G.Adj) (hcyc : IsCyclic G s) (k : ℕ) :
    (s.rotate k).IsChain G.Adj ∧ IsCyclic G (s.rotate k) := by
  rcases Nat.eq_zero_or_pos s.length with h0 | h0
  · rw [length_eq_zero_iff.1 h0]; simp only [rotate_nil]; exact ⟨.nil, by simp [IsCyclic]⟩
  have hk : k % s.length < s.length := Nat.mod_lt _ h0
  rw [← rotate_mod]
  rcases Nat.eq_zero_or_pos (k % s.length) with hz | hz
  · rw [hz, rotate_zero]; exact ⟨hc, hcyc⟩
  · rw [rotate_eq_drop_append_take hk.le]
    refine cyclic_swap ?_ ?_ (by rwa [take_append_drop]) (by rwa [take_append_drop])
    · intro h; have := congrArg length h; simp only [length_take, length_nil] at this; omega
    · intro h; have := congrArg length h; simp only [length_drop, length_nil] at this; omega

theorem isHamH_rotate {v : V} {s : List V} (hs : IsHamH G v s) (hcyc : IsCyclic G s) (k : ℕ) :
    IsHamH G v (s.rotate k) ∧ IsCyclic G (s.rotate k) := by
  have hp := rotate_perm s k
  obtain ⟨h1, h2⟩ := cyclic_rotate hs.2.2.2 hcyc k
  exact ⟨⟨hp.nodup_iff.2 hs.1, fun h => hs.2.1 (hp.mem_iff.1 h), by simpa using hs.2.2.1, h1⟩, h2⟩

/-- Steps 4–5: from an attachment `v :: s` to a cycle `s` of `H` with an eligible edge, reach a
lift. -/
theorem reach_lift_of_attach {v : V} {s : List V} (hl : IsHamPath G (v :: s)) (hs : IsHamH G v s)
    (hcyc : IsCyclic G s) {i : ℕ} (he : Elig G v s i) :
    ∃ P m, ∃ (hP : IsHamH G v P) (hm : Elig G v P m),
      (RGraph G).Reachable (cls _ hl) (cls _ (isHamPath_liftAt hP hm)) := by
  obtain ⟨hi, hvi, hvi1⟩ := he
  -- attachment at `s[i+1]`
  have hv0 : G.Adj v ((s.rotate (i + 1))[0]'(by simp; omega)) := by
    simpa [getElem_rotate, Nat.mod_eq_of_lt hi] using hvi1
  obtain ⟨ht, r1⟩ := attach_rotate' hl hcyc (i + 1) (by omega) hv0
  obtain ⟨t0, T', z, htT⟩ : ∃ t0 T' z, s.rotate (i + 1) = t0 :: (T' ++ [z]) := by
    rcases h : s.rotate (i + 1) with _ | ⟨t0, T⟩
    · have := congrArg length h; simp only [length_rotate, length_nil] at this; omega
    · rcases T.eq_nil_or_concat' with rfl | ⟨T', z, rfl⟩
      · have := congrArg length h; simp only [length_rotate, length_cons, length_nil] at this
        omega
      · exact ⟨t0, T', z, rfl⟩
  have hlen : T'.length + 2 = s.length := by
    have := congrArg length htT; simp at this; omega
  -- the next path of `H`: `P' = T' ++ [z, t0] = s.rotate (i + 2)`
  have hP'eq : s.rotate (i + 2) = T' ++ [z, t0] := by
    rw [show i + 2 = (i + 1) + 1 by rfl, ← rotate_rotate, htT, rotate_cons_succ, rotate_zero]
    simp
  obtain ⟨hP', _⟩ := isHamH_rotate hs hcyc (i + 2)
  rw [hP'eq] at hP'
  have hz : z = s[i] := by
    have := getElem_rotate (l := s) (n := i + 2) (k := T'.length) (by simp; omega)
    have e : (T'.length + (i + 2)) % s.length = i := by
      rw [show T'.length + (i + 2) = i + s.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    simp only [hP'eq, e] at this
    simpa using this
  have ht0 : t0 = s[i + 1] := by
    have := getElem_rotate (l := s) (n := i + 2) (k := T'.length + 1) (by simp; omega)
    have e : (T'.length + 1 + (i + 2)) % s.length = i + 1 := by
      rw [show T'.length + 1 + (i + 2) = (i + 1) + s.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hi]
    simp only [hP'eq, e] at this
    simpa using this
  have hm : Elig G v (T' ++ [z, t0]) T'.length := by
    refine ⟨by simp, ?_, ?_⟩
    · simpa [hz] using hvi
    · simpa [ht0] using hvi1
  -- `v :: t0 :: T' ++ [z]` is cyclic in `G` (`z ~ v`); rotate it to the lift
  have ht' : IsHamPath G (v :: t0 :: (T' ++ [z])) := htT ▸ ht
  have r1' : (RGraph G).Reachable (cls _ hl) (cls _ ht') := by
    rw [← cls_eq_of_eq ht ht' (by rw [htT])]; exact r1
  have hcycG : IsCyclic G ([v, t0] ++ (T' ++ [z])) := by
    intro a ha b hb
    simp only [cons_append, nil_append] at ha hb
    rw [show v :: t0 :: (T' ++ [z]) = (v :: t0 :: T') ++ [z] by simp, getLast?_append] at ha
    simp at ha hb
    subst ha hb
    rw [hz]; exact G.adj_symm hvi
  obtain ⟨h2, r2, _⟩ := reachable_rotate (x := [v, t0]) (y := T' ++ [z]) (by simpa using ht')
    (by simp) hcycG
  have hlift : liftAt v (T' ++ [z, t0]) T'.length = (T' ++ [z]) ++ [v, t0] := by
    have h1 : (T' ++ [z]).length = T'.length + 1 := by simp
    rw [liftAt, show T' ++ [z, t0] = (T' ++ [z]) ++ [t0] by simp, take_left' h1, drop_left' h1]
  refine ⟨_, _, hP', hm, r1'.trans ?_⟩
  convert r2 using 2
  all_goals first | rfl | simp [hlift]

theorem getElem_cons_length (v : V) (s : List V) (h : 0 < s.length) :
    (v :: s)[s.length]'(by simp) = s[s.length - 1] := by
  rw [getElem_cons, dif_neg (by omega)]

theorem isHamH_of_cons {v : V} {s : List V} (h : IsHamPath G (v :: s)) : IsHamH G v s := by
  obtain ⟨hn, hlen, hc⟩ := h
  rw [nodup_cons] at hn
  exact ⟨hn.2, hn.1, by simpa using hlen, (isChain_cons.1 hc).2⟩

/-- Step 1: every Hamiltonian path is joined to a cyclic one (Fact A in `G`). -/
theorem reach_cyclic (hdeg : ∀ x, Fintype.card V + 3 ≤ 2 * G.degree x) {Q : List V}
    (hQ : IsHamPath G Q) :
    ∃ Q' : List V, ∃ hQ' : IsHamPath G Q', (RGraph G).Reachable (cls _ hQ) (cls _ hQ') ∧
      IsCyclic G Q' := by
  rcases Nat.eq_zero_or_pos Q.length with h0 | h0
  · refine ⟨Q, hQ, by rfl, ?_⟩
    rw [length_eq_zero_iff.1 h0]; simp [IsCyclic]
  by_cases hc : G.Adj (Q[Q.length - 1]'(by omega)) (Q[0]'h0)
  · exact ⟨Q, hQ, by rfl, isCyclic_of_getElem h0 hc⟩
  · have hab : ¬ G.Adj (Q[0]'h0) (Q[Q.length - 1]'(by omega)) := fun h => hc (G.adj_symm h)
    have hA := factA G hQ h0 hab
    have h1 := hdeg (Q[0]'h0)
    have h2 := hdeg (Q[Q.length - 1]'(by omega))
    obtain ⟨c, hcm⟩ : (crossings G Q (Q[0]'h0) (Q[Q.length - 1]'(by omega))).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hs, hH, hcyc⟩ := crossing_front G hQ h0 hab hcm
    exact ⟨_, hH, reachable_of_step hQ (Or.inl hs), hcyc⟩

/-- Step 2: a cyclic Hamiltonian path of `G` is joined to one starting at `v`. -/
theorem reach_start_v (v : V) {Q : List V} (hQ : IsHamPath G Q) (hcyc : IsCyclic G Q)
    (h3 : 3 ≤ Q.length) :
    ∃ s : List V, ∃ hs : IsHamPath G (v :: s), (RGraph G).Reachable (cls _ hQ) (cls _ hs) ∧
      IsCyclic G (v :: s) := by
  have hv : v ∈ Q := mem_of_isOrdering hQ.1 hQ.2.1 v
  set k := Q.idxOf v
  have hk : k < Q.length := idxOf_lt_length_iff.2 hv
  have hdrop : Q.drop k = v :: Q.drop (k + 1) := by
    rw [drop_eq_getElem_cons hk]; congr 1; exact getElem_idxOf hk
  obtain ⟨h', r, c⟩ := reachable_rotate (x := Q.take k) (y := Q.drop k)
    (by rw [take_append_drop]; exact hQ) (by rw [take_append_drop]; exact h3)
    (by rw [take_append_drop]; exact hcyc)
  rw [hdrop] at h' c
  refine ⟨_, h', ?_, c⟩
  convert r using 2
  · simp [take_append_drop]
  · rw [hdrop]; rfl

/-- **Every path reaches `𝒦`.** Every Hamiltonian path of `G` is joined in `R(G)` to a lift of a
Hamiltonian path of `H`. -/
theorem reach_lift {v : V}
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card)
    (hdegv : Fintype.card V + 3 ≤ 2 * G.degree v) {Q : List V} (hQ : IsHamPath G Q) :
    ∃ P m, ∃ (hP : IsHamH G v P) (hm : Elig G v P m),
      (RGraph G).Reachable (cls _ hQ) (cls _ (isHamPath_liftAt hP hm)) := by
  have hdeg : ∀ x, Fintype.card V + 3 ≤ 2 * G.degree x := by
    intro x
    by_cases hx : x = v
    · subst hx; exact hdegv
    · have := hdegH x hx
      have := Finset.card_erase_le (s := G.neighborFinset x) (a := v)
      rw [card_neighborFinset_eq_degree] at this
      omega
  have hcard : 5 ≤ Fintype.card V := by
    have := hdeg v
    have := G.degree_lt_card_verts v
    omega
  -- step 1
  obtain ⟨Q₁, hQ₁, r₁, c₁⟩ := reach_cyclic hdeg hQ
  -- step 2
  obtain ⟨s, hs, r₂, c₂⟩ := reach_start_v v hQ₁ c₁ (by rw [hQ₁.2.1]; omega)
  have hsH := isHamH_of_cons hs
  have hslen : s.length + 1 = Fintype.card V := hsH.2.2.1
  have hs0 : 0 < s.length := by omega
  have hvs0 : G.Adj v (s[0]'hs0) := by
    obtain ⟨s0, s', rfl⟩ := exists_cons_of_ne_nil (ne_nil_of_length_pos hs0)
    exact (isChain_cons_cons.1 hs.2.2).1
  have hvsl : G.Adj (s[s.length - 1]'(by omega)) v := by
    have := (isCyclic_iff_getElem (m := v :: s) (by simp)).1 c₂
    simp only [length_cons, Nat.add_sub_cancel, getElem_cons_zero] at this
    rwa [getElem_cons_length v s hs0] at this
  -- step 3: make `s` cyclic, keeping `v` and `s[0]` fixed
  obtain ⟨s', hs', r₃, hs'H, c₃⟩ : ∃ s' : List V, ∃ hs' : IsHamPath G (v :: s'),
      (RGraph G).Reachable (cls _ hs) (cls _ hs') ∧ IsHamH G v s' ∧ IsCyclic G s' := by
    by_cases hc : G.Adj (s[s.length - 1]'(by omega)) (s[0]'hs0)
    · exact ⟨s, hs, by rfl, hsH, isCyclic_of_getElem hs0 hc⟩
    · have hab : ¬ G.Adj (s[0]'hs0) (s[s.length - 1]'(by omega)) := fun h => hc (G.adj_symm h)
      have h3 := three_le_crossings_H hsH hs0 hdegH
      obtain ⟨c, hcm⟩ : (crossings G s (s[0]'hs0) (s[s.length - 1]'(by omega))).Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨hb1, hb3⟩ := crossings_bounds G hsH.1 hs0 hab hcm
      have hcm' := hcm
      simp only [crossings, Finset.mem_filter, Finset.mem_range] at hcm'
      obtain ⟨_, hj, ha, hb⟩ := hcm'
      have hstep : BBStep G (v :: s) (v :: bbBack s c) := by
        refine Or.inr ⟨c + 1, by simp; omega, ?_, by simp [bbBack]⟩
        simp only [length_cons, Nat.add_sub_cancel, getElem_cons_succ]
        rw [getElem_cons_length v s hs0]; exact hb
      have hsH' : IsHamH G v (bbBack s c) :=
        isHamH_of_step hsH (Or.inr ⟨c, by omega, by simpa using hb, rfl⟩)
      refine ⟨_, isHamPath_of_step hs hstep, reachable_of_step hs hstep, hsH', ?_⟩
      have hl' : (bbBack s c).length = s.length := (bbBack_perm s c).length_eq
      apply isCyclic_of_getElem (by omega)
      have e1 : (bbBack s c)[0]'(by omega) = s[0] := by
        simp only [bbBack]; rw [getElem_append_left (by simp; omega)]; simp
      have e2 : (bbBack s c)[(bbBack s c).length - 1]'(by omega) = s[c + 1] := by
        simp only [bbBack]
        rw [getElem_append_right (by simp; omega)]
        simp only [getElem_reverse, getElem_drop]
        congr 1; simp; omega
      rw [e1, e2]; exact G.adj_symm ha
  -- steps 4-5
  obtain ⟨i₁, _, _, he₁, _⟩ := exists_two_elig hs'H hdegv
  obtain ⟨P, m, hP, hm, r₄⟩ := reach_lift_of_attach hs' hs'H c₃ he₁
  exact ⟨P, m, hP, hm, r₁.trans (r₂.trans (r₃.trans r₄))⟩

end Kazazi
