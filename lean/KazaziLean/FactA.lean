import KazaziLean.Lemmas

/-!
# Fact A (crossings), §1 of the paper

Let `P = w₁ ⋯ w_h` be a Hamiltonian path of a graph `F` on `h` vertices whose endpoints
`a = w₁`, `b = w_h` are non-adjacent. Then there are at least `d(a) + d(b) - (h-1)` indices
`i` with `a w_{i+1}, b w_i ∈ E(F)`.

Lean indices are 0-based: the paper's index `i ∈ {1,…,h-1}` is `i+1` for our `i ∈ range (h-1)`,
and `w_{i+1}, w_i` are `l[i+1], l[i]`.
-/

set_option linter.unusedSectionVars false

namespace Kazazi

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_of_isOrdering {l : List V} (hn : l.Nodup) (hlen : l.length = Fintype.card V) (x : V) :
    x ∈ l := by
  have : l.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hn, hlen]
  rw [← List.mem_toFinset, this]; exact Finset.mem_univ x

/-- Counting positions of an ordering, shifted by `c ≤ 1`. -/
theorem card_filter_shift {l : List V} (hn : l.Nodup) (hlen : l.length = Fintype.card V)
    (P : V → Prop) [DecidablePred P] (c : ℕ) (hex : ∀ k (hk : k < l.length), P l[k] →
      c ≤ k ∧ k < l.length - 1 + c) :
    ((range (l.length - 1)).filter (fun i => ∃ h : i + c < l.length, P l[i + c])).card =
      (univ.filter P).card := by
  refine Finset.card_bij (fun i hi => l[i + c]'(by
      simp only [mem_filter] at hi; exact hi.2.1)) ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter] at hi
    obtain ⟨_, h, hp⟩ := hi
    simpa using hp
  · intro i hi j hj e
    simp only [mem_filter] at hi hj
    have := (hn.getElem_inj_iff).1 e
    omega
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 (mem_of_isOrdering hn hlen x)
    obtain ⟨h1, h2⟩ := hex k hk hx
    refine ⟨k - c, ?_, ?_⟩
    · simp only [mem_filter, mem_range]
      refine ⟨by omega, by omega, ?_⟩
      simpa [show k - c + c = k by omega] using hx
    · simp [show k - c + c = k by omega]

theorem isCyclic_of_getElem {G : SimpleGraph V} {m : List V} (hm : 0 < m.length)
    (h : G.Adj (m[m.length - 1]'(by omega)) (m[0]'hm)) : IsCyclic G m := by
  intro z hz y hy
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.mem_def,
    Option.some.injEq] at hz
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hm, Option.mem_def,
    Option.some.injEq] at hy
  subst hz hy; exact h

theorem isCyclic_iff_getElem {G : SimpleGraph V} {m : List V} (hm : 0 < m.length) :
    IsCyclic G m ↔ G.Adj (m[m.length - 1]'(by omega)) (m[0]'hm) := by
  refine ⟨fun h => h _ ?_ _ ?_, isCyclic_of_getElem hm⟩
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hm]; rfl

theorem bbFront_getElem_zero (l : List V) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ l.length) :
    (bbFront l j)[0]'(by rw [(bbFront_perm l j).length_eq]; omega) = l[j - 1] := by
  simp only [bbFront]
  rw [List.getElem_append_left (by simp; omega)]
  simp [Nat.min_eq_left hj]

theorem bbFront_getElem (l : List V) {j k : ℕ} (hjk : j ≤ k) (hk : k < l.length) :
    (bbFront l j)[k]'(by rw [(bbFront_perm l j).length_eq]; omega) = l[k] := by
  simp only [bbFront]
  rw [List.getElem_append_right (by simp; omega)]
  simp [Nat.min_eq_left (show j ≤ l.length by omega)]
  congr 1; omega

theorem bbFront_getElem_last (l : List V) {j : ℕ} (hj : j < l.length) :
    (bbFront l j)[(bbFront l j).length - 1]'(by rw [(bbFront_perm l j).length_eq]; omega) =
      l[l.length - 1] := by
  have e : (bbFront l j).length = l.length := (bbFront_perm l j).length_eq
  simp only [e]
  exact bbFront_getElem l (by omega) (by omega)

/-- The set of crossing indices of Fact A (0-based). -/
def crossings (F : SimpleGraph V) [DecidableRel F.Adj] (l : List V) (a b : V) : Finset ℕ :=
  (range (l.length - 1)).filter (fun i => ∃ h : i + 1 < l.length, F.Adj a l[i + 1] ∧ F.Adj b l[i])

/-- **Fact A (crossings).** For a Hamiltonian path `l = w₁ ⋯ w_h` of `F` with non-adjacent
endpoints `a = w₁`, `b = w_h`, the number of indices `i` with `a w_{i+1}, b w_i ∈ E(F)` is at
least `d_F(a) + d_F(b) - (h - 1)` (stated without truncated subtraction). -/
theorem factA (F : SimpleGraph V) [DecidableRel F.Adj] {l : List V} (hl : IsHamPath F l)
    (h0 : 0 < l.length) (hab : ¬ F.Adj (l[0]'h0) (l[l.length - 1]'(by omega))) :
    F.degree (l[0]'h0) + F.degree (l[l.length - 1]'(by omega)) ≤
      (crossings F l (l[0]'h0) (l[l.length - 1]'(by omega))).card + (Fintype.card V - 1) := by
  set a := l[0]'h0
  set b := l[l.length - 1]'(by omega)
  obtain ⟨hn, hlen, _⟩ := hl
  set S := (range (l.length - 1)).filter (fun i => ∃ h : i + 1 < l.length, F.Adj a l[i + 1])
  set T := (range (l.length - 1)).filter (fun i => ∃ h : i + 0 < l.length, F.Adj b l[i + 0])
  have hS : S.card = F.degree a := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    refine card_filter_shift hn hlen (F.Adj a) 1 ?_
    intro k hk hp
    refine ⟨?_, by omega⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd hp F.irrefl
    · exact hk0
  have hT : T.card = F.degree b := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    refine card_filter_shift hn hlen (F.Adj b) 0 ?_
    intro k hk hp
    refine ⟨by omega, ?_⟩
    by_contra hc
    have : k = l.length - 1 := by omega
    subst this
    exact F.irrefl hp
  have hU : (S ∪ T).card ≤ l.length - 1 := by
    calc (S ∪ T).card ≤ (range (l.length - 1)).card :=
          card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
      _ = l.length - 1 := card_range _
  have hI : (S ∩ T).card ≤ (crossings F l a b).card := by
    apply card_le_card
    intro i hi
    simp only [S, T, mem_inter, mem_filter, crossings, Nat.add_zero] at hi ⊢
    obtain ⟨⟨hr, h1, ha⟩, _, _, hb⟩ := hi
    exact ⟨hr, h1, ha, hb⟩
  have := card_union_add_card_inter S T
  rw [← hlen]
  omega

/-- The crossing indices avoid the ends: `2 ≤ i ≤ h-2` in the paper's 1-based indexing,
i.e. `1 ≤ i ≤ h - 3` here. -/
theorem crossings_bounds (F : SimpleGraph V) [DecidableRel F.Adj] {l : List V} (hl : l.Nodup) (h0 : 0 < l.length)
    (hab : ¬ F.Adj (l[0]'h0) (l[l.length - 1]'(by omega))) {i : ℕ}
    (hi : i ∈ crossings F l (l[0]'h0) (l[l.length - 1]'(by omega))) :
    1 ≤ i ∧ i + 3 ≤ l.length := by
  simp only [crossings, mem_filter, mem_range] at hi
  obtain ⟨hr, h1, ha, hb⟩ := hi
  constructor
  · rcases Nat.eq_zero_or_pos i with rfl | h
    · exact absurd (F.adj_symm hb) (by simpa using hab)
    · exact h
  · by_contra hc
    have : i + 1 = l.length - 1 := by omega
    have e : l[i + 1] = l[l.length - 1] := by simp only [this]
    rw [e] at ha; exact hab ha

/-- The backbite `bb(a, w_{i+1})` at a crossing index yields a Hamiltonian path whose endpoints
`w_i, b` are adjacent. -/
theorem crossing_front (F : SimpleGraph V) [DecidableRel F.Adj] {l : List V} (hl : IsHamPath F l)
    (h0 : 0 < l.length) (hab : ¬ F.Adj (l[0]'h0) (l[l.length - 1]'(by omega))) {i : ℕ}
    (hi : i ∈ crossings F l (l[0]'h0) (l[l.length - 1]'(by omega))) :
    BBFront F l (bbFront l (i + 1)) ∧ IsHamPath F (bbFront l (i + 1)) ∧
      IsCyclic F (bbFront l (i + 1)) := by
  obtain ⟨hi1, hi3⟩ := crossings_bounds F hl.1 h0 hab hi
  simp only [crossings, mem_filter, mem_range] at hi
  obtain ⟨_, h1, ha, hb⟩ := hi
  refine ⟨⟨i + 1, h1, by omega, ha, rfl⟩, isHamPath_bbFront hl h1 ha, ?_⟩
  have hlen : (bbFront l (i + 1)).length = l.length := (bbFront_perm l _).length_eq
  apply isCyclic_of_getElem (by omega)
  rw [bbFront_getElem_zero l (by omega) (by omega), bbFront_getElem_last l (by omega)]
  simpa using hb

/-- Indices `i` such that both ends of the edge `P[i] P[i+1]` lie in `N` ("eligible" edges). -/
def eligible (P : List V) (N : Finset V) : Finset ℕ :=
  (range (P.length - 1)).filter (fun i => ∃ h : i + 1 < P.length, P[i] ∈ N ∧ P[i + 1] ∈ N)

theorem card_shift_ge (P : List V) (N : Finset V) (hN : ∀ x ∈ N, x ∈ P) (c : ℕ) (hc : c ≤ 1) :
    N.card ≤ ((range (P.length - 1)).filter (fun i => ∃ h : i + c < P.length, P[i + c] ∈ N)).card + 1 := by
  set S := (range (P.length - 1)).filter (fun i => ∃ h : i + c < P.length, P[i + c] ∈ N)
  rcases Nat.eq_zero_or_pos P.length with h0 | h0
  · have : N = ∅ := by
      ext x; simp only [Finset.notMem_empty, iff_false]
      intro hx; have := hN x hx; rw [List.length_eq_zero_iff.1 h0] at this; simp at this
    simp [this]
  -- the excluded position: `P.length - 1` if `c = 0`, `0` if `c = 1`
  set e := (if c = 0 then P.length - 1 else 0) with he
  have hsub : N ⊆ insert (P[e]'(by rw [he]; split_ifs <;> omega))
      (S.attach.image (fun i => P[i.1 + c]'(by
        have := i.2; simp only [S, mem_filter] at this; exact this.2.1))) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 (hN x hx)
    by_cases hke : k = e
    · subst hke; exact mem_insert_self _ _
    · refine mem_insert_of_mem (mem_image.2 ⟨⟨k - c, ?_⟩, mem_attach _ _, ?_⟩)
      · simp only [S, mem_filter, mem_range]
        refine ⟨by split_ifs at he <;> omega, by split_ifs at he <;> omega, ?_⟩
        simpa [show k - c + c = k by split_ifs at he <;> omega] using hx
      · simp only
        congr 1; split_ifs at he <;> omega
  calc N.card ≤ _ := card_le_card hsub
    _ ≤ _ := card_insert_le _ _
    _ ≤ S.attach.card + 1 := by gcongr; exact card_image_le
    _ = S.card + 1 := by rw [card_attach]

/-- **Eligible edges.** If all of `N` lies on the list `P`, at least `2|N| - |P| - 1` edges
`P[i] P[i+1]` have both ends in `N` (the paper's count `d - (h - d + 1) = 2d - h - 1`). -/
theorem eligible_card (P : List V) (N : Finset V) (hN : ∀ x ∈ N, x ∈ P) :
    2 * N.card ≤ (eligible P N).card + P.length + 1 := by
  set S0 := (range (P.length - 1)).filter (fun i => ∃ h : i + 0 < P.length, P[i + 0] ∈ N)
  set S1 := (range (P.length - 1)).filter (fun i => ∃ h : i + 1 < P.length, P[i + 1] ∈ N)
  have h0 : N.card ≤ S0.card + 1 := card_shift_ge P N hN 0 (by omega)
  have h1 : N.card ≤ S1.card + 1 := card_shift_ge P N hN 1 le_rfl
  have hU : (S0 ∪ S1).card ≤ P.length - 1 := by
    calc (S0 ∪ S1).card ≤ (range (P.length - 1)).card :=
          card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
      _ = P.length - 1 := card_range _
  have hI : (S0 ∩ S1).card ≤ (eligible P N).card := by
    apply card_le_card
    intro i hi
    simp only [S0, S1, mem_inter, mem_filter, eligible, Nat.add_zero] at hi ⊢
    obtain ⟨⟨hr, _, ha⟩, _, h1, hb⟩ := hi
    exact ⟨hr, h1, ha, hb⟩
  have := card_union_add_card_inter S0 S1
  have hL : N.card = 0 ∨ 1 ≤ P.length := by
    rcases Nat.eq_zero_or_pos P.length with h | h
    · left; rw [Finset.card_eq_zero]; ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx; have := hN x hx; rw [List.length_eq_zero_iff.1 h] at this; simp at this
    · right; exact h
  omega


end Kazazi
