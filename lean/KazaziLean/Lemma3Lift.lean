import KazaziLean.Lemma3Parts

/-!
# Lifts (step (b) of Lemma 3)

`liftAt v P i` inserts `v` into the edge `P[i] P[i+1]` of a path `P` of `H = G - v`
(a Hamiltonian path of `H` is represented by a list of vertices of `G` avoiding `v`).
-/
open List SimpleGraph
namespace Kazazi
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Inserting `v` into the edge `P[i] P[i+1]`. -/
def liftAt (v : V) (P : List V) (i : ℕ) : List V := P.take (i + 1) ++ v :: P.drop (i + 1)

theorem liftAt_append_left (v : V) (T D : List V) {i : ℕ} (hi : i + 1 ≤ T.length) :
    liftAt v (T ++ D) i = liftAt v T i ++ D := by
  simp [liftAt, take_append_of_le_length hi, drop_append_of_le_length hi]

theorem liftAt_append_right (v : V) (T D : List V) {i : ℕ} (hi : T.length ≤ i) :
    liftAt v (T ++ D) i = T ++ liftAt v D (i - T.length) := by
  simp only [liftAt, take_append, drop_append, take_of_length_le (show T.length ≤ i + 1 by omega),
    drop_eq_nil_of_le (show T.length ≤ i + 1 by omega), nil_append, append_assoc]
  rw [show i + 1 - T.length = i - T.length + 1 by omega]

theorem liftAt_reverse (v : V) (T : List V) {i : ℕ} (hi : i + 1 < T.length) :
    (liftAt v T i).reverse = liftAt v T.reverse (T.length - 2 - i) := by
  simp only [liftAt, reverse_append, reverse_cons, take_reverse, drop_reverse, append_assoc,
    singleton_append]
  rw [show T.length - (T.length - 2 - i + 1) = i + 1 by omega]

theorem length_liftAt (v : V) (P : List V) {i : ℕ} (hi : i + 1 < P.length) :
    (liftAt v P i).length = P.length + 1 := by
  simp [liftAt]; omega

/-- Suffix case of step (b). -/
theorem bbFront_liftAt_suffix (v : V) (P : List V) {i j : ℕ} (hij : j ≤ i) (hi : i + 1 < P.length) :
    bbFront (liftAt v P i) j = liftAt v (bbFront P j) i := by
  have hT : (P.take j).length = j := by simp; omega
  conv_lhs => rw [← take_append_drop j P, liftAt_append_right v _ _ (by omega), bbFront,
    take_left' (by simp; omega), drop_left' (by simp; omega)]
  rw [bbFront, liftAt_append_right v _ _ (by simp; omega)]
  simp [hT]

/-- Prefix case of step (b). -/
theorem bbFront_liftAt_prefix (v : V) (P : List V) {i j : ℕ} (hij : i + 2 ≤ j) (hj : j < P.length) :
    bbFront (liftAt v P i) (j + 1) = liftAt v (bbFront P j) (j - 2 - i) := by
  have hT : (P.take j).length = j := by simp; omega
  conv_lhs => rw [← take_append_drop j P, liftAt_append_left v _ _ (by omega), bbFront,
    take_left' (by rw [length_liftAt v _ (by omega), hT]), drop_left' (by rw [length_liftAt v _ (by omega), hT])]
  rw [liftAt_reverse v _ (by omega), bbFront, liftAt_append_left v _ _ (by simp; omega), hT]

theorem getElem_liftAt_le (v : V) (P : List V) {i k : ℕ} (hk : k ≤ i) (hi : i + 1 < P.length) :
    (liftAt v P i)[k]'(by rw [length_liftAt v P hi]; omega) = P[k] := by
  simp only [liftAt]
  rw [getElem_append_left (by simp; omega)]; simp

theorem getElem_liftAt_succ (v : V) (P : List V) {i : ℕ} (hi : i + 1 < P.length) :
    (liftAt v P i)[i + 1]'(by rw [length_liftAt v P hi]; omega) = v := by
  simp only [liftAt]
  rw [getElem_append_right (by simp)]
  simp [Nat.min_eq_left (show i + 1 ≤ P.length by omega)]

theorem getElem_liftAt_gt (v : V) (P : List V) {i k : ℕ} (hk : i + 1 ≤ k) (hkP : k < P.length) :
    (liftAt v P i)[k + 1]'(by simp [liftAt]; omega) = P[k] := by
  simp only [liftAt]
  rw [getElem_append_right (by simp; omega)]
  simp [Nat.min_eq_left (show i + 1 ≤ P.length by omega)]
  rw [getElem_cons, dif_neg (by omega), getElem_drop]
  congr 1; omega


theorem bbFront_getElem_lt (l : List V) {j k : ℕ} (hk : k < j) (hj : j ≤ l.length) :
    (bbFront l j)[k]'(by rw [(bbFront_perm l j).length_eq]; omega) = l[j - 1 - k] := by
  simp only [bbFront]
  rw [getElem_append_left (by simp; omega)]
  simp [Nat.min_eq_left hj]

/-- A Hamiltonian path of `H = G - v`, as a list of vertices of `G`. -/
def IsHamH (G : SimpleGraph V) (v : V) (P : List V) : Prop :=
  P.Nodup ∧ v ∉ P ∧ P.length + 1 = Fintype.card V ∧ P.IsChain G.Adj

/-- `P[i] P[i+1]` is an eligible edge: both ends are neighbours of `v`. -/
def Elig (G : SimpleGraph V) (v : V) (P : List V) (i : ℕ) : Prop :=
  ∃ hi : i + 1 < P.length, G.Adj v P[i] ∧ G.Adj v P[i + 1]

theorem isHamPath_liftAt {v : V} {P : List V} (hP : IsHamH G v P) {i : ℕ} (he : Elig G v P i) :
    IsHamPath G (liftAt v P i) := by
  obtain ⟨hi, h1, h2⟩ := he
  obtain ⟨hn, hv, hlen, hc⟩ := hP
  have hperm : liftAt v P i ~ v :: P := by
    unfold liftAt
    calc P.take (i + 1) ++ v :: P.drop (i + 1) ~ v :: (P.take (i + 1) ++ P.drop (i + 1)) :=
          perm_middle
      _ = v :: P := by rw [take_append_drop]
  refine ⟨hperm.nodup_iff.2 (nodup_cons.2 ⟨hv, hn⟩), by rw [hperm.length_eq]; simpa using hlen, ?_⟩
  have hc' := hc
  rw [← take_append_drop (i + 1) P] at hc'
  unfold liftAt
  refine IsChain.append hc'.left_of_append ?_ ?_
  · refine isChain_cons.2 ⟨?_, hc'.right_of_append⟩
    intro y hy
    rw [head?_drop, getElem?_eq_getElem hi, Option.mem_def, Option.some.injEq] at hy
    subst hy; exact h2
  · intro x hx y hy
    rw [getLast?_take] at hx
    simp only [show ¬ (i + 1 = 0) by omega, if_false, Nat.add_sub_cancel,
      getElem?_eq_getElem (by omega : i < P.length), Option.some_or, Option.mem_def,
      Option.some.injEq] at hx
    simp only [head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hx hy; exact G.adj_symm h1

/-- **Step (b), front backbites.** A front backbite `P → bbFront P j` (deleting the edge
`P[j-1] P[j]`) and an eligible edge `i ≠ j - 1`: the same backbite applied to the lift
`liftAt v P i` gives a lift of `bbFront P j`. -/
theorem commute_front {v : V} {P : List V} {j : ℕ} (hj : j < P.length) (hj2 : 2 ≤ j)
    (hadj : G.Adj (P[0]'(by omega)) P[j]) {i : ℕ} (he : Elig G v P i) (hij : i + 1 ≠ j) :
    ∃ i', Elig G v (bbFront P j) i' ∧ BBFront G (liftAt v P i) (liftAt v (bbFront P j) i') := by
  obtain ⟨hi, h1, h2⟩ := he
  have hlenQ : (bbFront P j).length = P.length := (bbFront_perm P j).length_eq
  have hlenL : (liftAt v P i).length = P.length + 1 := length_liftAt v P hi
  have e0 : (liftAt v P i)[0]'(by omega) = P[0] := getElem_liftAt_le v P (by omega) hi
  rcases Nat.lt_or_ge i j with hlt | hge
  · -- prefix case
    refine ⟨j - 2 - i, ⟨by omega, ?_, ?_⟩, j + 1, by omega, by omega, ?_, ?_⟩
    · rw [bbFront_getElem_lt P (by omega) hj.le]
      convert h2 using 2; omega
    · rw [bbFront_getElem_lt P (by omega) hj.le]
      convert h1 using 2; omega
    · rw [e0, getElem_liftAt_gt v P (by omega) hj]; exact hadj
    · exact (bbFront_liftAt_prefix v P (i := i) (by omega) hj).symm
  · -- suffix case
    refine ⟨i, ⟨by omega, ?_, ?_⟩, j, by omega, hj2, ?_, ?_⟩
    · rw [bbFront_getElem P hge (by omega)]; exact h1
    · rw [bbFront_getElem P (by omega) hi]; exact h2
    · rw [e0, getElem_liftAt_le v P hge hi]; exact hadj
    · exact (bbFront_liftAt_suffix v P hge hi).symm

theorem elig_reverse {v : V} {P : List V} {i : ℕ} (he : Elig G v P i) :
    Elig G v P.reverse (P.length - 2 - i) := by
  obtain ⟨hi, h1, h2⟩ := he
  refine ⟨by simp; omega, ?_, ?_⟩
  · rw [getElem_reverse]; convert h2 using 2; omega
  · rw [getElem_reverse]; convert h1 using 2; omega

/-- **Step (b), back backbites.** -/
theorem commute_back {v : V} {P : List V} {j : ℕ} (hj : j + 2 < P.length)
    (hadj : G.Adj (P[P.length - 1]'(by omega)) (P[j]'(by omega))) {i : ℕ} (he : Elig G v P i)
    (hij : i ≠ j) :
    ∃ i', Elig G v (bbBack P j) i' ∧ BBBack G (liftAt v P i) (liftAt v (bbBack P j) i') := by
  have hi := he.1
  have hR : bbFront P.reverse (P.length - 1 - j) = (bbBack P j).reverse := by
    rw [bbBack_eq P (by omega), reverse_reverse]
  have hadj' : G.Adj (P.reverse[0]'(by simp; omega)) (P.reverse[P.length - 1 - j]'(by simp; omega)) := by
    simp only [getElem_reverse]; convert hadj using 2; omega
  obtain ⟨i'', he'', hbb⟩ := commute_front (by simp; omega) (by omega) hadj' (elig_reverse he)
    (by omega)
  rw [hR] at he'' hbb
  have hQlen : (bbBack P j).length = P.length := (bbBack_perm P j).length_eq
  have e1 : liftAt v P.reverse (P.length - 2 - i) = (liftAt v P i).reverse :=
    (liftAt_reverse v P hi).symm
  have hi'' := he''.1
  have e2 : liftAt v (bbBack P j).reverse i'' =
      (liftAt v (bbBack P j) ((bbBack P j).length - 2 - i'')).reverse := by
    simp only [length_reverse] at hi''
    rw [liftAt_reverse v _ (by omega)]
    congr 1; omega
  rw [e1, e2] at hbb
  refine ⟨(bbBack P j).length - 2 - i'', ?_, bbBack_iff_front_reverse.2 hbb⟩
  have := elig_reverse he''
  simp only [reverse_reverse, length_reverse] at this
  exact this

end Kazazi
