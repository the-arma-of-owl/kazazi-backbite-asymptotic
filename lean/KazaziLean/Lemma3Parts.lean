import KazaziLean.FactA

/-!
# Sub-claims of Lemma 3 (vertex extension), §3 of the paper

Attachment moves of the proof of Lemma 3, at the level of vertex lists in `G` (the added
vertex is an arbitrary `v : V`). Lemma 3 itself is `Kazazi.lemma3` in `Lemma3.lean`.

* `attach_flip`  — "Same attachment point, other direction".
* `attach_move`  — "Moving to another attachment point `c ≠ a`" (`c ≠ b`).
* `attach_move_last` — "The case `c = b`".
* `lift_front_suffix`, `lift_front_prefix` — the list identities behind step (b):
  a front backbite commutes with inserting `v` into a retained edge, whether that edge lies
  in the kept suffix or in the reversed prefix.
* `five_crossings` — the arithmetic giving "at least 5 crossing indices" from Fact A
  (for a graph on all of `V`; not used by `lemma3`, which uses `three_le_crossings_H`).
* `attach_rotate`, `attach_rotate'`, `attach_flip'`, `attachments_connected` —
  "All attachments to `D` lie in one component of `R(G)`".
-/

set_option linter.unusedSectionVars false

namespace Kazazi

open List SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Attachment, same point, other direction.** In the attachment `(v, a, X, b)` (where the
part `a, X, b` traverses a Hamiltonian cycle `D` of `H` omitting the edge `ab`), the backbite
from `b` with target `a` gives the attachment `(v, a, b, Xᴿ)` at `a` in the other direction. -/
theorem attach_flip {v a b : V} {X : List V} (hl : IsHamPath G (v :: a :: (X ++ [b])))
    (hab : G.Adj b a) :
    ∃ h' : IsHamPath G (v :: a :: b :: X.reverse),
      (RGraph G).Reachable (cls _ hl) (cls _ h') := by
  cases X with
  | nil => exact ⟨by simpa using hl, by simp⟩
  | cons x X' =>
    have hstep : BBStep G (v :: a :: (x :: X' ++ [b])) (v :: a :: b :: (x :: X').reverse) := by
      refine Or.inr ⟨1, by simp, by simpa using hab, by simp [bbBack]⟩
    exact ⟨isHamPath_of_step hl hstep, reachable_of_step hl hstep⟩

/-- **Attachment, moving to another attachment point `c ≠ a, b`.** Writing the attachment at
`a` as `(v, a, A, c, B, b)`, the backbite from `v` with target `c` gives `(Aᴿ, a, v, c, B, b)`;
then the backbite from `b` with target `a` gives (the reversal of) `(v, c, B, b, a, A)`. -/
theorem attach_move {v a b c : V} {A B : List V}
    (hl : IsHamPath G ((v :: a :: A) ++ (c :: (B ++ [b])))) (hvc : G.Adj v c) (hab : G.Adj b a) :
    ∃ h' : IsHamPath G (v :: c :: (B ++ b :: a :: A)),
      (RGraph G).Reachable (cls _ hl) (cls _ h') := by
  have hlen : (v :: a :: A).length = A.length + 2 := by simp
  -- first backbite: from `v` with target `c`
  have hs1 : BBStep G ((v :: a :: A) ++ (c :: (B ++ [b])))
      ((A.reverse ++ [a, v]) ++ (c :: (B ++ [b]))) := by
    refine Or.inl ⟨A.length + 2, by simp, by omega, by simpa using hvc, ?_⟩
    rw [bbFront, take_left' hlen, drop_left' hlen]; simp
  have h1 := isHamPath_of_step hl hs1
  -- second backbite: from `b` with target `a`
  have hlen2 : (A.reverse ++ [a]).length = A.length + 1 := by simp
  have hs2 : BBStep G ((A.reverse ++ [a, v]) ++ (c :: (B ++ [b])))
      (v :: c :: (B ++ b :: a :: A)).reverse := by
    refine Or.inr ⟨A.length, by simp, by simpa using hab, ?_⟩
    have e : (A.reverse ++ [a, v]) ++ (c :: (B ++ [b])) =
        (A.reverse ++ [a]) ++ (v :: c :: (B ++ [b])) := by simp
    rw [e, bbBack, take_left' hlen2, drop_left' hlen2]
    simp
  have h2 := isHamPath_of_step h1 hs2
  have h3 : IsHamPath G (v :: c :: (B ++ b :: a :: A)) := by
    simpa using isHamPath_reverse h2
  refine ⟨h3, ?_⟩
  have r := (reachable_of_step hl hs1).trans (reachable_of_step h1 hs2)
  rwa [cls_reverse h3] at r

/-- **Attachment, the case `c = b`.** The same two moves turn `(v, a, A, b)` into
`(Aᴿ, a, v, b)` and then into (the reversal of) `(v, b, a, A)`. -/
theorem attach_move_last {v a b : V} {A : List V}
    (hl : IsHamPath G ((v :: a :: A) ++ [b])) (hvb : G.Adj v b) (hab : G.Adj b a) :
    ∃ h' : IsHamPath G (v :: b :: a :: A), (RGraph G).Reachable (cls _ hl) (cls _ h') := by
  have hlen : (v :: a :: A).length = A.length + 2 := by simp
  have hs1 : BBStep G ((v :: a :: A) ++ [b]) ((A.reverse ++ [a, v]) ++ [b]) := by
    refine Or.inl ⟨A.length + 2, by simp, by omega, by simpa using hvb, ?_⟩
    rw [bbFront, take_left' hlen, drop_left' hlen]; simp
  have h1 := isHamPath_of_step hl hs1
  have hlen2 : (A.reverse ++ [a]).length = A.length + 1 := by simp
  have hs2 : BBStep G ((A.reverse ++ [a, v]) ++ [b]) (v :: b :: a :: A).reverse := by
    refine Or.inr ⟨A.length, by simp, by simpa using hab, ?_⟩
    have e : (A.reverse ++ [a, v]) ++ [b] = (A.reverse ++ [a]) ++ [v, b] := by simp
    rw [e, bbBack, take_left' hlen2, drop_left' hlen2]
    simp
  have h2 := isHamPath_of_step h1 hs2
  have h3 : IsHamPath G (v :: b :: a :: A) := by simpa using isHamPath_reverse h2
  refine ⟨h3, ?_⟩
  have r := (reachable_of_step hl hs1).trans (reachable_of_step h1 hs2)
  rwa [cls_reverse h3] at r

/-- **Step (b), retained edge in the suffix.** If `P = T ++ D` and the front backbite with
target `D[0]` (index `|T|`) is applied, inserting `v` into an edge `xy` of `D` commutes with
the backbite. -/
theorem lift_front_suffix (T D₁ D₂ : List V) (x y v : V) :
    bbFront (T ++ (D₁ ++ x :: v :: y :: D₂)) T.length =
      T.reverse ++ (D₁ ++ x :: v :: y :: D₂) ∧
    bbFront (T ++ (D₁ ++ x :: y :: D₂)) T.length = T.reverse ++ (D₁ ++ x :: y :: D₂) := by
  constructor <;> rw [bbFront, take_left' rfl, drop_left' rfl]

/-- **Step (b), retained edge in the reversed prefix.** If the eligible edge `xy` lies in the
reversed prefix `T = T₁ ++ x :: y :: T₂`, then after inserting `v` the same backbite (now with
index `|T| + 1`, the target being unchanged) yields the backbite result with `v` still between
`x` and `y`. -/
theorem lift_front_prefix (T₁ T₂ D : List V) (x y v : V) :
    bbFront ((T₁ ++ x :: v :: y :: T₂) ++ D) ((T₁ ++ x :: y :: T₂).length + 1) =
      (T₂.reverse ++ y :: v :: x :: T₁.reverse) ++ D ∧
    bbFront ((T₁ ++ x :: y :: T₂) ++ D) (T₁ ++ x :: y :: T₂).length =
      (T₂.reverse ++ y :: x :: T₁.reverse) ++ D := by
  constructor
  · have h : (T₁ ++ x :: v :: y :: T₂).length = (T₁ ++ x :: y :: T₂).length + 1 := by
      simp; omega
    rw [bbFront, take_left' h, drop_left' h]; simp
  · rw [bbFront, take_left' rfl, drop_left' rfl]; simp

/-- The arithmetic of "By Fact A in `H` there are at least 5 crossing indices": if both
endpoints have degree at least `h/2 + 2` (written `2·d ≥ h + 4`), Fact A gives `≥ 5`. -/
theorem five_crossings (F : SimpleGraph V) [DecidableRel F.Adj] {l : List V} (hl : IsHamPath F l)
    (h0 : 0 < l.length) (hab : ¬ F.Adj (l[0]'h0) (l[l.length - 1]'(by omega)))
    (hdeg : ∀ x, Fintype.card V + 4 ≤ 2 * F.degree x) :
    5 ≤ (crossings F l (l[0]'h0) (l[l.length - 1]'(by omega))).card := by
  have := factA F hl h0 hab
  have h1 := hdeg (l[0]'h0)
  have h2 := hdeg (l[l.length - 1]'(by omega))
  have h3 := hl.2.1
  omega

@[simp] theorem getLast?_cons_append_singleton (a b : V) (l : List V) :
    (a :: (l ++ [b])).getLast? = some b := by
  rw [← cons_append, getLast?_append]; simp

/-- Moving the attachment point along the cycle (same orientation). -/
theorem attach_rotate {v : V} {s : List V} (hl : IsHamPath G (v :: s)) (hcyc : IsCyclic G s)
    {k : ℕ} (hk : 0 < k) (hks : k < s.length) (hv : G.Adj v s[k]) :
    ∃ h' : IsHamPath G (v :: s.rotate k), (RGraph G).Reachable (cls _ hl) (cls _ h') := by
  have hrot : s.rotate k = s.drop k ++ s.take k := rotate_eq_drop_append_take hks.le
  obtain ⟨a, A, hA⟩ : ∃ a A, s.take k = a :: A := by
    rcases h : s.take k with _ | ⟨a, A⟩
    · have := congrArg length h; simp only [length_take, length_nil] at this; omega
    · exact ⟨a, A, rfl⟩
  obtain ⟨c, D, hD⟩ : ∃ c D, s.drop k = c :: D := by
    rcases h : s.drop k with _ | ⟨c, D⟩
    · have := congrArg length h; simp at this; omega
    · exact ⟨c, D, rfl⟩
  have hs : s = (a :: A) ++ (c :: D) := by rw [← hA, ← hD, take_append_drop]
  have hc : s[k] = c := by
    have : (s.drop k)[0]'(by rw [hD]; simp) = c := by simp [hD]
    rw [← this, getElem_drop]; simp
  rw [hc] at hv
  have hlast : ∀ b, s.getLast? = some b → G.Adj b a := by
    intro b hb; exact hcyc b hb a (by rw [hs]; rfl)
  rcases D.eq_nil_or_concat' with rfl | ⟨B, b, rfl⟩
  · -- `c` is the last vertex
    have hl' : IsHamPath G ((v :: a :: A) ++ [c]) := by rw [hs] at hl; simpa using hl
    obtain ⟨h', r⟩ := attach_move_last hl' hv (hlast c (by rw [hs, getLast?_append]; simp))
    refine ⟨by rw [hrot, hA, hD]; simpa using h', ?_⟩
    have e1 : cls (v :: s) hl = cls _ hl' := cls_eq_of_eq _ _ (by rw [hs]; simp)
    rw [e1]; convert r using 2; rw [hrot, hA, hD]; simp
  · have hl' : IsHamPath G ((v :: a :: A) ++ (c :: (B ++ [b]))) := by
      rw [hs] at hl; simpa using hl
    obtain ⟨h', r⟩ := attach_move hl' hv (hlast b (by rw [hs, getLast?_append, ← cons_append, getLast?_append]; simp))
    refine ⟨by rw [hrot, hA, hD]; simpa using h', ?_⟩
    have e1 : cls (v :: s) hl = cls _ hl' := cls_eq_of_eq _ _ (by rw [hs]; simp)
    rw [e1]; convert r using 2; rw [hrot, hA, hD]; simp


/-- All attachments with the same orientation: `v :: s` reaches `v :: s.rotate k` whenever
`v` is adjacent to the new first vertex. -/
theorem attach_rotate' {v : V} {s : List V} (hl : IsHamPath G (v :: s)) (hcyc : IsCyclic G s)
    (k : ℕ) (hs0 : 0 < s.length) (hv : G.Adj v ((s.rotate k)[0]'(by simpa using hs0))) :
    ∃ h' : IsHamPath G (v :: s.rotate k), (RGraph G).Reachable (cls _ hl) (cls _ h') := by
  have hk : k % s.length < s.length := Nat.mod_lt _ hs0
  rcases Nat.eq_zero_or_pos (k % s.length) with h0 | h0
  · rw [← rotate_mod, h0, rotate_zero]; exact ⟨hl, by rfl⟩
  · obtain ⟨h', r⟩ := attach_rotate hl hcyc h0 hk (by simpa [getElem_rotate] using hv)
    rw [rotate_mod] at h'
    refine ⟨h', ?_⟩
    convert r using 2 <;> simp

/-- Reversing the orientation of an attachment (`attach_flip`), phrased with rotations:
`v :: s` reaches `v :: s'` where `s' = sᴿ.rotate (|s| - 1)` starts at `s[0]`; `s'` is cyclic. -/
theorem attach_flip' {v : V} {s : List V} (hl : IsHamPath G (v :: s)) (hcyc : IsCyclic G s)
    (h2 : 2 ≤ s.length) :
    ∃ h' : IsHamPath G (v :: s.reverse.rotate (s.length - 1)),
      (RGraph G).Reachable (cls _ hl) (cls _ h') ∧ IsCyclic G (s.reverse.rotate (s.length - 1)) := by
  obtain ⟨a, X, b, rfl⟩ : ∃ a X b, s = a :: (X ++ [b]) := by
    rcases s with _ | ⟨a, s⟩
    · simp at h2
    · rcases s.eq_nil_or_concat' with rfl | ⟨X, b, rfl⟩
      · simp at h2
      · exact ⟨a, X, b, rfl⟩
  have e : (a :: (X ++ [b])).reverse.rotate ((a :: (X ++ [b])).length - 1) = a :: b :: X.reverse := by
    have hlen : (b :: X.reverse).length = (a :: (X ++ [b])).length - 1 := by simp
    rw [show (a :: (X ++ [b])).reverse = (b :: X.reverse) ++ [a] by simp,
      rotate_eq_drop_append_take (by simp), ← hlen, drop_left' rfl, take_left' rfl]
    simp
  obtain ⟨h', r⟩ := attach_flip (G := G) hl (hcyc b (by simp) a (by simp))
  rw [e]
  refine ⟨h', r, ?_⟩
  intro z hz y hy
  simp only [head?_cons, Option.mem_def, Option.some.injEq] at hy
  subst hy
  rcases X with _ | ⟨x, X⟩
  · simp at hz; subst hz; exact hcyc _ (by simp) _ (by simp)
  · simp only [reverse_cons] at hz
    rw [show a :: b :: (X.reverse ++ [x]) = (a :: b :: X.reverse) ++ [x] from rfl,
      getLast?_append] at hz
    simp at hz
    subst hz
    exact G.adj_symm (isChain_cons_cons.1 (isChain_cons.1 hl.2.2).2).1

/-- **All attachments to `D` lie in one component of `R(G)`.** Here the cycle `D` of `H` is
given by the cyclic list `s`, an attachment is `v :: t` with `t` a rotation of `s` or of `sᴿ`
whose first vertex is adjacent to `v`. -/
theorem attachments_connected {v : V} {s : List V} (hl : IsHamPath G (v :: s))
    (hcyc : IsCyclic G s) (h2 : 2 ≤ s.length) {t : List V}
    (ht : (∃ k, t = s.rotate k) ∨ (∃ k, t = s.reverse.rotate k)) (ht0 : 0 < t.length)
    (hv : G.Adj v (t[0]'ht0)) :
    ∃ h' : IsHamPath G (v :: t), (RGraph G).Reachable (cls _ hl) (cls _ h') := by
  rcases ht with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact attach_rotate' hl hcyc k (by omega) hv
  · obtain ⟨h1, r1, c1⟩ := attach_flip' hl hcyc h2
    have e : s.reverse.rotate k = (s.reverse.rotate (s.length - 1)).rotate (k + 1) := by
      have : s.length - 1 + (k + 1) = k + s.reverse.length := by simp; omega
      conv_rhs => rw [rotate_rotate, this, ← rotate_mod, Nat.add_mod_right, rotate_mod]
    have hl0 : 0 < (s.reverse.rotate (s.length - 1)).length := by simp; omega
    have hv' : G.Adj v (((s.reverse.rotate (s.length - 1)).rotate (k + 1))[0]'(by simpa using hl0)) := by
      simpa [← e] using hv
    obtain ⟨h2', r2⟩ := attach_rotate' h1 c1 (k + 1) hl0 hv'
    refine ⟨by rw [e]; exact h2', r1.trans ?_⟩
    convert r2 using 2 <;> rw [e]


end Kazazi
