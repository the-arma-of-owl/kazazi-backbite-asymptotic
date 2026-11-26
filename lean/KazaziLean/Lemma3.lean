import KazaziLean.Lemma3Reach

/-!
# Lemma 3 (vertex extension), §3 of the paper

**Lemma 3.** Let `H` be a graph on `h` vertices with `δ(H) ≥ h/2 + 2` and `R(H)` connected. Let
`G` be obtained by adding a vertex `v` with `d := |N(v) ∩ V(H)| ≥ h/2 + 2`. Then `R(G)` is
connected.

Formalization: `G` is a graph on `V`, `v : V`, and `H = G.induce {v}ᶜ` (so `G` is `H` plus the
vertex `v`). The inequalities `δ(H) ≥ h/2 + 2`, `d ≥ h/2 + 2` are written `h + 4 ≤ 2·δ`,
`h + 4 ≤ 2·d` with `h = |{v}ᶜ|`. Since `v` is not adjacent to itself, `N(v) ∩ V(H) = N(v)`.
-/

set_option linter.unusedSectionVars false

namespace Kazazi

open List SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem liftsConn_refl {v : V} {P : List V}
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card) :
    LiftsConn G v P P :=
  fun hP _ _ hi _ hj => lifts_same hP hdegH hi hj

/-- List-level core of Lemma 3: if all lifts of all Hamiltonian paths of `H` lie in one
component, then `R(G)` is connected. -/
theorem rConnected_of_liftsConn {v : V}
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card)
    (hdegv : Fintype.card V + 3 ≤ 2 * G.degree v)
    (hconn : ∀ P Q, IsHamH G v P → IsHamH G v Q → LiftsConn G v P Q) : RConnected G := by
  intro X Y
  induction X using Quotient.ind
  induction Y using Quotient.ind
  rename_i p q
  obtain ⟨P, m, hP, hm, r₁⟩ := reach_lift hdegH hdegv p.2
  obtain ⟨Q, n, hQ, hn, r₂⟩ := reach_lift hdegH hdegv q.2
  exact r₁.trans ((hconn P Q hP hQ hP hQ m hm n hn).trans r₂.symm)

/-! ### Bridge between `H = G.induce {v}ᶜ` and lists of vertices of `G` avoiding `v` -/

section Bridge

variable (v : V)

set_option quotPrecheck false in
local notation "W" => ↥({v}ᶜ : Set V)

theorem card_compl_singleton : Fintype.card W = Fintype.card V - 1 := by
  rw [Fintype.card_compl_set]; simp

theorem degree_induce_compl (x : W) :
    (G.induce ({v}ᶜ : Set V)).degree x = ((G.neighborFinset x).erase v).card := by
  rw [← card_neighborFinset_eq_degree, ← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext y
  simp [mem_neighborFinset]
  exact and_comm

theorem isHamH_map {p : List W} (hp : IsHamPath (G.induce ({v}ᶜ : Set V)) p) :
    IsHamH G v (p.map Subtype.val) := by
  obtain ⟨hn, hlen, hc⟩ := hp
  have hcard := card_compl_singleton v
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  refine ⟨hn.map Subtype.val_injective, ?_, by simp; omega, ?_⟩
  · simp
  · rw [isChain_map]; exact hc.imp (fun a b h => by simpa using h)

theorem map_bbFront (p : List W) (j : ℕ) :
    (bbFront p j).map Subtype.val = bbFront (p.map Subtype.val) j := by
  simp [bbFront, map_take, map_drop, map_reverse]

theorem map_bbBack (p : List W) (j : ℕ) :
    (bbBack p j).map Subtype.val = bbBack (p.map Subtype.val) j := by
  simp [bbBack, map_take, map_drop, map_reverse]

theorem bbStep_map {p q : List W} (h : BBStep (G.induce ({v}ᶜ : Set V)) p q) :
    BBStep G (p.map Subtype.val) (q.map Subtype.val) := by
  rcases h with ⟨j, hj, hj2, hadj, rfl⟩ | ⟨j, hj, hadj, rfl⟩
  · refine Or.inl ⟨j, by simpa using hj, hj2, ?_, map_bbFront v p j⟩
    simpa using hadj
  · refine Or.inr ⟨j, by simpa using hj, ?_, map_bbBack v p j⟩
    simpa using hadj

theorem exists_of_isHamH {P : List V} (hP : IsHamH G v P) :
    ∃ p : List W, IsHamPath (G.induce ({v}ᶜ : Set V)) p ∧ p.map Subtype.val = P := by
  have hmem : ∀ x ∈ P, x ∈ ({v}ᶜ : Set V) := fun x hx h => hP.2.1 (h ▸ hx)
  have hmap : (P.pmap Subtype.mk hmem).map Subtype.val = P := by simp [List.map_pmap]
  refine ⟨P.pmap Subtype.mk hmem, ⟨?_, ?_, ?_⟩, hmap⟩
  · exact hP.1.pmap (fun _ _ _ _ h => by simpa using h)
  · have := hP.2.2.1; rw [length_pmap, card_compl_singleton]; omega
  · have h := hP.2.2.2
    rw [← hmap, isChain_map] at h
    exact h.imp (fun a b h => by simpa using h)

theorem stepRep_map {p q : List W} (h : StepRep (G.induce ({v}ᶜ : Set V)) p q) :
    ∃ p' ∈ [p.map Subtype.val, (p.map Subtype.val).reverse],
      ∃ q' ∈ [q.map Subtype.val, (q.map Subtype.val).reverse], BBStep G p' q' := by
  obtain ⟨p', hp', q', hq', hs⟩ := h
  refine ⟨p'.map Subtype.val, ?_, q'.map Subtype.val, ?_, bbStep_map v hs⟩
  · simp only [mem_cons, not_mem_nil, or_false] at hp' ⊢
    rcases hp' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (map_reverse ..)
  · simp only [mem_cons, not_mem_nil, or_false] at hq' ⊢
    rcases hq' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (map_reverse ..)

theorem liftsConn_of_mem {P P' : List V}
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card)
    (h : P' ∈ [P, P.reverse]) : LiftsConn G v P P' := by
  simp only [mem_cons, not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact liftsConn_refl hdegH
  · exact liftsConn_reverse hdegH

theorem isHamH_of_mem {P P' : List V} (hP : IsHamH G v P) (h : P' ∈ [P, P.reverse]) :
    IsHamH G v P' := by
  simp only [mem_cons, not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact hP
  · exact isHamH_reverse hP

/-- `R(H)`-adjacent paths have all lifts in one component. -/
theorem liftsConn_of_stepRep {p q : List W}
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card)
    (hdegv : Fintype.card V + 3 ≤ 2 * G.degree v)
    (hp : IsHamPath (G.induce ({v}ᶜ : Set V)) p) (hq : IsHamPath (G.induce ({v}ᶜ : Set V)) q)
    (h : StepRep (G.induce ({v}ᶜ : Set V)) p q) :
    LiftsConn G v (p.map Subtype.val) (q.map Subtype.val) := by
  obtain ⟨p', hp', q', hq', hs⟩ := stepRep_map v h
  have hP := isHamH_map v hp
  have hQ := isHamH_map v hq
  have hP' := isHamH_of_mem v hP hp'
  have hQ' := isHamH_of_mem v hQ hq'
  refine liftsConn_trans hdegv hP' (liftsConn_of_mem v hdegH hp') ?_
  refine liftsConn_trans hdegv hQ' (liftsConn_of_step hdegH hdegv hs) ?_
  exact liftsConn_symm (liftsConn_of_mem v hdegH hq')

theorem liftsConn_of_reachable
    (hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card)
    (hdegv : Fintype.card V + 3 ≤ 2 * G.degree v)
    {X Y : RVert (G.induce ({v}ᶜ : Set V))} (w : (RGraph (G.induce ({v}ᶜ : Set V))).Walk X Y) :
    ∀ p q : HamPath (G.induce ({v}ᶜ : Set V)), Quotient.mk _ p = X → Quotient.mk _ q = Y →
      LiftsConn G v (p.1.map Subtype.val) (q.1.map Subtype.val) := by
  induction w with
  | nil =>
    intro p q hp hq
    rw [← hq] at hp
    rcases Quotient.exact hp with h | h
    · rw [← h]; exact liftsConn_refl hdegH
    · rw [h, map_reverse]; first | exact liftsConn_reverse hdegH | exact liftsConn_symm (liftsConn_reverse hdegH)
  | @cons X Z Y hadj w ih =>
    intro p q hp hq
    obtain ⟨r, rfl⟩ := Quotient.exists_rep Z
    have h1 := ih r q rfl hq
    subst hp
    simp only [RGraph, fromRel_adj] at hadj
    have hP := isHamH_map v p.2
    have hR := isHamH_map v r.2
    obtain ⟨_, h | h⟩ := hadj
    · exact liftsConn_trans hdegv hR (liftsConn_of_stepRep v hdegH hdegv p.2 r.2 h) h1
    · exact liftsConn_trans hdegv hR
        (liftsConn_symm (liftsConn_of_stepRep v hdegH hdegv r.2 p.2 h)) h1

end Bridge

/-- **Lemma 3 (vertex extension).** Let `H = G - v` have `h` vertices, `δ(H) ≥ h/2 + 2` and `R(H)`
connected, and let `d = |N(v) ∩ V(H)| ≥ h/2 + 2`. Then `R(G)` is connected. -/
theorem lemma3 (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hH : RConnected (G.induce ({v}ᶜ : Set V)))
    (hδ : ∀ x : ↥({v}ᶜ : Set V),
      Fintype.card ↥({v}ᶜ : Set V) + 4 ≤ 2 * (G.induce ({v}ᶜ : Set V)).degree x)
    (hd : Fintype.card ↥({v}ᶜ : Set V) + 4 ≤
      2 * ((G.neighborFinset v).filter (· ∈ ({v}ᶜ : Set V))).card) :
    RConnected G := by
  have hcard := card_compl_singleton v
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  have hdegH : ∀ x, x ≠ v → Fintype.card V + 3 ≤ 2 * ((G.neighborFinset x).erase v).card := by
    intro x hx
    have := hδ ⟨x, hx⟩
    rw [degree_induce_compl] at this
    simp only at this
    omega
  have hdegv : Fintype.card V + 3 ≤ 2 * G.degree v := by
    have : (G.neighborFinset v).filter (· ∈ ({v}ᶜ : Set V)) = G.neighborFinset v := by
      apply Finset.filter_true_of_mem
      intro x hx h
      rw [Set.mem_singleton_iff.1 h] at hx
      exact G.irrefl ((mem_neighborFinset _ _ _).1 hx)
    rw [this, card_neighborFinset_eq_degree] at hd
    omega
  refine rConnected_of_liftsConn hdegH hdegv ?_
  intro P Q hP hQ
  obtain ⟨p, hp, rfl⟩ := exists_of_isHamH v hP
  obtain ⟨q, hq, rfl⟩ := exists_of_isHamH v hQ
  obtain ⟨w⟩ := hH (Quotient.mk _ ⟨p, hp⟩) (Quotient.mk _ ⟨q, hq⟩)
  exact liftsConn_of_reachable v hdegH hdegv w ⟨p, hp⟩ ⟨q, hq⟩ rfl rfl

end Kazazi
