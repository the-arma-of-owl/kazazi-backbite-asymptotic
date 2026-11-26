# Lean formalization: definitions, Lemma 1, Facts A and B, Lemma 3, and §6 item 3

The code uses Lean 4.37.0-rc1 and Mathlib v4.37.0-rc1. It has no `sorry`, `admit`, new `axiom` or `native_decide`. Every main theorem depends only on `propext`, `Classical.choice` and `Quot.sound`; run `lake env lean KazaziLean/Axioms.lean` to see this. [`STATEMENTS.md`](STATEMENTS.md) puts each Lean statement next to the sentence of the paper it formalizes and lists every difference.

| Paper | Lean | Notes |
|---|---|---|
| §1 definitions | `IsHamPath`, `bbFront`, `bbBack`, `RGraph`, `RConnected` (`Defs.lean`) | Paths are lists. A path is identified with its reversal. |
| Backbites are invertible; the rotation fact ("Cycles") | `bbFront_invol`, `bbStep_symm`, `reachable_rotate` (`Lemmas.lean`) | |
| **Fact A** (crossings) | `factA`, `crossings_bounds`, `crossing_front` (`FactA.lean`) | Stated without truncated subtraction. |
| **Fact B** (interval reversal) | `factB` (`Forcing.lean`) | The cycle is written as a cyclic path starting at $a$. |
| Forcing graphs, **Lemma 1** | `IsForcing`, `lemma1` (`Forcing.lean`) | |
| **Lemma 3** (vertex extension), the key new tool | `lemma3` (`Lemma3*.lean`) | Fully proved, with the paper's hypotheses $\delta(H)\ge h/2+2$, $R(H)$ connected, $d\ge h/2+2$. |
| §6 item 3: Hamiltonicity is not sufficient | `hamiltonian_not_sufficient` (`Example.lean`) | Kernel `decide`. It proves that $R(G)$ is disconnected, but not the exact 18/4 split. |

**Not formalized:** Theorem 1 itself, Lemma 2 (forcing blow-up), Lemma 4 (typical core), §§4–5, and the other §6 computations.

## The main statement

```lean
theorem lemma3 (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hH : RConnected (G.induce ({v}ᶜ : Set V)))
    (hδ : ∀ x : ↥({v}ᶜ : Set V),
      Fintype.card ↥({v}ᶜ : Set V) + 4 ≤ 2 * (G.induce ({v}ᶜ : Set V)).degree x)
    (hd : Fintype.card ↥({v}ᶜ : Set V) + 4 ≤
      2 * ((G.neighborFinset v).filter (· ∈ ({v}ᶜ : Set V))).card) :
    RConnected G
```

Here $H$ is `G.induce {v}ᶜ`, the graph $G$ with $v$ removed, and $h=|\{v\}^c|$.

## Building

```bash
cd lean
lake exe cache get                     # prebuilt Mathlib
lake build                             # about 20 s after Mathlib
lake env lean KazaziLean/Axioms.lean   # prints the axioms of every main theorem
```

## How this was produced

- **Writing.** A Claude (Opus 5.5) agent wrote the Lean code.
- **Checking.** The coordinating Claude session then:
  - read the definitions and every main statement and compared them with the paper;
  - checked the files for `sorry`, `axiom`, `native_decide`, `implemented_by` and kernel-skipping options;
  - rebuilt everything from a clean state in this standalone project and confirmed the axioms.
