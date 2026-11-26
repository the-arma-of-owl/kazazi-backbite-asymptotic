# Changelog

## v1.1 (26 Nov 2026)

v1.1 incorporates the two independent reviews of v1: [`VERIFICATION.md`](VERIFICATION.md) (Claude) and [`REVIEW_GPT-6.2-Sol.md`](REVIEW_GPT-6.2-Sol.md). Both found **no mathematical error in the proof of Theorem 1**. The v1 text is kept as `paper/.v1_reviewed.md`.

### Corrections

- **§6.6, error.** v1 listed "the 3×m grid" as forcing. Only the 3×3 grid is forcing. The 3×4 grid is not: the explicit ordering `0 3 4 5 2 1 7 10 9 6 8 11` cannot reach a grid path. Our own data already showed this (`data/forcing_skeletons.txt`); the text was wrong. The orders tested for each skeleton are now stated.
- **Remark 1, error.** The bound $n_0(\gamma)$ is doubly exponential, $\exp\exp(O(\gamma^{-2}\log^2(1/\gamma)))$, not tower-type.
- **Remark 3, removed.** It stated without proof that Lemma 3 (then Lemma 4) holds with weaker constants. Both referees found a gap in the "same proof" claim. The remark was not used anywhere.
- **§6.3, wording.** The five listed graph6 codes are one graph up to isomorphism, and the text now says so.

### Gaps closed (none affects correctness)

- **Lemma 2(i), degenerate cases.** Both circuits are cut at a fixed vertex of $W_1$. Reversing the whole closed trail is trivial. The twin swap is trivial when $|V|=1$. Fact B now states $a\ne b$.
- **Fact A.** The corollary now assumes $n\ge 3$.
- **Lemma 4 (then Lemma 5).** $t$ is an integer, and Hoeffding's bound is stated for $u\ge 0$.

### Attribution

- **Squared paths.** The forcing property of $P_n^2$ is now attributed to the proof of [K, Cor. 3.4, Prop. 5.1], not to the statement of [K, Thm 1.1].
- **Lemma 2(ii).** The proof is said to follow [K, §3] closely.
- **Fact A.** Attributed to Dirac, Ore and Pósa.
- **References.** [D] and [O] were added, and [FK] and [KPS] are now cited in the text.

### Numbering

- Facts 2, 3 → Facts A, B.
- Lemmas 4, 5 → Lemmas 3, 4.
- "Property (F)" → "forcing".
- In Remark 2, $K_{n/2,n/2}$ is now called bipartite, not near-bipartite.

### Additions

- **§6.1.** Conjecture 7.8 also holds for $n=12$. All 495,369,040 graphs with $\delta\ge6$ contain a spanning $P_{12}^2$, a spanning ladder, or a spanning $d_{13}$, and all three are forcing at $n=12$. The containment code was cross-checked against brute force.
- **§6.4.** The fixed-endpoint property is equivalent to connectivity of $R(G+\text{pendant vertex at }b)$. This was checked on 150 random graphs.
