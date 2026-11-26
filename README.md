# Backbite reconfiguration: Kazazi's conjecture holds asymptotically

**Paper:** [`paper/asymptotic_threshold.md`](paper/asymptotic_threshold.md) · **Independent verification:** [`VERIFICATION.md`](VERIFICATION.md) · **Code:** [`code/`](code/) · **Data:** [`data/`](data/)

## Result

A *backbite* on a Hamiltonian path picks an endpoint $u$, adds an edge $uv$ of the graph, and deletes the path edge at $v$ that keeps the result a Hamiltonian path. This is the "rotation" from Pósa's rotation–extension method and the move behind backbite Monte Carlo sampling of polymers. $R(G)$ is the graph whose vertices are the Hamiltonian paths of $G$, two paths being adjacent when one backbite turns one into the other.

A. Kazazi ([arXiv:2610.05068](https://arxiv.org/abs/2610.05068), Oct 2026) proved that $R(G)$ is connected when $\delta(G)\ge\lceil(2n-1)/3\rceil$. He built graphs with $\delta(G)=\lfloor n/2\rfloor-3$ whose $R(G)$ is disconnected, and conjectured that $\delta(G)\ge n/2$ suffices (**Conjecture 7.8**).

> **Theorem.** For every $\gamma>0$ there is $n_0(\gamma)$ such that every graph $G$ on $n\ge n_0(\gamma)$ vertices with $\delta(G)\ge(1/2+\gamma)n$ has connected $R(G)$.

So the minimum-degree threshold is $n/2+o(n)$. This improves the proven ratio from $2/3$ to the conjectured $1/2$, asymptotically. The exact conjecture ($\delta\ge n/2$ for every $n$) remains open.

**Key new tool: the vertex-extension lemma.** If $\delta(H)\ge |H|/2+2$ and $R(H)$ is connected, then adding a vertex with at least $|H|/2+2$ neighbours in $H$ keeps $R$ connected.

The proof has three further ingredients:

- a forcing blow-up structure;
- a sampling argument based on Erdős's box theorem;
- a random vertex ordering.

### Computational findings (see paper §6)

- Conjecture 7.8 holds for every $n\le 12$, checked exhaustively ($n=12$: all 495,369,040 graphs with $\delta\ge 6$).
- Every graph with $n=10,\ \delta\ge4$ (1,249,973 graphs) and every graph with $n=9,\ \delta\ge3$ has connected $R(G)$, so the conjecture is far from tight at small $n$.
- **Hamiltonicity alone is not enough.** A Hamiltonian graph on 10 vertices has disconnected $R(G)$. All of Kazazi's examples are non-Hamiltonian.
- **New, stronger conjecture (fixed endpoint, Pósa rotations).** For $\delta\ge n/2$ and every vertex $b$, Hamiltonian paths ending at $b$ are connected using moves at the other end only. This was verified for all $n\le 10$, and it fails just below $n/2$. Equivalently, Kazazi's conjecture survives attaching one pendant vertex.
- A Bondy–Chvátal-style closure lemma fails ($n=9$).
- The exact diameter of $R(P_n^2)$ is computed for $n\le 18$.

## Özet (Türkçe)

Kazazi (Ekim 2026) Hamilton yollarının "backbite" hamleleriyle yeniden yapılandırma grafiği $R(G)$ için şu sanıyı ortaya attı: $\delta(G)\ge n/2$ ise $R(G)$ bağlantılıdır. Kendisi bunu yalnızca $\delta\ge(2n-1)/3$ için kanıtlamıştı.

Bu depoda sanının **asimptotik** halini kanıtlıyoruz: her $\gamma>0$ için, yeterince büyük $n$'de $\delta\ge(1/2+\gamma)n$ yeterlidir. Kazazi'nin $\lfloor n/2\rfloor-3$'teki karşı örnekleriyle birlikte bu, eşiğin $n/2+o(n)$ olduğunu gösterir. Tam sanı ($\delta\ge n/2$, her $n$ için) hâlâ açıktır.

Ayrıca bilgisayarla şunları gösterdik:

- Sanı $n\le 12$ için doğrudur ($n=12$'de 495 milyon graf tarandı).
- Hamilton döngüsü olması tek başına yetmez; $n=10$'da bir örnek var.
- Daha güçlü bir "sabit uçlu" sürüm $n\le 10$'da doğrudur ve $n/2$'nin hemen altında bozulur. Bunu yeni bir sanı olarak öneriyoruz.

## How this was produced

- **Direction.** Efe Çam directed the work.
- **Proof.** The proof idea and first draft of the proof came from **GPT-6.2 Astra** (OpenAI, via Codex), prompted with the problem and our computational findings.
- **Computations, checking and write-up.** **Claude** (Anthropic, via Claude Code) wrote and ran all computations, checked the proof line by line, filled in the details and wrote the paper.
- **Independent verification.** A separate Claude instance with no access to the above reasoning refereed the write-up adversarially; see [`VERIFICATION.md`](VERIFICATION.md). A second review came from GPT-6.2 Sol ([`REVIEW_GPT-6.2-Sol.md`](REVIEW_GPT-6.2-Sol.md)). Both reviews were of v1; their minor fixes are in v1.1 (see [`CHANGELOG.md`](CHANGELOG.md)).

Errors are possible. Please open an issue if you find one.

## Reproducing the computations

Requirements: `gcc`, `python3`, `geng` (nauty).

```bash
cd code
gcc -O3 -o bbconn bbconn.c && gcc -O3 -o forcing forcing.c && gcc -O3 -o sabituc sabituc.c
geng -q -d5 10 | ./bbconn -s        # Conjecture 7.8, n = 10 (graphs containing P_n^2 are skipped: Kazazi's theorem)
python3 aday.py c1 10 | ./forcing   # the cycle C_10 is not "forcing"
python3 blowup.py 1,2,3,3 | ./forcing
```

Some output labels are in Turkish:

| Label | Meaning |
|---|---|
| `BAGLANTISIZ` | disconnected |
| `incelenen` | checked |
| `kare_yol_atlanan` | skipped: contains $P_n^2$ |
| `baglantisiz` | number disconnected |
| `ZORLAYICI` | forcing |
| `DEGIL` | not |
| `ulasilan` | reached |
| `bilesen` | components |

## Citation / Atıf

```bibtex
@misc{cam2026backbite,
  author       = {{\c{C}}am, Efe},
  title        = {Backbite reconfiguration of {H}amiltonian paths: the minimum-degree threshold is asymptotically $n/2$},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://github.com/the-arma-of-owl/kazazi-backbite-asymptotic}},
  note         = {Version 1.1}
}
```

The same metadata is in [`CITATION.cff`](CITATION.cff), which GitHub uses for its “Cite this repository” button. Atıf için bu BibTeX kaydını ya da GitHub'daki “Cite this repository” düğmesini kullanabilirsiniz.

## License

Text: CC BY 4.0. Code: MIT.
