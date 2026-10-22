# Hamiltonicity and connectivity thresholds of G(n, p) in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of two classical threshold results for the binomial random
graph `G(n, p)`:

* **Pósa's theorem** (L. Pósa, *Hamiltonian circuits in random graphs*, Discrete Math. 14 (1976)
  359–364). For some constant `C`, `G(n, p)` with `p ≥ C log n / n` is Hamiltonian with
  probability tending to `1`. The proof gives `C = 80`.
* **The connectivity threshold of Erdős and Rényi** (*On random graphs I*, Publ. Math.
  Debrecen 6 (1959) 290–297), on both sides. If `ω(n) → ∞`, then `G(n, (log n + ω(n))/n)` is
  connected with probability tending to `1`, and `G(n, (log n − ω(n))/n)` with probability
  tending to `0`.

All statements are in the namespace `RandomGraphThresholds` of `Challenge.lean`.

## The model

`G(n, p)` lives on the vertex set `Fin n`. It is a finite product probability space with one
independent `Bernoulli(p)` coin for each unordered pair of distinct vertices (`Pairs n`, `coin`).
`graphOf ω` is the graph of the pairs whose coin came up `true`, and `gnpProb n p Q` is the
probability that `G(n, p)` has property `Q`. The product-space definitions `pw`, `pE` and `pProb`
are copied in the Challenge. Hamiltonicity and connectivity are Mathlib's
`SimpleGraph.IsHamiltonian` and `SimpleGraph.Connected`.

## Results

| Lean | Statement |
|---|---|
| `posa` | `∃ C > 0, ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, ∀ p ∈ [C log n / n, 1], P(G(n, p) is Hamiltonian) ≥ 1 − ε` |
| `connected_of_log_add` | `ω → ∞ ⟹ P(G(n, min 1 ((log n + ω n)/n)) is connected) → 1` |
| `not_connected_of_log_sub` | `ω → ∞ ⟹ P(G(n, max 0 ((log n − ω n)/n)) is connected) → 0` |

## Proofs

The proofs are in `PseudorandomLib/RandomGraphs/`. They build on the finite product probability
of the author's Ehard–Glock–Joos formalization (`PseudorandomLib/FiniteProb.lean`, unchanged,
from Palomar PALOMAR-2026-10-17-000004).

* **Connectivity, upper side** (`Connectivity.lean`): a union bound over the vertex sets of size
  at most `n/2` with no edge leaving them.
* **Connectivity, lower side** (`Isolated.lean`): the second moment method on isolated
  vertices.
* **Pósa's theorem** (`Posa.lean` and its imports) is proved by a two-round exposure, writing
  `G(n, p)` as a union of independent `G(n, p₁)` and `G(n, p₂)`:
  * with high probability `G(n, p₁)` is an expander (`Expansion.lean`);
  * Pósa's rotation lemma gives many endpoints of longest paths (`Rotation.lean`), hence many
    boosters (`Boosters.lean`);
  * a union bound over at most `n` boosting rounds (`Round.lean`) closes a Hamiltonian cycle;
  * monotonicity in `p`, by coupling (`Coupling.lean`), covers every `p ∈ [80 log n/n, 1]`.

No `sorry` and no `native_decide` is used; the only axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the audited statements. It imports
  only Mathlib.
- [`Solution.lean`](Solution.lean) and [`PseudorandomLib/`](PseudorandomLib): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## Sources

* L. Pósa, *Hamiltonian circuits in random graphs*, Discrete Math. 14 (1976) 359–364,
  doi:10.1016/0012-365X(76)90068-6.
* P. Erdős, A. Rényi, *On random graphs I*, Publ. Math. Debrecen 6 (1959) 290–297,
  doi:10.5486/PMD.1959.6.3-4.12.

## Authorship and use of AI

The author chose the results and directed the work. The proofs were produced by Harmonic's
Aristotle from formal statements and a suggested proof route, on top of the author's
Ehard–Glock–Joos library. Claude (Claude Code) wrote the model and the statements, audited the
return, built it locally and prepared this package. Lean checks everything mechanically. See
`formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
