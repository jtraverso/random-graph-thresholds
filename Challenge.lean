/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Thresholds for the binomial random graph `G(n, p)`

Statements in the namespace `RandomGraphThresholds`:

* `posa`: L. Pósa, *Hamiltonian circuits in random graphs*, Discrete Math. 14 (1976) 359–364:
  for some constant `C`, `G(n, p)` with `p ≥ C log n / n` is Hamiltonian with probability
  tending to `1`.
* `connected_of_log_add`, `not_connected_of_log_sub`: the connectivity threshold of Erdős and
  Rényi (1959): `G(n, (log n ± ω(n))/n)` with `ω(n) → ∞` is connected with probability tending
  to `1`, resp. `0`.

`G(n, p)` is modelled as a finite product probability space with one independent `Bernoulli(p)`
coin for each unordered pair of distinct vertices of `Fin n`. The definitions below are part of
the audited statements; the Mathlib definitions used (including `SimpleGraph.IsHamiltonian` and
`SimpleGraph.Connected`) are reproduced in `MATHLIB_DEFINITIONS.md`.
-/

@[expose] public section

namespace RandomGraphThresholds

section ProductProbability

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The product weight of an outcome. -/
def pw (P : ι → α → ℝ) (ω : ι → α) : ℝ := ∏ i, P i (ω i)

/-- Expectation in the product space. -/
def pE (P : ι → α → ℝ) (f : (ι → α) → ℝ) : ℝ := ∑ ω, pw P ω * f ω

open Classical in
/-- Probability of an event in the product space. -/
noncomputable def pProb (P : ι → α → ℝ) (S : (ι → α) → Prop) : ℝ :=
  pE P (fun ω => if S ω then 1 else 0)

end ProductProbability

/-- The potential edges of a graph on `Fin n`. -/
abbrev Pairs (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- Independent `Bernoulli(p)` coins, one per pair. -/
noncomputable def coin (p : ℝ) (n : ℕ) : Pairs n → Bool → ℝ := fun _ b => if b then p else 1 - p

/-- The graph whose edges are the pairs whose coin came up `true`. -/
def graphOf {n : ℕ} (ω : Pairs n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬ e.IsDiag, ω ⟨e, h⟩ = true}

/-- `P(G(n, p) has property Q)`. -/
noncomputable def gnpProb (n : ℕ) (p : ℝ) (Q : SimpleGraph (Fin n) → Prop) : ℝ :=
  pProb (coin p n) (fun ω => Q (graphOf ω))

/-- **Pósa (1976).** There is `C > 0` such that for every `ε > 0` and all large `n`, `G(n, p)`
is Hamiltonian with probability at least `1 - ε` whenever `C log n / n ≤ p ≤ 1`. -/
theorem posa : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ p : ℝ, C * Real.log n / n ≤ p → p ≤ 1 →
    1 - ε ≤ gnpProb n p (fun G => G.IsHamiltonian) := by
  sorry

/-- **Erdős–Rényi (1959), connectivity, upper side.** If `ω(n) → ∞`, then
`G(n, (log n + ω(n))/n)` is connected with probability tending to `1`. -/
theorem connected_of_log_add (ω : ℕ → ℝ) (hω : Filter.Tendsto ω Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n : ℕ => gnpProb n (min 1 ((Real.log n + ω n) / n)) (fun G => G.Connected))
      Filter.atTop (nhds 1) := by
  sorry

/-- **Erdős–Rényi (1959), connectivity, lower side.** If `ω(n) → ∞`, then
`G(n, (log n - ω(n))/n)` is connected with probability tending to `0`. -/
theorem not_connected_of_log_sub (ω : ℕ → ℝ) (hω : Filter.Tendsto ω Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n : ℕ => gnpProb n (max 0 ((Real.log n - ω n) / n)) (fun G => G.Connected))
      Filter.atTop (nhds 0) := by
  sorry

end RandomGraphThresholds
