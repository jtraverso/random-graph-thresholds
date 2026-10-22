/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.FiniteProb

/-! # The binomial random graph `G(n, p)`

The random graph `G(n, p)` on the vertex set `Fin n` is modelled as a finite product probability
space (see `PseudorandomLib.FiniteProb`): one independent `Bernoulli(p)` coin for every potential
edge, i.e. for every non-diagonal unordered pair of vertices.
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

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

theorem coin_isPMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (n : ℕ) : IsPMF (coin p n) := by
  refine ⟨fun _ b => ?_, fun _ => ?_⟩
  · cases b <;> simp [coin] <;> linarith
  · simp [coin]

theorem graphOf_adj {n : ℕ} (ω : Pairs n → Bool) (u v : Fin n) :
    (graphOf ω).Adj u v ↔ ∃ h : u ≠ v, ω ⟨s(u, v), by simpa using h⟩ = true := by
  simp only [graphOf, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_, hω⟩, hne⟩
    exact ⟨hne, hω⟩
  · rintro ⟨hne, hω⟩
    exact ⟨⟨by simpa using hne, hω⟩, hne⟩

theorem graphOf_adj_iff {n : ℕ} (ω : Pairs n → Bool) (e : Pairs n) (u v : Fin n)
    (he : e.1 = s(u, v)) : (graphOf ω).Adj u v ↔ ω e = true := by
  rw [graphOf_adj]
  obtain ⟨e, hd⟩ := e
  subst he
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by simpa using hd, h⟩

end Pseudorandom.RandomGraphs
