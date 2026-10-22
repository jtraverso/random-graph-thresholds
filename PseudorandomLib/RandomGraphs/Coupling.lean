/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Defs

/-! # Couplings of finite product spaces and monotonicity of `G(n, p)`

* `pE_map`: transport of an expectation along a coordinatewise map.
* `pE_pairSpace`: Fubini for a product space whose coordinates are pairs.
* `pProb_coinPair_or`: `G(n, 1 - (1 - p)(1 - q))` is the union of independent `G(n, p)` and
  `G(n, q)`.
* `gnpProb_mono`: monotone graph properties have nondecreasing probability in `p`.
-/

@[expose] public section

namespace Pseudorandom

open Finset

section General

variable {ι α β γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β] [Fintype γ]

/-- Transport of an expectation along a coordinatewise map `f : β → α`. -/
theorem pE_map [DecidableEq α] (P : ι → α → ℝ) (P' : ι → β → ℝ) (f : β → α)
    (h : ∀ i a, P i a = ∑ b, if f b = a then P' i b else 0) (g : (ι → α) → ℝ) :
    pE P' (fun ω => g (fun i => f (ω i))) = pE P g := by
  unfold pE pw
  have key : ∀ ω : ι → α, ∏ i, P i (ω i) =
      ∑ ω' : ι → β, if (fun i => f (ω' i)) = ω then ∏ i, P' i (ω' i) else 0 := by
    intro ω
    simp_rw [h]
    rw [Fintype.prod_sum]
    refine Fintype.sum_congr _ _ fun ω' => ?_
    rw [Finset.prod_ite_zero]
    congr 1
    simp only [Finset.mem_univ, true_imp_iff]
    exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩
  simp_rw [key, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun ω' => ?_
  rw [Finset.sum_eq_single (fun i => f (ω' i))]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Fubini for a product space whose coordinates are pairs with independent components. -/
theorem pE_pairSpace (P1 : ι → β → ℝ) (P2 : ι → γ → ℝ) (f : (ι → β × γ) → ℝ) :
    pE (fun i x => P1 i x.1 * P2 i x.2) f =
      pE P1 (fun ω1 => pE P2 (fun ω2 => f (fun i => (ω1 i, ω2 i)))) := by
  unfold pE pw
  have hR : (∑ ω1 : ι → β, (∏ i, P1 i (ω1 i)) *
      ∑ ω2 : ι → γ, (∏ i, P2 i (ω2 i)) * f (fun i => (ω1 i, ω2 i))) =
      ∑ x : (ι → β) × (ι → γ), (∏ i, P1 i (x.1 i)) * ((∏ i, P2 i (x.2 i)) *
        f (fun i => (x.1 i, x.2 i))) := by
    rw [Fintype.sum_prod_type]
    simp [Finset.mul_sum]
  rw [hR]
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow ι (fun _ => β) (fun _ => γ)) _ _
    fun ω => ?_
  simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk, Prod.mk.eta]
  rw [Finset.prod_mul_distrib]
  ring

theorem pProb_pairSpace (P1 : ι → β → ℝ) (P2 : ι → γ → ℝ) (S : (ι → β × γ) → Prop) :
    pProb (fun i x => P1 i x.1 * P2 i x.2) S =
      pE P1 (fun ω1 => pProb P2 (fun ω2 => S (fun i => (ω1 i, ω2 i)))) := by
  classical
  unfold pProb
  rw [pE_pairSpace]

theorem pProb_map [DecidableEq α] (P : ι → α → ℝ) (P' : ι → β → ℝ) (f : β → α)
    (h : ∀ i a, P i a = ∑ b, if f b = a then P' i b else 0) (S : (ι → α) → Prop) :
    pProb P' (fun ω => S (fun i => f (ω i))) = pProb P S := by
  classical
  unfold pProb
  rw [← pE_map P P' f h]

end General

namespace RandomGraphs

/-- Two independent families of coins, one with bias `p` and one with bias `q`. -/
noncomputable def coinPair (p q : ℝ) (n : ℕ) : Pairs n → Bool × Bool → ℝ :=
  fun e x => coin p n e x.1 * coin q n e x.2

theorem coinPair_isPMF {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (n : ℕ) : IsPMF (coinPair p q n) := by
  refine ⟨fun e x => mul_nonneg ((coin_isPMF hp0 hp1 n).1 e x.1)
    ((coin_isPMF hq0 hq1 n).1 e x.2), fun e => ?_⟩
  simp [coinPair, coin, Fintype.sum_prod_type]
  ring

/-- The first family of coins in `coinPair` has the law of `coin p`. -/
theorem pProb_coinPair_fst (p q : ℝ) (n : ℕ) (S : (Pairs n → Bool) → Prop) :
    pProb (coinPair p q n) (fun ω => S (fun e => (ω e).1)) = pProb (coin p n) S := by
  refine pProb_map (coin p n) (coinPair p q n) Prod.fst (fun e a => ?_) S
  cases a <;> simp [coinPair, coin, Fintype.sum_prod_type] <;> ring

/-- `G(n, 1 - (1 - p)(1 - q))` is the union of independent `G(n, p)` and `G(n, q)`. -/
theorem pProb_coinPair_or (p q : ℝ) (n : ℕ) (S : (Pairs n → Bool) → Prop) :
    pProb (coinPair p q n) (fun ω => S (fun e => (ω e).1 || (ω e).2)) =
      pProb (coin (1 - (1 - p) * (1 - q)) n) S := by
  refine pProb_map (coin (1 - (1 - p) * (1 - q)) n) (coinPair p q n) (fun x => x.1 || x.2)
    (fun e a => ?_) S
  cases a
  · simp [coinPair, coin, Fintype.sum_prod_type]
  · simp [coinPair, coin, Fintype.sum_prod_type]
    ring

theorem graphOf_mono {n : ℕ} {ω ω' : Pairs n → Bool} (h : ∀ e, ω e = true → ω' e = true) :
    graphOf ω ≤ graphOf ω' := by
  intro u v huv
  rw [graphOf_adj] at huv ⊢
  obtain ⟨hne, hω⟩ := huv
  exact ⟨hne, h _ hω⟩

/-- Monotone graph properties have nondecreasing probability in `G(n, p)`. -/
theorem gnpProb_mono {n : ℕ} {Q : SimpleGraph (Fin n) → Prop}
    (hQ : ∀ G H : SimpleGraph (Fin n), G ≤ H → Q G → Q H) {p q : ℝ} (hp0 : 0 ≤ p)
    (hpq : p ≤ q) (hq1 : q ≤ 1) : gnpProb n p Q ≤ gnpProb n q Q := by
  rcases eq_or_lt_of_le (le_trans hpq hq1) with hp1 | hp1
  · have : q = 1 := le_antisymm hq1 (hp1 ▸ hpq)
    rw [hp1, this]
  set r := (q - p) / (1 - p) with hr
  have h1p : 0 < 1 - p := by linarith
  have hr0 : 0 ≤ r := div_nonneg (by linarith) h1p.le
  have hr1 : r ≤ 1 := by rw [hr, div_le_one h1p]; linarith
  have hq : q = 1 - (1 - p) * (1 - r) := by
    rw [hr]; field_simp; ring
  unfold gnpProb
  rw [← pProb_coinPair_fst p r n, hq, ← pProb_coinPair_or p r n]
  refine pProb_mono (coinPair_isPMF hp0 hp1.le hr0 hr1 n) fun ω hω => hQ _ _ ?_ hω
  exact graphOf_mono fun e he => by simp [he]

end RandomGraphs

end Pseudorandom
