/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Connectivity
public import PseudorandomLib.RandomGraphs.Rotation

/-! # Expansion of `G(n, p)`

If some set `S` with `s = |S| ≤ n / 4` has fewer than `2 s` neighbours outside `S`, then there is a
set `T` of `2 s` vertices outside `S` such that no edge joins `S` to the remaining `n - 3 s`
vertices. The union bound gives
`P(G(n, p) is not an (n/4)-expander) ≤ ∑_{s=1}^{n/4} n^{3s} (1 - p)^{s (n - 3 s)}`
(`gnpProb_not_expander_le`), which is at most `r / (1 - r)` with `r = n³ e^{-p n / 4}`
(`expanderBound_le`).
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open Finset Real

variable {n : ℕ}

/-- A witness to the failure of expansion. -/
theorem exists_witness_of_not_expander (G : SimpleGraph (Fin n)) (h : ¬ IsExpander G (n / 4)) :
    ∃ s ∈ Icc 1 (n / 4), ∃ S ∈ powersetCard s (univ : Finset (Fin n)),
      ∃ T ∈ powersetCard (2 * s) (univ \ S), ∀ a ∈ S, ∀ b ∈ univ \ (S ∪ T), ¬ G.Adj a b := by
  classical
  unfold IsExpander at h
  push Not at h
  obtain ⟨S, hS, hlt⟩ := h
  have hs1 : 1 ≤ S.card := by
    rcases Nat.eq_zero_or_pos S.card with h0 | h0
    · rw [h0] at hlt; simp at hlt
    · exact h0
  have h4 : 4 * S.card ≤ n := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).1 hS; omega
  have hcardc : (univ \ S).card = n - S.card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  obtain ⟨T, hNT, hT, hTcard⟩ := exists_subsuperset_card_eq
    (sdiff_subset_sdiff (subset_univ (nbhd G S)) (subset_refl S)) hlt.le
    (by rw [hcardc]; omega)
  refine ⟨S.card, mem_Icc.2 ⟨hs1, hS⟩, S, mem_powersetCard.2 ⟨subset_univ _, rfl⟩, T,
    mem_powersetCard.2 ⟨hT, hTcard⟩, fun a ha b hb hab => ?_⟩
  have hb' := (mem_sdiff.1 hb).2
  rw [mem_union, not_or] at hb'
  have : b ∈ nbhd G S \ S := by
    simp only [nbhd, mem_sdiff, mem_filter, mem_univ, true_and]
    exact ⟨⟨a, ha, hab⟩, hb'.1⟩
  exact hb'.2 (hNT this)

/-- The union bound for non-expansion. -/
theorem gnpProb_not_expander_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    gnpProb n p (fun G => ¬ IsExpander G (n / 4)) ≤
      ∑ s ∈ Icc 1 (n / 4), (n : ℝ) ^ (3 * s) * (1 - p) ^ (s * (n - 3 * s)) := by
  classical
  have hP := coin_isPMF hp0 hp1 n
  unfold gnpProb
  refine (pProb_mono hP fun ω h => exists_witness_of_not_expander _ h).trans ?_
  refine (pProb_exists_le hP _ _).trans (sum_le_sum fun s hs => ?_)
  have hs := mem_Icc.1 hs
  have h4 : 4 * s ≤ n := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).1 hs.2; omega
  refine (pProb_exists_le hP _ _).trans ?_
  refine (sum_le_sum fun S _ => pProb_exists_le hP _ _).trans ?_
  have hterm : ∀ S ∈ powersetCard s (univ : Finset (Fin n)), ∀ T ∈ powersetCard (2 * s) (univ \ S),
      pProb (coin p n) (fun ω => ∀ a ∈ S, ∀ b ∈ univ \ (S ∪ T), ¬ (graphOf ω).Adj a b) =
        (1 - p) ^ (s * (n - 3 * s)) := by
    intro S hS T hT
    have hS := mem_powersetCard.1 hS
    have hT := mem_powersetCard.1 hT
    have hdisj : Disjoint S T := by
      rw [disjoint_left]
      intro a haS haT
      exact (mem_sdiff.1 (hT.1 haT)).2 haS
    have h := gnpProb_noCross hp0 hp1 (disjoint_left.2 fun a (ha : a ∈ S) hb =>
      (mem_sdiff.1 hb).2 (mem_union_left _ ha) : Disjoint S (univ \ (S ∪ T)))
    unfold gnpProb at h
    rw [h, card_sdiff_of_subset (subset_univ _), card_union_of_disjoint hdisj, card_univ,
      Fintype.card_fin, hS.2, hT.2]
    congr 2
    omega
  calc ∑ S ∈ powersetCard s (univ : Finset (Fin n)), ∑ T ∈ powersetCard (2 * s) (univ \ S),
        pProb (coin p n) (fun ω => ∀ a ∈ S, ∀ b ∈ univ \ (S ∪ T), ¬ (graphOf ω).Adj a b)
      = ∑ S ∈ powersetCard s (univ : Finset (Fin n)), ∑ _T ∈ powersetCard (2 * s) (univ \ S),
          (1 - p) ^ (s * (n - 3 * s)) :=
        sum_congr rfl fun S hS => sum_congr rfl fun T hT => hterm S hS T hT
    _ ≤ ∑ _S ∈ powersetCard s (univ : Finset (Fin n)), (n : ℝ) ^ (2 * s) *
          (1 - p) ^ (s * (n - 3 * s)) := by
        refine sum_le_sum fun S hS => ?_
        rw [sum_const, card_powersetCard, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by linarith) _)
        have hc : (univ \ S).card ≤ n := by
          have := card_le_univ (univ \ S); simpa using this
        calc (((univ \ S).card.choose (2 * s) : ℕ) : ℝ)
            ≤ (((univ \ S).card ^ (2 * s) : ℕ) : ℝ) := by
              exact_mod_cast Nat.choose_le_pow _ _
          _ ≤ (n : ℝ) ^ (2 * s) := by
              push_cast; exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hc) _
    _ ≤ (n : ℝ) ^ (3 * s) * (1 - p) ^ (s * (n - 3 * s)) := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by linarith) _)
        rw [show 3 * s = s + 2 * s by ring, pow_add]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Nat.choose_le_pow _ _

/-- The non-expansion bound is geometrically small. -/
theorem expanderBound_le (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : (n : ℝ) ^ 3 * exp (-(p * n / 4)) < 1) :
    ∑ s ∈ Icc 1 (n / 4), (n : ℝ) ^ (3 * s) * (1 - p) ^ (s * (n - 3 * s)) ≤
      (n : ℝ) ^ 3 * exp (-(p * n / 4)) / (1 - (n : ℝ) ^ 3 * exp (-(p * n / 4))) := by
  set r := (n : ℝ) ^ 3 * exp (-(p * n / 4)) with hrdef
  have hr0 : 0 ≤ r := by positivity
  calc ∑ s ∈ Icc 1 (n / 4), (n : ℝ) ^ (3 * s) * (1 - p) ^ (s * (n - 3 * s))
      ≤ ∑ s ∈ Icc 1 (n / 4), r ^ s := by
        refine sum_le_sum fun s hs => ?_
        have hs := mem_Icc.1 hs
        have h4 : 4 * s ≤ n := by
          have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).1 hs.2; omega
        have hcast : ((n - 3 * s : ℕ) : ℝ) = n - 3 * s := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        have h4' : (4 : ℝ) * s ≤ n := by exact_mod_cast h4
        have hpow : (1 - p) ^ (s * (n - 3 * s)) ≤ exp (-(p * n / 4)) ^ s := by
          calc (1 - p) ^ (s * (n - 3 * s)) ≤ exp (-p) ^ (s * (n - 3 * s)) :=
                pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-p)]) _
            _ = exp (-(p * s * (n - 3 * s))) := by
                rw [← Real.exp_nat_mul]; push_cast [Nat.cast_mul, hcast]; ring_nf
            _ ≤ exp (-(p * n / 4) * s) := by
                refine exp_le_exp.2 ?_
                have : (n : ℝ) / 4 ≤ n - 3 * s := by linarith
                have hs0 : (0 : ℝ) ≤ s := by positivity
                nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hp0 hs0)]
            _ = exp (-(p * n / 4)) ^ s := by rw [← Real.exp_nat_mul]; ring_nf
        calc (n : ℝ) ^ (3 * s) * (1 - p) ^ (s * (n - 3 * s))
            ≤ ((n : ℝ) ^ 3) ^ s * exp (-(p * n / 4)) ^ s := by
              rw [← pow_mul]
              exact mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = r ^ s := by rw [hrdef, mul_pow]
    _ = ∑ s ∈ Ico 1 (n / 4 + 1), r ^ s := rfl
    _ ≤ r ^ 1 / (1 - r) := geom_sum_Ico_le_of_lt_one hr0 hr
    _ = r / (1 - r) := by rw [pow_one]

end Pseudorandom.RandomGraphs
