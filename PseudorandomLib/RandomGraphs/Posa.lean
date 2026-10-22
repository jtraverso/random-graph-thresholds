/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Round
public import PseudorandomLib.RandomGraphs.Expansion
public import PseudorandomLib.RandomGraphs.HamCycle
public import PseudorandomLib.RandomGraphs.Coupling

/-! # Pósa's theorem: Hamiltonicity of `G(n, C log n / n)`

Two-round exposure: `G(n, 1 - (1 - p₁)(1 - p₂))` is the union of independent `G₁ = G(n, p₁)` and
`G₂ = G(n, p₂)` with `p₁ = 16 log n / n` and `p₂ = 64 log n / n`. With high probability `G₁` is
connected and every set of at most `n / 4` vertices expands by a factor two; for every such `G₁`
the sprinkling round (`round_bound`) fails with probability at most `e (n + 1) (64 log n / n)^n`.
By monotonicity, `G(n, p)` is Hamiltonian with high probability for every `p ≥ 80 log n / n`.
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open Finset Real Filter

/-- Two-round exposure: the failure probability of Hamiltonicity in the union is at most the
failure probability of the first round plus a uniform bound for the second round. -/
theorem gnpProb_not_hamCycle_le (n : ℕ) {p₁ p₂ δ : ℝ} (hp₁0 : 0 ≤ p₁) (hp₁1 : p₁ ≤ 1)
    (hp₂0 : 0 ≤ p₂) (hp₂1 : p₂ ≤ 1) (hδ : 0 ≤ δ)
    (hgood : ∀ ω₁ : Pairs n → Bool, (graphOf ω₁).Connected → IsExpander (graphOf ω₁) (n / 4) →
      pProb (coin p₂ n) (fun ω₂ => ¬ HasHamCycle (graphOf ω₁ ⊔ graphOf ω₂)) ≤ δ) :
    gnpProb n (1 - (1 - p₁) * (1 - p₂)) (fun G => ¬ HasHamCycle G) ≤
      gnpProb n p₁ (fun G => ¬ G.Connected) + gnpProb n p₁ (fun G => ¬ IsExpander G (n / 4)) +
        δ := by
  classical
  have hP₁ := coin_isPMF hp₁0 hp₁1 n
  have hP₂ := coin_isPMF hp₂0 hp₂1 n
  unfold gnpProb
  rw [← pProb_coinPair_or p₁ p₂ n (fun ω => ¬ HasHamCycle (graphOf ω))]
  have h := pProb_pairSpace (coin p₁ n) (coin p₂ n)
    (fun ω => ¬ HasHamCycle (graphOf (fun e => (ω e).1 || (ω e).2)))
  simp only at h
  rw [show coinPair p₁ p₂ n = fun i x => coin p₁ n i x.1 * coin p₂ n i x.2 from rfl, h]
  simp_rw [graphOf_or]
  set bad : (Pairs n → Bool) → Prop :=
    fun ω₁ => ¬ (graphOf ω₁).Connected ∨ ¬ IsExpander (graphOf ω₁) (n / 4) with hbad
  calc pE (coin p₁ n) (fun ω₁ => pProb (coin p₂ n)
          (fun ω₂ => ¬ HasHamCycle (graphOf ω₁ ⊔ graphOf ω₂)))
      ≤ pE (coin p₁ n) (fun ω₁ => (if bad ω₁ then 1 else 0) + δ) := by
        refine pE_mono hP₁ fun ω₁ => ?_
        by_cases hb : bad ω₁
        · simp only [hb, ↓reduceIte]
          have := pProb_le_one hP₂ (fun ω₂ => ¬ HasHamCycle (graphOf ω₁ ⊔ graphOf ω₂))
          linarith
        · simp only [hb, ↓reduceIte, zero_add]
          simp only [hbad, not_or, not_not] at hb
          exact hgood ω₁ hb.1 hb.2
    _ = pProb (coin p₁ n) bad + δ := by
        rw [pE_add, pE_const hP₁,
          pProb_eq_pE bad (fun ω => if bad ω then 1 else 0) (fun ω h => by simp [h])
          (fun ω h => by simp [h])]
    _ ≤ _ := by
        have := pProb_or_le hP₁ (fun ω₁ => ¬ (graphOf ω₁).Connected)
          (fun ω₁ => ¬ IsExpander (graphOf ω₁) (n / 4))
        linarith

theorem one_lt_log_of_four_le {n : ℕ} (hn : 4 ≤ n) : 1 < Real.log n := by
  have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- The numerical bound for the sprinkling round with `q = 64 log n / n`. -/
theorem round_numeric {n : ℕ} (hn : 4 ≤ n) (hq : 64 * Real.log n / n ≤ 1 / 4) :
    ∑ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ n),
        (64 * Real.log n / n) ^ F.card * (1 - 64 * Real.log n / n) ^ ((n / 4 + 1) ^ 2 / 2) ≤
      exp 1 * (n + 1) * (1 / 4) ^ n := by
  set L := Real.log n with hL
  set q := 64 * L / n with hqdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL1 : 1 < L := one_lt_log_of_four_le hn
  have hq0 : 0 ≤ q := by positivity
  have hX : (n : ℝ) ^ 2 * q = 64 * n * L := by rw [hqdef]; field_simp
  have hX1 : 1 ≤ (n : ℝ) ^ 2 * q := by
    rw [hX]
    have : (1 : ℝ) ≤ n := by linarith [show (4 : ℝ) ≤ n by exact_mod_cast hn]
    nlinarith
  set M := (n / 4 + 1) ^ 2 / 2 with hM
  have hMreal : (n : ℝ) ^ 2 / 32 - 1 / 2 ≤ M := by
    have h1 : (n / 4 + 1) ^ 2 ≤ 2 * M + 1 := by
      have := Nat.div_add_mod ((n / 4 + 1) ^ 2) 2
      have := Nat.mod_lt ((n / 4 + 1) ^ 2) (by norm_num : 2 > 0)
      omega
    have h2 : n + 1 ≤ 4 * (n / 4 + 1) := by omega
    have h1' : ((n / 4 + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * M + 1 := by exact_mod_cast h1
    have h2' : (n : ℝ) / 4 ≤ ((n / 4 + 1 : ℕ) : ℝ) := by
      have : ((n + 1 : ℕ) : ℝ) ≤ ((4 * (n / 4 + 1) : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this ⊢
      linarith
    have h3 : ((n : ℝ) / 4) ^ 2 ≤ ((n / 4 + 1 : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2' 2
    nlinarith
  have hexp : (1 - q) ^ M ≤ exp (1 - 2 * n * L) := by
    calc (1 - q) ^ M ≤ exp (-q) ^ M :=
          pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-q)]) _
      _ = exp (-(q * M)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ exp (1 - 2 * n * L) := by
          refine exp_le_exp.2 ?_
          have : q * ((n : ℝ) ^ 2 / 32 - 1 / 2) ≤ q * M := mul_le_mul_of_nonneg_left hMreal hq0
          have hqn : q * (n : ℝ) ^ 2 = 64 * n * L := by rw [mul_comm]; exact hX
          nlinarith
  have hsum := sum_small_sets_le hq0 hX1
  have hkey : (n : ℝ) ^ 2 * q * exp (-(2 * L)) = q := by
    rw [Real.exp_neg, show 2 * L = Real.log ((n : ℝ) ^ 2) by rw [hL, Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
    field_simp
  rw [← sum_mul]
  calc (∑ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ n), q ^ F.card) *
        (1 - q) ^ M
      ≤ ((n + 1) * ((n : ℝ) ^ 2 * q) ^ n) * exp (1 - 2 * n * L) :=
        mul_le_mul hsum hexp (pow_nonneg (by linarith) _) (by positivity)
    _ = exp 1 * (n + 1) * ((n : ℝ) ^ 2 * q * exp (-(2 * L))) ^ n := by
        rw [mul_pow (a := (n : ℝ) ^ 2 * q) (b := exp (-(2 * L))), ← Real.exp_nat_mul,
          show (1 : ℝ) - 2 * n * L = 1 + n * (-(2 * L)) by ring, Real.exp_add]
        ring
    _ = exp 1 * (n + 1) * q ^ n := by rw [hkey]
    _ ≤ exp 1 * (n + 1) * (1 / 4) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq _) (by positivity)

/-- The disconnection bound for `p₁ = 16 log n / n`. -/
noncomputable def connErr (n : ℕ) : ℝ :=
  4 * exp 1 * exp (-(15 * Real.log n / 4)) / (1 - 4 * exp 1 * exp (-(15 * Real.log n / 4)))

/-- The non-expansion bound for `p₁ = 16 log n / n`. -/
noncomputable def expErr (n : ℕ) : ℝ := (1 / n) / (1 - 1 / n)

/-- The sprinkling bound for `p₂ = 64 log n / n`. -/
noncomputable def roundErr (n : ℕ) : ℝ := exp 1 * (n + 1) * (1 / 4) ^ n

theorem eventually_good : ∀ᶠ n : ℕ in atTop,
    4 ≤ n ∧ 64 * Real.log n / n ≤ 1 / 4 ∧ 4 * exp 1 * exp (-(15 * Real.log n / 4)) < 1 := by
  have hL : Tendsto (fun n : ℕ => Real.log n / n) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ => 4 * exp 1 * exp (-(15 * Real.log n / 4))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => 15 * Real.log n / 4) atTop atTop :=
      (hlogn.const_mul_atTop (by norm_num : (0 : ℝ) < 15)).atTop_div_const (by norm_num)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (4 * exp 1)
    simpa [Function.comp_def] using h2
  filter_upwards [eventually_ge_atTop 4,
    hL.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 256)),
    hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n h1 h2 h3
  refine ⟨h1, ?_, h3⟩
  rw [mul_div_assoc]
  linarith

theorem errors_tendsto :
    Tendsto (fun n => connErr n + expErr n + roundErr n) atTop (nhds 0) := by
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ => 4 * exp 1 * exp (-(15 * Real.log n / 4))) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => 15 * Real.log n / 4) atTop atTop :=
      (hlogn.const_mul_atTop (by norm_num : (0 : ℝ) < 15)).atTop_div_const (by norm_num)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (4 * exp 1)
    simpa [Function.comp_def] using h2
  have hA : Tendsto connErr atTop (nhds 0) := by
    have h := hr.div (tendsto_const_nhds.sub hr) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    rw [sub_zero, div_one] at h
    exact h
  have hB : Tendsto expErr atTop (nhds 0) := by
    have h0 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h := h0.div (tendsto_const_nhds.sub h0) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    rw [sub_zero, div_one] at h
    exact h
  have hD : Tendsto roundErr atTop (nhds 0) := by
    have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1
      (by rw [abs_of_pos (by norm_num)]; norm_num : |(1 / 4 : ℝ)| < 1)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
    have h3 := (h1.add h2).const_mul (exp 1)
    simp only [pow_one, add_zero, mul_zero] at h3
    refine h3.congr fun n => ?_
    simp only [roundErr]
    ring
  simpa using (hA.add hB).add hD

/-- For all large `n`, the two-round exposure fails with probability at most the sum of the three
error terms. -/
theorem eventually_not_hamCycle_le : ∀ᶠ n : ℕ in atTop,
    gnpProb n (1 - (1 - 16 * Real.log n / n) * (1 - 64 * Real.log n / n))
        (fun G => ¬ HasHamCycle G) ≤ connErr n + expErr n + roundErr n := by
  filter_upwards [eventually_good] with n ⟨hn, hq, hr⟩
  set L := Real.log n with hL
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL1 : 1 < L := one_lt_log_of_four_le hn
  have hp₁0 : 0 ≤ 16 * L / n := by positivity
  have hp₂0 : 0 ≤ 64 * L / n := by positivity
  have hp₁1 : 16 * L / n ≤ 1 := by
    have : 16 * L / n ≤ 64 * L / n := div_le_div_of_nonneg_right (by linarith) hnpos.le
    linarith
  have hp₂1 : 64 * L / n ≤ 1 := by linarith
  have hk : 1 ≤ n / 4 := by omega
  refine (gnpProb_not_hamCycle_le n hp₁0 hp₁1 hp₂0 hp₂1 (δ := roundErr n) (by
    unfold roundErr; positivity) fun ω₁ hconn hexp =>
      (round_bound ω₁ hconn hexp hk hp₂0 hp₂1).trans (round_numeric hn hq)).trans ?_
  have hconn : gnpProb n (16 * L / n) (fun G => ¬ G.Connected) ≤ connErr n := by
    refine (gnpProb_not_connected_le (by omega) hp₁0 hp₁1).trans ?_
    refine disconnBound_le (by omega) (by positivity) hp₁0 hp₁1 (Or.inr ?_) hr
    rw [div_mul_cancel₀ _ hnpos.ne']
    linarith
  have hexp : gnpProb n (16 * L / n) (fun G => ¬ IsExpander G (n / 4)) ≤ expErr n := by
    have hrn : (n : ℝ) ^ 3 * exp (-(16 * L / n * n / 4)) = 1 / n := by
      rw [div_mul_cancel₀ _ hnpos.ne', show 16 * L / 4 = ((4 : ℕ) : ℝ) * L by push_cast; ring,
        Real.exp_neg, Real.exp_nat_mul, hL, Real.exp_log hnpos]
      field_simp
    have h1n : 1 / (n : ℝ) < 1 := by
      rw [div_lt_one hnpos]; exact_mod_cast (by omega : 1 < n)
    refine (gnpProb_not_expander_le hp₁0 hp₁1).trans ?_
    have := expanderBound_le (n := n) (by omega) hp₁0 hp₁1 (hrn ▸ h1n)
    rw [hrn] at this
    exact this
  linarith

/-- **Pósa (1976)**: there is `C > 0` such that for every `ε > 0` and all large `n`, `G(n, p)` is
Hamiltonian with probability at least `1 - ε` for every `p ∈ [C log n / n, 1]` (with `C = 80`). -/
theorem posa : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ p : ℝ, C * Real.log n / n ≤ p → p ≤ 1 →
    1 - ε ≤ gnpProb n p (fun G => G.IsHamiltonian) := by
  refine ⟨80, by norm_num, fun ε hε => ?_⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((errors_tendsto.eventually (gt_mem_nhds hε)).and
    (eventually_not_hamCycle_le.and eventually_good))
  refine ⟨n₀, fun n hn p hp hp1 => ?_⟩
  obtain ⟨herr, hfail, hn4, hq, -⟩ := hn₀ n hn
  set L := Real.log n with hL
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL1 : 1 < L := one_lt_log_of_four_le hn4
  set p₁ := 16 * L / n with hp₁
  set p₂ := 64 * L / n with hp₂
  have hp₁0 : 0 ≤ p₁ := by positivity
  have hp₂0 : 0 ≤ p₂ := by positivity
  have hp₁1 : p₁ ≤ 1 := by
    have : p₁ ≤ p₂ := div_le_div_of_nonneg_right (by linarith) hnpos.le
    linarith
  have hp₂1 : p₂ ≤ 1 := by linarith
  set p' := 1 - (1 - p₁) * (1 - p₂) with hp'
  have hp'0 : 0 ≤ p' := by nlinarith
  have hp'p : p' ≤ p := by
    have : p₁ + p₂ = 80 * L / n := by rw [hp₁, hp₂]; ring
    nlinarith
  have hP' := coin_isPMF hp'0 (hp'p.trans hp1) n
  have h3 : 3 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  calc 1 - ε ≤ 1 - gnpProb n p' (fun G => ¬ HasHamCycle G) := by linarith
    _ = gnpProb n p' (fun G => HasHamCycle G) := by
        unfold gnpProb
        rw [pProb_not hP' (fun ω => HasHamCycle (graphOf ω))]
        ring
    _ ≤ gnpProb n p' (fun G => G.IsHamiltonian) :=
        pProb_mono hP' fun ω h => HasHamCycle.isHamiltonian h h3
    _ ≤ gnpProb n p (fun G => G.IsHamiltonian) :=
        gnpProb_mono (fun G H hGH hG => hG.mono hGH) hp'0 hp'p hp1

end Pseudorandom.RandomGraphs
