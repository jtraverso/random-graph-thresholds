/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Connectivity

/-! # Isolated vertices and disconnectedness below `(log n - ω) / n`

The second moment method for the number `X` of isolated vertices: with
`μ = E X = n (1 - p)^{n - 1}`, `P(X = 0) ≤ Var X / μ² ≤ 1 / μ + (1 - p)^{-2} - 1`
(`gnpProb_connected_le`). A connected graph on at least two vertices has no isolated vertex.
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open Finset Real Filter

variable {n : ℕ}

/-- `v` is an isolated vertex of `G`. -/
def IsIsolated (G : SimpleGraph (Fin n)) (v : Fin n) : Prop := ∀ b ∈ univ \ {v}, ¬ G.Adj v b

theorem gnpProb_isIsolated {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) :
    gnpProb n p (fun G => IsIsolated G v) = (1 - p) ^ (n - 1) := by
  have h := gnpProb_noCross hp0 hp1 (Finset.disjoint_sdiff : Disjoint {v} (univ \ {v}))
  rw [Finset.card_singleton, one_mul, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine pProb_congr fun ω => ?_
  simp [IsIsolated]

theorem gnpProb_isIsolated_pair_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {u v : Fin n}
    (huv : u ≠ v) :
    gnpProb n p (fun G => IsIsolated G u ∧ IsIsolated G v) ≤ (1 - p) ^ (2 * (n - 2)) := by
  have h := gnpProb_noCross hp0 hp1 (Finset.disjoint_sdiff : Disjoint {u, v} (univ \ {u, v}))
  rw [Finset.card_pair huv, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_pair huv, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine pProb_mono (coin_isPMF hp0 hp1 n) fun ω hω a ha b hb => ?_
  have hb' : b ∉ ({u, v} : Finset (Fin n)) := (Finset.mem_sdiff.1 hb).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb'
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact hω.1 b (by simpa using hb'.1)
  · exact hω.2 b (by simpa using hb'.2)

theorem not_isIsolated_of_connected {G : SimpleGraph (Fin n)} (hn : 2 ≤ n) (hG : G.Connected)
    (v : Fin n) : ¬ IsIsolated G v := by
  intro hv
  obtain ⟨w, hw⟩ : ∃ w : Fin n, w ≠ v := by
    by_cases h : v = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
  obtain ⟨p⟩ := hG.preconnected v w
  cases p with
  | nil => exact hw rfl
  | cons h _ =>
    exact hv _ (by simp [G.ne_of_adj h |>.symm]) h

/-- Second moment bound: `P(G(n, p) connected) ≤ 1 / μ + (1 - p)^{-2} - 1`, where
`μ = n (1 - p)^{n - 1}` is the expected number of isolated vertices. -/
theorem gnpProb_connected_le (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    gnpProb n p (fun G => G.Connected) ≤
      1 / (n * (1 - p) ^ (n - 1)) + (1 / (1 - p) ^ 2 - 1) := by
  classical
  have hP := coin_isPMF hp0 hp1.le n
  have h1p : 0 < 1 - p := by linarith
  set μ : ℝ := n * (1 - p) ^ (n - 1) with hμ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hμpos : 0 < μ := mul_pos hnpos (pow_pos h1p _)
  set I : Fin n → (Pairs n → Bool) → ℝ :=
    fun v ω => if IsIsolated (graphOf ω) v then 1 else 0 with hI
  set X : (Pairs n → Bool) → ℝ := fun ω => ∑ v, I v ω with hX
  have hEI : ∀ v, pE (coin p n) (I v) = (1 - p) ^ (n - 1) := fun v =>
    gnpProb_isIsolated hp0 hp1.le v
  have hEX : pE (coin p n) X = μ := by
    rw [hX, pE_sum]
    simp [hEI, hμ]
  have hII : ∀ u v ω, I u ω * I v ω =
      if IsIsolated (graphOf ω) u ∧ IsIsolated (graphOf ω) v then 1 else 0 := by
    intro u v ω
    by_cases hu : IsIsolated (graphOf ω) u <;> by_cases hv : IsIsolated (graphOf ω) v <;>
      simp [hI, hu, hv]
  have hEII : ∀ u v, u ≠ v → pE (coin p n) (fun ω => I u ω * I v ω) ≤
      (1 - p) ^ (2 * (n - 2)) := by
    intro u v huv
    have := gnpProb_isIsolated_pair_le hp0 hp1.le huv
    unfold gnpProb at this
    rwa [pProb_eq_pE _ (fun ω => I u ω * I v ω) (fun ω h => by simp [hII, h])
      (fun ω h => by simp [hII, h])] at this
  have hEX2 : pE (coin p n) (fun ω => X ω ^ 2) ≤
      μ + n * (n - 1) * (1 - p) ^ (2 * (n - 2)) := by
    have hsq : (fun ω => X ω ^ 2) = fun ω => ∑ u, ∑ v, I u ω * I v ω := by
      funext ω; rw [hX, sq, Finset.sum_mul_sum]
    rw [hsq, pE_sum]
    simp_rw [pE_sum]
    have hrow : ∀ u, ∑ v, pE (coin p n) (fun ω => I u ω * I v ω) ≤
        (1 - p) ^ (n - 1) + (n - 1) * (1 - p) ^ (2 * (n - 2)) := by
      intro u
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
      have hself : pE (coin p n) (fun ω => I u ω * I u ω) = (1 - p) ^ (n - 1) := by
        rw [← hEI u]
        congr 1; funext ω
        by_cases hu : IsIsolated (graphOf ω) u <;> simp [hI, hu]
      rw [hself]
      have : ∑ v ∈ univ.erase u, pE (coin p n) (fun ω => I u ω * I v ω) ≤
          ∑ v ∈ univ.erase u, (1 - p) ^ (2 * (n - 2)) :=
        Finset.sum_le_sum fun v hv => hEII u v (Finset.ne_of_mem_erase hv).symm
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)] at this
      push_cast at this
      linarith
    calc ∑ u, ∑ v, pE (coin p n) (fun ω => I u ω * I v ω)
        ≤ ∑ _u : Fin n, ((1 - p) ^ (n - 1) + (n - 1) * (1 - p) ^ (2 * (n - 2))) :=
          Finset.sum_le_sum fun u _ => hrow u
      _ = μ + n * (n - 1) * (1 - p) ^ (2 * (n - 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hμ]; ring
  have hVar : pE (coin p n) (fun ω => (X ω - μ) ^ 2) =
      pE (coin p n) (fun ω => X ω ^ 2) - μ ^ 2 := by
    have : (fun ω => (X ω - μ) ^ 2) = fun ω => (X ω ^ 2 + (-2 * μ) * X ω) + μ ^ 2 := by
      funext ω; ring
    rw [this, pE_add, pE_add, pE_const_mul, pE_const hP, hEX]
    ring
  have hconn : ∀ ω, (graphOf ω).Connected → μ ^ 2 ≤ (X ω - μ) ^ 2 := by
    intro ω hω
    have : X ω = 0 := by
      rw [hX]
      refine Finset.sum_eq_zero fun v _ => ?_
      simp [hI, not_isIsolated_of_connected hn hω v]
    rw [this]; nlinarith
  have hmarkov := pProb_ge_le_markov hP (f := fun ω => (X ω - μ) ^ 2) (fun ω => sq_nonneg _)
    (pow_pos hμpos 2)
  have hpow : (1 - p) ^ (n - 1) = (1 - p) ^ (n - 2) * (1 - p) := by
    rw [← pow_succ]; congr 1; omega
  have hμ2 : μ ^ 2 = (n : ℝ) ^ 2 * (1 - p) ^ (2 * (n - 2)) * (1 - p) ^ 2 := by
    rw [hμ, hpow, mul_comm 2 (n - 2), pow_mul]; ring
  calc gnpProb n p (fun G => G.Connected)
      ≤ pProb (coin p n) (fun ω => μ ^ 2 ≤ (X ω - μ) ^ 2) :=
        pProb_mono hP fun ω h => hconn ω h
    _ ≤ pE (coin p n) (fun ω => (X ω - μ) ^ 2) / μ ^ 2 := hmarkov
    _ ≤ (μ + n * (n - 1) * (1 - p) ^ (2 * (n - 2)) - μ ^ 2) / μ ^ 2 := by
        rw [hVar]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ 1 / μ + (1 / (1 - p) ^ 2 - 1) := by
        have hA : 0 < (1 - p) ^ (2 * (n - 2)) := pow_pos h1p _
        have hB : 0 < (1 - p) ^ 2 := pow_pos h1p _
        rw [div_le_iff₀ (by positivity)]
        have hkey : (n : ℝ) * (n - 1) * (1 - p) ^ (2 * (n - 2)) ≤
            μ ^ 2 * (1 / (1 - p) ^ 2) := by
          rw [hμ2]
          field_simp
          nlinarith
        have : 1 / μ * μ ^ 2 = μ := by field_simp
        nlinarith

/-- Lower bound on the expected number of isolated vertices:
`n (1 - p)^{n - 1} ≥ exp(log n - n p - 2 n p²)` for `0 ≤ p ≤ 1/2`. -/
theorem exp_le_isolated_mean (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    exp (Real.log n - n * p - 2 * n * p ^ 2) ≤ n * (1 - p) ^ (n - 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1p : 0 < 1 - p := by linarith
  have hlog : -p - 2 * p ^ 2 ≤ Real.log (1 - p) := by
    have h := Real.one_sub_inv_le_log_of_pos h1p
    have : -p - 2 * p ^ 2 ≤ 1 - (1 - p)⁻¹ := by
      rw [show 1 - (1 - p)⁻¹ = -p / (1 - p) by field_simp; ring, le_div_iff₀ h1p]
      nlinarith
    linarith
  have hpow : (1 - p) ^ n ≤ (1 - p) ^ (n - 1) :=
    pow_le_pow_of_le_one h1p.le (by linarith) (Nat.sub_le n 1)
  have hexp : exp (n * (-p - 2 * p ^ 2)) ≤ (1 - p) ^ n := by
    calc exp (n * (-p - 2 * p ^ 2)) ≤ exp (n * Real.log (1 - p)) :=
          exp_le_exp.2 (mul_le_mul_of_nonneg_left hlog hnpos.le)
      _ = (1 - p) ^ n := by rw [← Real.log_pow, Real.exp_log (pow_pos h1p _)]
  calc exp (Real.log n - n * p - 2 * n * p ^ 2) = n * exp (n * (-p - 2 * p ^ 2)) := by
        rw [show Real.log n - n * p - 2 * n * p ^ 2 = Real.log n + n * (-p - 2 * p ^ 2) by ring,
          Real.exp_add, Real.exp_log hnpos]
    _ ≤ n * (1 - p) ^ (n - 1) :=
        mul_le_mul_of_nonneg_left (hexp.trans hpow) hnpos.le

/-- **Erdős–Rényi (1959)**, lower side: for `p = (log n - ω(n)) / n` with `ω → ∞`, `G(n, p)` is
connected with probability tending to `0` (it has isolated vertices w.h.p.). -/
theorem not_connected_of_log_sub (ω : ℕ → ℝ) (hω : Tendsto ω atTop atTop) :
    Tendsto (fun n : ℕ => gnpProb n (max 0 ((Real.log n - ω n) / n)) (fun G => G.Connected))
      atTop (nhds 0) := by
  set p : ℕ → ℝ := fun n => max 0 ((Real.log n - ω n) / n) with hpdef
  have hL : Tendsto (fun n : ℕ => Real.log n / n) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hL2 : Tendsto (fun n : ℕ => Real.log n ^ 2 / n) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- eventually `0 ≤ p n ≤ log n / n`
  have hp_le : ∀ᶠ n : ℕ in atTop, 0 ≤ p n ∧ p n ≤ Real.log n / n := by
    filter_upwards [hω.eventually_ge_atTop 0, eventually_ge_atTop 1] with n h1 h2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h2
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast h2)
    refine ⟨le_max_left _ _, max_le (div_nonneg hlog0 hnpos.le) ?_⟩
    exact div_le_div_of_nonneg_right (by linarith) hnpos.le
  have hp : Tendsto p atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL ?_ ?_
    · filter_upwards [hp_le] with n h using h.1
    · filter_upwards [hp_le] with n h using h.2
  -- the exponent in the lower bound on the mean tends to infinity
  set E : ℕ → ℝ := fun n => min (Real.log n) (ω n) - 2 * (Real.log n ^ 2 / n) with hEdef
  have hE : Tendsto E atTop atTop := by
    have hmin : Tendsto (fun n => min (Real.log (n : ℕ)) (ω n)) atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [hlogn.eventually_ge_atTop b, hω.eventually_ge_atTop b] with n h1 h2
      exact le_min h1 h2
    have h2 : Tendsto (fun n : ℕ => 2 * (Real.log n ^ 2 / n)) atTop (nhds 0) := by
      simpa using hL2.const_mul 2
    exact hmin.atTop_add (by simpa using h2.neg) |>.congr fun n => by simp [hEdef, sub_eq_add_neg]
  set μ : ℕ → ℝ := fun n => (n : ℝ) * (1 - p n) ^ (n - 1) with hμdef
  have hμ : Tendsto μ atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (Real.tendsto_exp_atTop.comp hE)
    filter_upwards [hp_le, hp.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_ge_atTop 1, hω.eventually_ge_atTop 0] with n hpn hp2 hn hωn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    refine le_trans ?_ (exp_le_isolated_mean hn hpn.1 hp2)
    refine exp_le_exp.2 ?_
    have h1 : min (Real.log n) (ω n) ≤ Real.log n - n * p n := by
      rcases le_or_gt (Real.log n - ω n) 0 with h | h
      · have : p n = 0 := by
          simp only [hpdef]
          exact max_eq_left (div_nonpos_of_nonpos_of_nonneg h hnpos.le)
        rw [this]; simp
      · have : p n = (Real.log n - ω n) / n := by
          simp only [hpdef]
          exact max_eq_right (div_nonneg h.le hnpos.le)
        rw [this, mul_div_cancel₀ _ hnpos.ne']
        have := min_le_right (Real.log n) (ω n)
        linarith
    have h2 : n * p n ^ 2 ≤ Real.log n ^ 2 / n := by
      rw [le_div_iff₀ hnpos]
      have : n * p n ≤ Real.log n := by rw [le_div_iff₀ hnpos] at hpn; linarith
      have : 0 ≤ n * p n := mul_nonneg hnpos.le hpn.1
      nlinarith
    simp only [hEdef]
    nlinarith
  -- the second moment bound tends to zero
  have hbound : Tendsto (fun n => 1 / μ n + (1 / (1 - p n) ^ 2 - 1)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => 1 / μ n) atTop (nhds 0) := by
      simpa [Pi.inv_def] using hμ.inv_tendsto_atTop
    have h2 : Tendsto (fun n => 1 / (1 - p n) ^ 2 - 1) atTop (nhds 0) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).pow 2
      have h' := (tendsto_const_nhds (x := (1 : ℝ))).div h (by norm_num)
      simpa using h'.sub_const 1
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
  · filter_upwards [hp_le, hp.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with n hpn hp2
    exact pProb_nonneg (coin_isPMF hpn.1 (by linarith) n) _
  · filter_upwards [hp_le, hp.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_ge_atTop 2] with n hpn hp2 hn
    exact gnpProb_connected_le hn hpn.1 (by linarith)

end Pseudorandom.RandomGraphs
