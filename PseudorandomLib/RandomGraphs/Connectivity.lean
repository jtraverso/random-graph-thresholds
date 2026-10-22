/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Crossing

/-! # Connectivity of `G(n, p)` above `(log n + ω) / n`

A disconnected graph on `n` vertices has a vertex set `S` with `1 ≤ |S| ≤ n / 2` and no edges
leaving it (`exists_cut_of_not_connected`). The union bound gives
`P(G(n, p) disconnected) ≤ ∑_{s=1}^{n/2} C(n, s) (1 - p)^{s (n - s)}` (`gnpProb_not_connected_le`),
and for `p n ≥ log n + ω` every summand is at most `(4 e · e^{-ω/4})^s`
(`disconnBound_term_le`).
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open Finset Real Filter

/-- A disconnected graph on `Fin n` has a nonempty set of at most `n / 2` vertices with no edge
leaving it. -/
theorem exists_cut_of_not_connected {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (hG : ¬ G.Connected) :
    ∃ s ∈ Icc 1 (n / 2), ∃ S ∈ powersetCard s (univ : Finset (Fin n)),
      ∀ a ∈ S, ∀ b ∈ univ \ S, ¬ G.Adj a b := by
  classical
  have hpre : ¬ G.Preconnected := fun h =>
    hG ((SimpleGraph.connected_iff G).2 ⟨h, ⟨⟨0, hn⟩⟩⟩)
  unfold SimpleGraph.Preconnected at hpre
  push Not at hpre
  obtain ⟨u, v, huv⟩ := hpre
  set C : Finset (Fin n) := univ.filter (G.Reachable u) with hC
  have hclosed : ∀ a ∈ C, ∀ b, b ∉ C → ¬ G.Adj a b := by
    intro a ha b hb hab
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hb (ha.trans hab.reachable)
  have huC : u ∈ C := by simp [hC]
  have hvC : v ∉ C := by simp [hC, huv]
  have hcardC : C.card + (univ \ C).card = n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have := Finset.card_le_univ C
    simp only [Fintype.card_fin] at this
    omega
  by_cases h2 : 2 * C.card ≤ n
  · refine ⟨C.card, ?_, C, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩, ?_⟩
    · have : 1 ≤ C.card := Finset.card_pos.2 ⟨u, huC⟩
      simp only [Finset.mem_Icc]
      exact ⟨this, (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)⟩
    · intro a ha b hb
      exact hclosed a ha b (Finset.mem_sdiff.1 hb).2
  · refine ⟨(univ \ C).card, ?_, univ \ C,
      Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩, ?_⟩
    · have : 1 ≤ (univ \ C).card := Finset.card_pos.2 ⟨v, by simp [hvC]⟩
      simp only [Finset.mem_Icc]
      exact ⟨this, (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)⟩
    · intro a ha b hb
      have hb' : b ∈ C := by simpa using hb
      have ha' : a ∉ C := (Finset.mem_sdiff.1 ha).2
      exact fun hab => hclosed b hb' a ha' hab.symm

/-- The first moment bound for disconnectedness. -/
noncomputable def disconnBound (n : ℕ) (p : ℝ) : ℝ :=
  ∑ s ∈ Icc 1 (n / 2), (n.choose s : ℝ) * (1 - p) ^ (s * (n - s))

theorem gnpProb_not_connected_le {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    gnpProb n p (fun G => ¬ G.Connected) ≤ disconnBound n p := by
  have hP := coin_isPMF hp0 hp1 n
  unfold gnpProb
  calc pProb (coin p n) (fun ω => ¬ (graphOf ω).Connected)
      ≤ pProb (coin p n) (fun ω => ∃ s ∈ Icc 1 (n / 2),
          ∃ S ∈ powersetCard s (univ : Finset (Fin n)),
            ∀ a ∈ S, ∀ b ∈ univ \ S, ¬ (graphOf ω).Adj a b) :=
        pProb_mono hP fun ω h => exists_cut_of_not_connected hn _ h
    _ ≤ ∑ s ∈ Icc 1 (n / 2), pProb (coin p n) (fun ω =>
          ∃ S ∈ powersetCard s (univ : Finset (Fin n)),
            ∀ a ∈ S, ∀ b ∈ univ \ S, ¬ (graphOf ω).Adj a b) := pProb_exists_le hP _ _
    _ ≤ ∑ s ∈ Icc 1 (n / 2), ∑ S ∈ powersetCard s (univ : Finset (Fin n)),
          pProb (coin p n) (fun ω => ∀ a ∈ S, ∀ b ∈ univ \ S, ¬ (graphOf ω).Adj a b) :=
        Finset.sum_le_sum fun s _ => pProb_exists_le hP _ _
    _ = disconnBound n p := by
        unfold disconnBound
        refine Finset.sum_congr rfl fun s _ => ?_
        have : ∀ S ∈ powersetCard s (univ : Finset (Fin n)),
            pProb (coin p n) (fun ω => ∀ a ∈ S, ∀ b ∈ univ \ S, ¬ (graphOf ω).Adj a b) =
              (1 - p) ^ (s * (n - s)) := by
          intro S hS
          have hS := Finset.mem_powersetCard.1 hS
          have h := gnpProb_noCross hp0 hp1 (Finset.disjoint_sdiff : Disjoint S (univ \ S))
          unfold gnpProb at h
          rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
            Fintype.card_fin, hS.2]
        rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `x e^{-x/2} ≤ 4 e^{-x/4}`. -/
theorem mul_exp_neg_half_le (x : ℝ) : x * exp (-(x / 2)) ≤ 4 * exp (-(x / 4)) := by
  have h1 : x / 4 + 1 ≤ exp (x / 4) := add_one_le_exp _
  have h2 : exp (-(x / 2)) = exp (-(x / 4)) * exp (-(x / 4)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : exp (x / 4) * exp (-(x / 4)) = 1 := by rw [← Real.exp_add]; simp
  have hpos := exp_pos (-(x / 4))
  rw [h2]
  have : x * exp (-(x / 4)) ≤ 4 := by nlinarith
  nlinarith

/-- `C(n, s) ≤ (e n / s)^s`. -/
theorem choose_le_exp_mul_div_pow (n s : ℕ) (hs : 1 ≤ s) :
    (n.choose s : ℝ) ≤ (exp 1 * n / s) ^ s := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 := Nat.choose_le_pow_div (α := ℝ) s n
  have h2 := Real.pow_div_factorial_le_exp (s : ℝ) hspos.le s
  have hf : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have hss : (0 : ℝ) < (s : ℝ) ^ s := by positivity
  calc (n.choose s : ℝ) ≤ (n : ℝ) ^ s / s.factorial := h1
    _ ≤ (n : ℝ) ^ s * (exp 1 ^ s / (s : ℝ) ^ s) := by
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.exp_nat_mul, mul_one, inv_le_comm₀ hf (by positivity), inv_div,
          div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hf] at h2
        linarith
    _ = (exp 1 * n / s) ^ s := by rw [div_pow, mul_pow]; ring

/-- Each summand of `disconnBound` is geometrically small when `p n ≥ log n + ω`. -/
theorem disconnBound_term_le {n : ℕ} (hn : 1 ≤ n) {ω q : ℝ} (hω : 0 ≤ ω) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hq : Real.log n + ω ≤ q * n) {s : ℕ} (hs1 : 1 ≤ s) (hs2 : 2 * s ≤ n) :
    (n.choose s : ℝ) * (1 - q) ^ (s * (n - s)) ≤ (4 * exp 1 * exp (-(ω / 4))) ^ s := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs1
  have hns : ((n - s : ℕ) : ℝ) = n - s := by rw [Nat.cast_sub (by omega)]
  have hs2' : (2 : ℝ) * s ≤ n := by exact_mod_cast hs2
  have hpow : (1 - q) ^ (s * (n - s)) ≤ exp (-(q * (n - s))) ^ s := by
    rw [mul_comm, pow_mul]
    refine pow_le_pow_left₀ (pow_nonneg (by linarith) _) ?_ s
    calc (1 - q) ^ (n - s) ≤ exp (-q) ^ (n - s) :=
          pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-q)]) _
      _ = exp (-(q * (n - s))) := by rw [← Real.exp_nat_mul, hns]; ring_nf
  have hlog : n * exp (-(q * n)) ≤ exp (-ω) := by
    calc (n : ℝ) * exp (-(q * n)) = exp (Real.log n - q * n) := by
          rw [Real.exp_sub, Real.exp_log hnpos, Real.exp_neg, div_eq_mul_inv]
      _ ≤ exp (-ω) := exp_le_exp.2 (by linarith)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hr1 : exp (-ω) * exp 1 ≤ 4 * exp 1 * exp (-(ω / 4)) := by
    have : exp (-ω) ≤ exp (-(ω / 4)) := exp_le_exp.2 (by linarith)
    nlinarith [exp_pos 1, exp_pos (-(ω / 4))]
  rcases le_or_gt (q * s) 1 with hA | hB
  · -- few vertices: `C(n, s) ≤ n ^ s`
    calc (n.choose s : ℝ) * (1 - q) ^ (s * (n - s))
        ≤ (n : ℝ) ^ s * exp (-(q * (n - s))) ^ s := by
          refine mul_le_mul (by exact_mod_cast Nat.choose_le_pow n s) hpow
            (pow_nonneg (by linarith) _) (by positivity)
      _ = (n * exp (-(q * (n - s)))) ^ s := by rw [mul_pow]
      _ ≤ (4 * exp 1 * exp (-(ω / 4))) ^ s := by
          refine pow_le_pow_left₀ (by positivity) ?_ s
          calc (n : ℝ) * exp (-(q * (n - s))) = n * exp (-(q * n)) * exp (q * s) := by
                rw [mul_assoc, ← Real.exp_add]; ring_nf
            _ ≤ exp (-ω) * exp 1 :=
                mul_le_mul hlog (exp_le_exp.2 hA) (exp_pos _).le (exp_pos _).le
            _ ≤ _ := hr1
  · -- many vertices: `C(n, s) ≤ (e n / s) ^ s` and `n / s < q n`
    calc (n.choose s : ℝ) * (1 - q) ^ (s * (n - s))
        ≤ (exp 1 * n / s) ^ s * exp (-(q * (n - s))) ^ s := by
          refine mul_le_mul (choose_le_exp_mul_div_pow n s hs1) hpow
            (pow_nonneg (by linarith) _) (by positivity)
      _ = (exp 1 * n / s * exp (-(q * (n - s)))) ^ s := by rw [mul_pow]
      _ ≤ (4 * exp 1 * exp (-(ω / 4))) ^ s := by
          refine pow_le_pow_left₀ (by positivity) ?_ s
          have hx : (n : ℝ) / s ≤ q * n := by
            rw [div_le_iff₀ hspos]; nlinarith
          have he1 : exp (-(q * (n - s))) ≤ exp (-(q * n / 2)) :=
            exp_le_exp.2 (by nlinarith)
          have hqn : ω ≤ q * n := by linarith
          calc exp 1 * n / s * exp (-(q * (n - s)))
              = exp 1 * (n / s) * exp (-(q * (n - s))) := by ring
            _ ≤ exp 1 * (q * n) * exp (-(q * n / 2)) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left hx (exp_pos 1).le) he1
                  (exp_pos _).le (by positivity)
            _ = exp 1 * ((q * n) * exp (-((q * n) / 2))) := by ring
            _ ≤ exp 1 * (4 * exp (-((q * n) / 4))) :=
                mul_le_mul_of_nonneg_left (mul_exp_neg_half_le _) (exp_pos 1).le
            _ ≤ 4 * exp 1 * exp (-(ω / 4)) := by
                have : exp (-((q * n) / 4)) ≤ exp (-(ω / 4)) := exp_le_exp.2 (by linarith)
                nlinarith [exp_pos 1]

/-- The disconnection bound when `p n ≥ log n + ω` (or `p = 1`). -/
theorem disconnBound_le {n : ℕ} (hn : 1 ≤ n) {ω q : ℝ} (hω : 0 ≤ ω) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hq : q = 1 ∨ Real.log n + ω ≤ q * n)
    (hr : 4 * exp 1 * exp (-(ω / 4)) < 1) :
    disconnBound n q ≤ 4 * exp 1 * exp (-(ω / 4)) / (1 - 4 * exp 1 * exp (-(ω / 4))) := by
  set r := 4 * exp 1 * exp (-(ω / 4)) with hrdef
  have hr0 : 0 ≤ r := by positivity
  rcases hq with hq | hq
  · have : disconnBound n q = 0 := by
      unfold disconnBound
      refine Finset.sum_eq_zero fun s hs => ?_
      have hs := Finset.mem_Icc.1 hs
      have h2 : 2 * s ≤ n := by
        have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 hs.2; omega
      rw [hq, sub_self, zero_pow (Nat.mul_pos (by omega) (by omega)).ne', mul_zero]
    rw [this]
    exact div_nonneg hr0 (by linarith)
  · unfold disconnBound
    calc ∑ s ∈ Icc 1 (n / 2), (n.choose s : ℝ) * (1 - q) ^ (s * (n - s))
        ≤ ∑ s ∈ Icc 1 (n / 2), r ^ s := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hs := Finset.mem_Icc.1 hs
          have h2 : 2 * s ≤ n := by
            have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 hs.2; omega
          exact disconnBound_term_le hn hω hq0 hq1 hq hs.1 h2
      _ = ∑ s ∈ Ico 1 (n / 2 + 1), r ^ s := rfl
      _ ≤ r ^ 1 / (1 - r) := geom_sum_Ico_le_of_lt_one hr0 hr
      _ = r / (1 - r) := by rw [pow_one]

/-- **Erdős–Rényi (1959)**, upper side: for `p = (log n + ω(n)) / n` with `ω → ∞`, `G(n, p)` is
connected with probability tending to `1`. -/
theorem connected_of_log_add (ω : ℕ → ℝ) (hω : Tendsto ω atTop atTop) :
    Tendsto (fun n : ℕ => gnpProb n (min 1 ((Real.log n + ω n) / n)) (fun G => G.Connected))
      atTop (nhds 1) := by
  set r : ℕ → ℝ := fun n => 4 * exp 1 * exp (-(ω n / 4)) with hrdef
  have hr : Tendsto r atTop (nhds 0) := by
    have h1 : Tendsto (fun n => ω n / 4) atTop atTop :=
      hω.atTop_div_const (by norm_num)
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := h2.const_mul (4 * exp 1)
    simpa [hrdef, Function.comp_def] using h3
  have hlow : Tendsto (fun n => 1 - r n / (1 - r n)) atTop (nhds 1) := by
    have : Tendsto (fun n => r n / (1 - r n)) atTop (nhds 0) := by
      have h := hr.div (tendsto_const_nhds.sub hr) (by norm_num : (1 : ℝ) - 0 ≠ 0)
      rw [sub_zero, div_one] at h
      exact h
    simpa using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · have hev1 : ∀ᶠ n in atTop, 0 ≤ ω n := hω.eventually_ge_atTop 0
    have hev2 : ∀ᶠ n in atTop, r n < 1 := hr.eventually (gt_mem_nhds (by norm_num))
    have hev3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    filter_upwards [hev1, hev2, hev3] with n h1 h2 h3
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h3
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast h3)
    set q := min 1 ((Real.log n + ω n) / n) with hqdef
    have hq0 : 0 ≤ q := le_min zero_le_one (div_nonneg (by linarith) hnpos.le)
    have hq1 : q ≤ 1 := min_le_left _ _
    have hq : q = 1 ∨ Real.log n + ω n ≤ q * n := by
      rcases min_choice 1 ((Real.log n + ω n) / n) with h | h
      · exact Or.inl (hqdef ▸ h)
      · right; rw [hqdef, h, div_mul_cancel₀ _ hnpos.ne']
    have hb := disconnBound_le h3 h1 hq0 hq1 hq h2
    have hc := gnpProb_not_connected_le h3 hq0 hq1
    have hnot : gnpProb n q (fun G => ¬ G.Connected) = 1 - gnpProb n q (fun G => G.Connected) :=
      pProb_not (coin_isPMF hq0 hq1 n) _
    rw [hnot] at hc
    change 1 - r n / (1 - r n) ≤ gnpProb n q (fun G => G.Connected)
    linarith
  · filter_upwards [eventually_ge_atTop 1, hω.eventually_ge_atTop 0] with n h3 h1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast h3
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast h3)
    exact pProb_le_one (coin_isPMF (le_min zero_le_one (div_nonneg (by linarith) hnpos.le))
      (min_le_left _ _) n) _

end Pseudorandom.RandomGraphs
