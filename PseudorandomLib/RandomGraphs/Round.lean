/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Boosters
public import PseudorandomLib.RandomGraphs.Crossing

/-! # The sprinkling round

Fix a connected graph `G₁ = graphOf ω₁` on `Fin n` in which every set of at most `n / 4` vertices
expands by a factor two, and add an independent `G(n, q)`. If the union has no Hamiltonian cycle,
then (`exists_boost_closure`) some set `F` of at most `n` pairs is present in the second graph while
all boosters of `G₁ ∪ F` (at least `(n/4 + 1)² / 2` of them, by `booster_count`) are absent. The
union bound over `F` gives `round_bound`.
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open Finset Real

variable {n : ℕ}

theorem exists_eq_sym2_mk {V : Type*} (z : Sym2 V) : ∃ u v, z = s(u, v) := by
  induction z using Sym2.ind with
  | h u v => exact ⟨u, v, rfl⟩

theorem graphOf_or (ω₁ ω₂ : Pairs n → Bool) :
    graphOf (fun e => ω₁ e || ω₂ e) = graphOf ω₁ ⊔ graphOf ω₂ := by
  ext u v
  simp only [SimpleGraph.sup_adj, graphOf_adj, Bool.or_eq_true]
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact ⟨h, Or.inl h'⟩
    · exact ⟨h, Or.inr h'⟩

/-- The graph with edge set `F`. -/
def setGraph (F : Finset (Pairs n)) : SimpleGraph (Fin n) := graphOf fun e => decide (e ∈ F)

open Classical in
/-- The boosters of a graph, as potential edges. -/
noncomputable def boostPairs (Γ : SimpleGraph (Fin n)) : Finset (Pairs n) :=
  univ.filter fun e => e.1 ∈ boosterSet Γ

theorem card_boosterSet_le (Γ : SimpleGraph (Fin n)) :
    (boosterSet Γ).card ≤ (boostPairs Γ).card := by
  classical
  have : boosterSet Γ ⊆ (boostPairs Γ).map (Function.Embedding.subtype _) := by
    intro e he
    have he' := he
    simp only [boosterSet, mem_filter, mem_univ, true_and] at he'
    obtain ⟨u, v, rfl, hb⟩ := he'
    refine mem_map.2 ⟨⟨s(u, v), by simpa using hb.2.1⟩, ?_, rfl⟩
    simp [boostPairs, he]
  exact (card_le_card this).trans_eq (card_map _)

theorem disjoint_boostPairs (ω₁ : Pairs n → Bool) (F : Finset (Pairs n)) :
    Disjoint F (boostPairs (graphOf ω₁ ⊔ setGraph F)) := by
  classical
  rw [disjoint_left]
  intro e heF heB
  simp only [boostPairs, boosterSet, mem_filter, mem_univ, true_and] at heB
  obtain ⟨u, v, he, hb⟩ := heB
  apply hb.1
  rw [SimpleGraph.sup_adj]
  right
  rw [setGraph, graphOf_adj_iff _ e u v he]
  simpa using heF

theorem pProb_false {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (P : ι → α → ℝ) :
    pProb P (fun _ => False) = 0 := by
  simp [pProb, pE]

/-- One sprinkling round. -/
theorem round_bound (ω₁ : Pairs n → Bool) (hconn : (graphOf ω₁).Connected)
    (hexp : IsExpander (graphOf ω₁) (n / 4)) (hk : 1 ≤ n / 4) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    pProb (coin q n) (fun ω₂ => ¬ HasHamCycle (graphOf ω₁ ⊔ graphOf ω₂)) ≤
      ∑ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ n),
        q ^ F.card * (1 - q) ^ ((n / 4 + 1) ^ 2 / 2) := by
  classical
  have hP := coin_isPMF hq0 hq1 n
  set Γ : Finset (Pairs n) → SimpleGraph (Fin n) := fun F => graphOf ω₁ ⊔ setGraph F with hΓ
  have hwit : ∀ ω₂ : Pairs n → Bool, ¬ HasHamCycle (graphOf ω₁ ⊔ graphOf ω₂) →
      ∃ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ n),
        ¬ HasHamCycle (Γ F) ∧ ((∀ e ∈ F, ω₂ e = true) ∧ ∀ e ∈ boostPairs (Γ F), ω₂ e = false) := by
    intro ω₂ hH
    obtain ⟨F₀, hcard, hsub, hham, hboost⟩ := exists_boost_closure (graphOf ω₁) (graphOf ω₂) hH
    set F : Finset (Pairs n) := univ.filter fun e => e.1 ∈ F₀ with hFdef
    have hgraph : setGraph F = SimpleGraph.fromEdgeSet ↑F₀ := by
      ext u v
      simp only [setGraph, graphOf_adj, hFdef, mem_filter, mem_univ, true_and, decide_eq_true_eq,
        SimpleGraph.fromEdgeSet_adj, mem_coe]
      constructor
      · rintro ⟨h, h'⟩; exact ⟨h', h⟩
      · rintro ⟨h', h⟩; exact ⟨h, h'⟩
    have hΓF : Γ F = graphOf ω₁ ⊔ SimpleGraph.fromEdgeSet ↑F₀ := by rw [hΓ]; simp only [hgraph]
    refine ⟨F, mem_filter.2 ⟨mem_powerset.2 (subset_univ _), ?_⟩, hΓF ▸ hham, ?_, ?_⟩
    · refine le_trans ?_ (hcard.trans_eq (Fintype.card_fin n))
      refine card_le_card_of_injOn Subtype.val (fun e he => ?_) Subtype.val_injective.injOn
      simpa [hFdef] using he
    · intro e he
      have he' : e.1 ∈ F₀ := by simpa [hFdef] using he
      obtain ⟨u, v, huv⟩ := exists_eq_sym2_mk e.1
      have := hsub _ he'
      rw [huv, SimpleGraph.mem_edgeSet] at this
      exact (graphOf_adj_iff ω₂ e u v huv).1 this
    · intro e he
      simp only [boostPairs, boosterSet, mem_filter, mem_univ, true_and] at he
      obtain ⟨u, v, huv, hb⟩ := he
      rw [hΓF] at hb
      have := hboost u v hb
      rw [graphOf_adj_iff ω₂ e u v huv] at this
      simpa using this
  refine (pProb_mono hP fun ω₂ h => hwit ω₂ h).trans ?_
  refine (pProb_exists_le hP _ _).trans (sum_le_sum fun F hF => ?_)
  by_cases hham : HasHamCycle (Γ F)
  · rw [pProb_congr (T := fun _ => False) (fun ω => ⟨fun h => h.1 hham, False.elim⟩),
      pProb_false]
    positivity
  · rw [pProb_congr (T := fun ω => (∀ e ∈ F, ω e = true) ∧ ∀ e ∈ boostPairs (Γ F), ω e = false)
      (fun ω => ⟨fun h => h.2, fun h => ⟨hham, h⟩⟩),
      pProb_coin_present_absent hq0 hq1 _ _ (disjoint_boostPairs ω₁ F)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 _)
    refine pow_le_pow_of_le_one (by linarith) (by linarith) ?_
    have hle : graphOf ω₁ ≤ Γ F := le_sup_left
    have hcount : (n / 4 + 1) ^ 2 ≤ 2 * (boosterSet (graphOf ω₁ ⊔ setGraph F)).card :=
      booster_count hk (hexp.mono hle) (hconn.mono hle) hham
    have := card_boosterSet_le (graphOf ω₁ ⊔ setGraph F)
    exact Nat.div_le_of_le_mul (by omega)

theorem card_pairs_le (n : ℕ) : Fintype.card (Pairs n) ≤ n ^ 2 := by
  calc Fintype.card (Pairs n) ≤ Fintype.card (Sym2 (Fin n)) := Fintype.card_subtype_le _
    _ ≤ Fintype.card (Fin n × Fin n) :=
        Fintype.card_le_of_surjective (Function.uncurry Sym2.mk) Sym2.mk_surjective
    _ = n ^ 2 := by simp [sq]

/-- Counting the sets of at most `n` pairs, weighted by `q ^ |F|`. -/
theorem sum_small_sets_le {q : ℝ} (hq0 : 0 ≤ q) (hX : 1 ≤ (n : ℝ) ^ 2 * q) :
    ∑ F ∈ (univ : Finset (Pairs n)).powerset.filter (fun F => F.card ≤ n), q ^ F.card ≤
      (n + 1) * ((n : ℝ) ^ 2 * q) ^ n := by
  classical
  set N := Fintype.card (Pairs n) with hN
  have hNn : (N : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast card_pairs_le n
  rw [sum_filter]
  have h := sum_powerset_apply_card (fun m => if m ≤ n then q ^ m else 0)
    (x := (univ : Finset (Pairs n)))
  rw [h, card_univ, ← hN]
  calc ∑ m ∈ range (N + 1), N.choose m • (if m ≤ n then q ^ m else 0)
      ≤ ∑ m ∈ range (N + 1), if m ≤ n then ((n : ℝ) ^ 2 * q) ^ n else 0 := by
        refine sum_le_sum fun m _ => ?_
        rw [nsmul_eq_mul]
        split_ifs with hm
        · calc (N.choose m : ℝ) * q ^ m ≤ (N : ℝ) ^ m * q ^ m := by
                refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hq0 _)
                exact_mod_cast Nat.choose_le_pow N m
            _ ≤ ((n : ℝ) ^ 2) ^ m * q ^ m :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hNn _)
                  (pow_nonneg hq0 _)
            _ = ((n : ℝ) ^ 2 * q) ^ m := by rw [mul_pow]
            _ ≤ ((n : ℝ) ^ 2 * q) ^ n := pow_le_pow_right₀ hX hm
        · simp
    _ = ∑ m ∈ (range (N + 1)).filter (· ≤ n), ((n : ℝ) ^ 2 * q) ^ n := by rw [sum_filter]
    _ ≤ ∑ m ∈ range (n + 1), ((n : ℝ) ^ 2 * q) ^ n := by
        refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) (fun _ _ _ => by positivity)
        simp only [mem_filter, mem_range] at hm ⊢
        omega
    _ = (n + 1) * ((n : ℝ) ^ 2 * q) ^ n := by simp

end Pseudorandom.RandomGraphs
