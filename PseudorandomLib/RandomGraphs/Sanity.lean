/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Crossing

/-! # Sanity checks of the model on tiny `n`

`G(2, 1)` is the single edge, hence connected; `G(2, 0)` is empty, hence disconnected.
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open Finset

theorem graphOf_true_connected : (graphOf (fun _ : Pairs 2 => true)).Connected := by
  have hadj : (graphOf (fun _ : Pairs 2 => true)).Adj 0 1 := by
    rw [graphOf_adj]; exact ⟨by decide, rfl⟩
  refine (SimpleGraph.connected_iff _).2 ⟨fun u v => ?_, ⟨0⟩⟩
  fin_cases u <;> fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact hadj.reachable
  · exact hadj.symm.reachable
  · exact SimpleGraph.Reachable.refl _

theorem graphOf_false_not_connected : ¬ (graphOf (fun _ : Pairs 2 => false)).Connected := by
  have hbot : graphOf (fun _ : Pairs 2 => false) = ⊥ := by
    ext u v; simp [graphOf_adj]
  rw [hbot]
  intro h
  have := SimpleGraph.reachable_bot.1 (h.preconnected (0 : Fin 2) 1)
  exact absurd this (by decide)

/-- `P(G(2, 1) is connected) = 1`. -/
theorem gnpProb_two_one_connected : gnpProb 2 1 (fun G => G.Connected) = 1 := by
  have hP := coin_isPMF (zero_le_one' ℝ) le_rfl 2
  have h := pProb_coin_present_absent (zero_le_one' ℝ) le_rfl (univ : Finset (Pairs 2)) ∅
    (disjoint_empty_right _)
  simp only [one_pow, card_empty, pow_zero, mul_one, notMem_empty, IsEmpty.forall_iff,
    implies_true, and_true] at h
  refine le_antisymm (pProb_le_one hP _) (h.symm.le.trans (pProb_mono hP fun ω hω => ?_))
  have : ω = fun _ => true := funext fun e => hω e (mem_univ e)
  rw [this]
  exact graphOf_true_connected

/-- `P(G(2, 0) is connected) = 0`. -/
theorem gnpProb_two_zero_connected : gnpProb 2 0 (fun G => G.Connected) = 0 := by
  have hP := coin_isPMF le_rfl (zero_le_one' ℝ) 2
  have h := pProb_coin_present_absent le_rfl (zero_le_one' ℝ) ∅ (univ : Finset (Pairs 2))
    (disjoint_empty_left _)
  simp only [card_empty, pow_zero, sub_zero, one_pow, one_mul, notMem_empty,
    IsEmpty.forall_iff, implies_true, true_and] at h
  have hnot := pProb_not hP (fun ω => ∀ e ∈ (univ : Finset (Pairs 2)), ω e = false)
  rw [h, sub_self] at hnot
  refine le_antisymm ?_ (pProb_nonneg hP _)
  refine (pProb_mono hP fun ω hω hall => ?_).trans hnot.le
  have : ω = fun _ => false := funext fun e => hall e (mem_univ e)
  rw [this] at hω
  exact graphOf_false_not_connected hω

end Pseudorandom.RandomGraphs
