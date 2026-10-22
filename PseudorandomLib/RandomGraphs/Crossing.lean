/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Coupling

/-! # Cylinder events in `G(n, p)`

* `pProb_coin_present_absent`: prescribed present and absent edges.
* `gnpProb_noCross`: no edges between two disjoint vertex sets `A`, `B` has probability
  `(1 - p) ^ (|A| * |B|)`.
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open Finset

variable {n : ℕ}

/-- Prescribed present edges `F` and absent edges `B` (disjoint). -/
theorem pProb_coin_present_absent {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F B : Finset (Pairs n))
    (hFB : Disjoint F B) :
    pProb (coin p n) (fun ω => (∀ e ∈ F, ω e = true) ∧ ∀ e ∈ B, ω e = false) =
      p ^ F.card * (1 - p) ^ B.card := by
  classical
  have h := pProb_cylinder (coin_isPMF hp0 hp1 n) (F ∪ B) (fun e => decide (e ∈ F))
  rw [Finset.prod_union hFB] at h
  have hF : ∏ e ∈ F, coin p n e (decide (e ∈ F)) = p ^ F.card := by
    rw [Finset.prod_congr rfl (g := fun _ => p)]
    · simp
    · intro e he; simp [coin, he]
  have hB : ∏ e ∈ B, coin p n e (decide (e ∈ F)) = (1 - p) ^ B.card := by
    rw [Finset.prod_congr rfl (g := fun _ => 1 - p)]
    · simp
    · intro e he
      have : e ∉ F := fun h' => Finset.disjoint_left.mp hFB h' he
      simp [coin, this]
  rw [hF, hB] at h
  rw [← h]
  refine pProb_congr fun ω => ?_
  constructor
  · rintro ⟨h1, h2⟩ e he
    rcases Finset.mem_union.mp he with he | he
    · simp [he, h1 e he]
    · have : e ∉ F := fun h' => Finset.disjoint_left.mp hFB h' he
      simp [this, h2 e he]
  · intro h
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · simpa [he] using h e (Finset.mem_union_left _ he)
    · have : e ∉ F := fun h' => Finset.disjoint_left.mp hFB h' he
      simpa [this] using h e (Finset.mem_union_right _ he)

/-- The pairs crossing between two vertex sets. -/
def crossPairs (A B : Finset (Fin n)) : Finset (Pairs n) :=
  univ.filter fun e => ∃ a ∈ A, ∃ b ∈ B, e.1 = s(a, b)

theorem card_crossPairs {A B : Finset (Fin n)} (hAB : Disjoint A B) :
    (crossPairs A B).card = A.card * B.card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij (fun x hx => (⟨s(x.1, x.2), by
      have hx := Finset.mem_product.mp hx
      rw [Sym2.mk_isDiag_iff]
      intro h
      exact Finset.disjoint_left.mp hAB hx.1 (by rw [h]; exact hx.2)⟩ : Pairs n)) ?_ ?_ ?_
  · intro x hx
    have hx := Finset.mem_product.mp hx
    simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x.1, hx.1, x.2, hx.2, rfl⟩
  · intro x hx y hy hxy
    have hx := Finset.mem_product.mp hx
    have hy := Finset.mem_product.mp hy
    have h2 : s(x.1, x.2) = s(y.1, y.2) := congrArg Subtype.val hxy
    rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Prod.ext h3 h4
    · exact absurd (h3 ▸ hy.2) (Finset.disjoint_left.mp hAB hx.1)
  · intro e he
    simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨a, ha, b, hb, hab⟩ := he
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, Subtype.ext hab.symm⟩

theorem noCross_iff (ω : Pairs n → Bool) (A B : Finset (Fin n)) :
    (∀ a ∈ A, ∀ b ∈ B, ¬ (graphOf ω).Adj a b) ↔ ∀ e ∈ crossPairs A B, ω e = false := by
  constructor
  · intro h e he
    simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨a, ha, b, hb, hab⟩ := he
    have := h a ha b hb
    rw [graphOf_adj_iff ω e a b hab] at this
    simpa using this
  · intro h a ha b hb hadj
    have hne : a ≠ b := (graphOf ω).ne_of_adj hadj
    have hmem : (⟨s(a, b), by simpa using hne⟩ : Pairs n) ∈ crossPairs A B := by
      simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, b, hb, rfl⟩
    rw [graphOf_adj_iff ω ⟨s(a, b), by simpa using hne⟩ a b rfl] at hadj
    simp [h _ hmem] at hadj

/-- No edges between two disjoint vertex sets. -/
theorem gnpProb_noCross {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : Finset (Fin n)}
    (hAB : Disjoint A B) :
    gnpProb n p (fun G => ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) = (1 - p) ^ (A.card * B.card) := by
  unfold gnpProb
  rw [pProb_congr (fun ω => noCross_iff ω A B)]
  have h := pProb_coin_present_absent hp0 hp1 ∅ (crossPairs A B) (Finset.disjoint_empty_left _)
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, true_and,
    Finset.card_empty, pow_zero, one_mul] at h
  rw [h, card_crossPairs hAB]

end Pseudorandom.RandomGraphs
