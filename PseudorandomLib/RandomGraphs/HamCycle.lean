/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Rotation

/-! # From list cycles to Mathlib's Hamiltonian cycles

A list of all vertices, consecutive ones adjacent and the last adjacent to the first, gives a
Hamiltonian cycle in the sense of `SimpleGraph.IsHamiltonian` when there are at least three
vertices (`HasHamCycle.isHamiltonian`).
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The walk along a list of vertices, consecutive ones adjacent. -/
def walkOfList : (a : V) → (l : List V) → (a :: l).IsChain G.Adj →
    G.Walk a ((a :: l).getLast (List.cons_ne_nil a l))
  | _, [], _ => Walk.nil
  | _, _ :: l, h => Walk.cons (List.isChain_cons_cons.1 h).1
      (walkOfList _ l (List.isChain_cons_cons.1 h).2)

theorem support_walkOfList (a : V) (l : List V) (h : (a :: l).IsChain G.Adj) :
    (walkOfList a l h).support = a :: l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact congrArg (a :: ·) (ih b _)

theorem HasHamCycle.isHamiltonian [Fintype V] [DecidableEq V] (h : HasHamCycle G)
    (h3 : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
  intro _
  obtain ⟨l, hl, hlen, hc⟩ := h
  obtain ⟨a, l', rfl⟩ : ∃ a l', l = a :: l' := by
    cases l with
    | nil => simp at hlen; omega
    | cons a l' => exact ⟨a, l', rfl⟩
  set q := walkOfList a l' hl.2 with hq
  have hza : G.Adj ((a :: l').getLast (List.cons_ne_nil a l')) a :=
    hc _ (Option.mem_def.2 (List.getLast?_eq_some_getLast _)) a rfl
  refine ⟨_, Walk.cons hza q, ?_⟩
  have hsupp : q.support = a :: l' := support_walkOfList a l' hl.2
  have hqlen : q.length + 1 = Fintype.card V := by
    have := Walk.length_support q
    rw [hsupp] at this
    simp only [List.length_cons] at this hlen
    omega
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq, Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Walk.isPath_def, Walk.support_tail_of_not_nil _ Walk.not_nil_cons, Walk.support_cons,
      List.tail_cons, hsupp]
    exact hl.1
  · simp only [Walk.length_cons]; omega
  · simp only [Walk.length_cons]; omega

end Pseudorandom.RandomGraphs
