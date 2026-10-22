/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-! # Consecutive pairs of a list

`cpairs l` is the list of consecutive pairs `(l[i], l[i+1])` of a list `l`. These are the edges
traversed by a path given as a list of vertices; we record how they behave under appending and
reversing, and their uniqueness properties for lists without duplicates.
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

variable {V : Type*}

/-- The consecutive pairs of a list. -/
def cpairs : List V → List (V × V)
  | a :: b :: l => (a, b) :: cpairs (b :: l)
  | _ => []

@[simp] theorem cpairs_nil : cpairs ([] : List V) = [] := rfl

@[simp] theorem cpairs_singleton (a : V) : cpairs [a] = [] := rfl

@[simp] theorem cpairs_cons_cons (a b : V) (l : List V) :
    cpairs (a :: b :: l) = (a, b) :: cpairs (b :: l) := rfl

theorem mem_cpairs_cons {x a b : V} {l : List V} :
    (a, b) ∈ cpairs (x :: l) ↔ (a = x ∧ l.head? = some b) ∨ (a, b) ∈ cpairs l := by
  cases l with
  | nil => simp
  | cons y l =>
    simp only [cpairs_cons_cons, List.mem_cons, Prod.mk.injEq, List.head?_cons, Option.some.injEq]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact Or.inl ⟨h1, h2.symm⟩
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | h)
      · exact Or.inl ⟨h1, h2.symm⟩
      · exact Or.inr h

theorem fst_mem_of_mem_cpairs {a b : V} {l : List V} (h : (a, b) ∈ cpairs l) : a ∈ l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rcases mem_cpairs_cons.1 h with ⟨rfl, _⟩ | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem snd_mem_tail_of_mem_cpairs {a b : V} {l : List V} (h : (a, b) ∈ cpairs l) :
    b ∈ l.tail := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rcases mem_cpairs_cons.1 h with ⟨_, hb⟩ | h
    · cases l with
      | nil => simp at hb
      | cons y l => simp at hb; simp [hb]
    · have := ih h
      cases l with
      | nil => simp at this
      | cons y l => exact List.mem_of_mem_tail this

theorem snd_mem_of_mem_cpairs {a b : V} {l : List V} (h : (a, b) ∈ cpairs l) : b ∈ l :=
  List.mem_of_mem_tail (snd_mem_tail_of_mem_cpairs h)

theorem mem_cpairs_append {a b : V} {A B : List V} :
    (a, b) ∈ cpairs (A ++ B) ↔
      (a, b) ∈ cpairs A ∨ (a, b) ∈ cpairs B ∨ (A.getLast? = some a ∧ B.head? = some b) := by
  induction A with
  | nil => simp
  | cons x A ih =>
    rw [List.cons_append, mem_cpairs_cons, ih, mem_cpairs_cons]
    cases A with
    | nil => simp; aesop
    | cons y A =>
      simp only [List.cons_append, List.head?_cons, List.getLast?_cons_cons]
      tauto

theorem mem_cpairs_reverse {a b : V} {l : List V} :
    (a, b) ∈ cpairs l.reverse ↔ (b, a) ∈ cpairs l := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.reverse_cons, mem_cpairs_append, ih, List.getLast?_reverse]
    have e := @mem_cpairs_cons V x b a l
    simp only [cpairs_singleton, List.not_mem_nil, false_or, List.head?_cons,
      Option.some.injEq] at e ⊢
    rw [e]; aesop

theorem mem_cpairs_of_eq {l s t : List V} {a b : V} (h : l = s ++ a :: b :: t) :
    (a, b) ∈ cpairs l := by
  subst h
  rw [mem_cpairs_append]
  simp

theorem cpairs_fst_unique {l : List V} (hl : l.Nodup) {a b b' : V} (h : (a, b) ∈ cpairs l)
    (h' : (a, b') ∈ cpairs l) : b = b' := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rcases mem_cpairs_cons.1 h with ⟨rfl, hb⟩ | h1 <;>
      rcases mem_cpairs_cons.1 h' with ⟨hx, hb'⟩ | h2
    · rw [hb] at hb'; exact Option.some.inj hb'
    · exact absurd (fst_mem_of_mem_cpairs h2) hl.1
    · exact absurd (hx ▸ fst_mem_of_mem_cpairs h1) hl.1
    · exact ih hl.2 h1 h2

theorem cpairs_snd_unique {l : List V} (hl : l.Nodup) {a a' b : V} (h : (a, b) ∈ cpairs l)
    (h' : (a', b) ∈ cpairs l) : a = a' := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    have hhead : ∀ {c}, l.head? = some c → (∀ d, (d, c) ∉ cpairs l) := by
      intro c hc d hd
      cases l with
      | nil => simp at hc
      | cons y l =>
        simp only [List.head?_cons, Option.some.injEq] at hc
        subst hc
        exact (List.nodup_cons.1 hl.2).1 (snd_mem_tail_of_mem_cpairs hd)
    rcases mem_cpairs_cons.1 h with ⟨rfl, hb⟩ | h1 <;>
      rcases mem_cpairs_cons.1 h' with ⟨hx, hb'⟩ | h2
    · exact hx.symm
    · exact absurd h2 (hhead hb a')
    · exact absurd h1 (hhead hb' a)
    · exact ih hl.2 h1 h2

theorem not_mem_cpairs_getLast {l : List V} (hl : l.Nodup) {a b : V}
    (hlast : l.getLast? = some a) : (a, b) ∉ cpairs l := by
  induction l with
  | nil => simp at hlast
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    intro h
    cases l with
    | nil => simp at h
    | cons y l =>
      rw [List.getLast?_cons_cons] at hlast
      rcases mem_cpairs_cons.1 h with ⟨rfl, _⟩ | h1
      · exact hl.1 (List.mem_of_getLast? hlast)
      · exact ih hl.2 hlast h1

/-- `a` and `b` are consecutive (in some order) along `l`. -/
def PAdj (l : List V) (a b : V) : Prop := (a, b) ∈ cpairs l ∨ (b, a) ∈ cpairs l

end Pseudorandom.RandomGraphs
