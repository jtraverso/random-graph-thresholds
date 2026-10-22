/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.PathList

/-! # Pósa rotations

Paths in a graph are represented as lists of distinct vertices with consecutive vertices adjacent
(`IsPathList`). A *rotation* of a path `A ++ B` whose last vertex is adjacent to the last vertex of
`A` is the path `A ++ B.reverse`; it has the same vertex set and the same first vertex.

*Pósa's lemma* (`posa_endSet_card`): if `P` is a longest path and `END` is the set of last vertices
of the paths obtained from `P` by repeated rotations, then every neighbour of `END` lies in `END`
or next to `END` along `P`; hence `|N(END) \ END| < 2 |END|`, and in a graph in which every set `S`
with `|S| ≤ k` has `|N(S) \ S| ≥ 2 |S|`, `END` has more than `k` elements.
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- A path: a list of distinct vertices, consecutive ones adjacent. -/
def IsPathList (l : List V) : Prop := l.Nodup ∧ l.IsChain G.Adj

/-- `G` has a path with `m` vertices. -/
def HasPathLen (m : ℕ) : Prop := ∃ l, IsPathList G l ∧ l.length = m

open Classical in
/-- The maximal number of vertices of a path in `G`. -/
noncomputable def maxPathLen : ℕ := Nat.findGreatest (HasPathLen G) (Fintype.card V)

/-- A longest path of `G`. -/
def IsLongest (l : List V) : Prop := IsPathList G l ∧ l.length = maxPathLen G

/-- `G` has a Hamiltonian cycle, given as a path through all vertices whose ends are adjacent. -/
def HasHamCycle : Prop :=
  ∃ l, IsPathList G l ∧ l.length = Fintype.card V ∧ ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, G.Adj a b

open Classical in
/-- The (external and internal) neighbourhood of a vertex set. -/
noncomputable def nbhd (S : Finset V) : Finset V := univ.filter fun y => ∃ x ∈ S, G.Adj x y

/-- Every set `S` with `|S| ≤ k` has at least `2 |S|` neighbours outside `S`. -/
def IsExpander [DecidableEq V] (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≤ k → 2 * S.card ≤ (nbhd G S \ S).card

variable {G}

theorem IsPathList.length_le_maxPathLen {l : List V} (h : IsPathList G l) :
    l.length ≤ maxPathLen G := by
  classical
  unfold maxPathLen
  exact Nat.le_findGreatest h.1.length_le_card ⟨l, h, rfl⟩

theorem exists_isLongest (G : SimpleGraph V) : ∃ l, IsLongest G l := by
  classical
  have h : HasPathLen G (maxPathLen G) := by
    unfold maxPathLen
    exact Nat.findGreatest_spec (m := 0) (Nat.zero_le _)
      ⟨[], ⟨List.nodup_nil, List.IsChain.nil⟩, rfl⟩
  obtain ⟨l, hl, hlen⟩ := h
  exact ⟨l, hl, hlen⟩

theorem maxPathLen_le_card (G : SimpleGraph V) : maxPathLen G ≤ Fintype.card V := by
  classical
  unfold maxPathLen
  exact Nat.findGreatest_le _

omit [Fintype V] in
theorem IsPathList.mono {H : SimpleGraph V} (hGH : G ≤ H) {l : List V} (h : IsPathList G l) :
    IsPathList H l :=
  ⟨h.1, h.2.imp fun _ _ hab => hGH hab⟩

theorem maxPathLen_mono {H : SimpleGraph V} (hGH : G ≤ H) : maxPathLen G ≤ maxPathLen H := by
  obtain ⟨l, hl, hlen⟩ := exists_isLongest G
  rw [← hlen]
  exact (hl.mono hGH).length_le_maxPathLen

theorem HasHamCycle.mono {H : SimpleGraph V} (hGH : G ≤ H) (h : HasHamCycle G) : HasHamCycle H := by
  obtain ⟨l, hl, hlen, hc⟩ := h
  exact ⟨l, hl.mono hGH, hlen, fun a ha b hb => hGH (hc a ha b hb)⟩

theorem nbhd_mono {H : SimpleGraph V} (hGH : G ≤ H) (S : Finset V) : nbhd G S ⊆ nbhd H S := by
  classical
  intro y hy
  simp only [nbhd, mem_filter, mem_univ, true_and] at hy ⊢
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨x, hx, hGH hxy⟩

theorem IsExpander.mono [DecidableEq V] {H : SimpleGraph V} (hGH : G ≤ H) {k : ℕ}
    (h : IsExpander G k) :
    IsExpander H k := fun S hS =>
  (h S hS).trans (card_le_card (sdiff_subset_sdiff (nbhd_mono hGH S) (subset_refl _)))

/-! ### Rotations -/

variable (G) in
/-- One rotation step. -/
def Rot (l l' : List V) : Prop :=
  ∃ A B : List V, l = A ++ B ∧ l' = A ++ B.reverse ∧ A ≠ [] ∧
    ∀ a ∈ A.getLast?, ∀ b ∈ B.getLast?, G.Adj a b

variable (G) in
/-- Paths obtained by repeated rotations. -/
def Reach : List V → List V → Prop := Relation.ReflTransGen (Rot G)

omit [Fintype V] in
theorem Rot.perm {l l' : List V} (h : Rot G l l') : l'.Perm l := by
  obtain ⟨A, B, rfl, rfl, -, -⟩ := h
  exact (List.perm_append_left_iff A).2 (List.reverse_perm B)

omit [Fintype V] in
theorem Rot.head {l l' : List V} (h : Rot G l l') : l'.head? = l.head? := by
  obtain ⟨A, B, rfl, rfl, hA, -⟩ := h
  rw [List.head?_append, List.head?_append]
  cases A with
  | nil => exact absurd rfl hA
  | cons a A => simp

omit [Fintype V] in
theorem Rot.isPathList {l l' : List V} (h : Rot G l l') (hl : IsPathList G l) :
    IsPathList G l' := by
  refine ⟨h.perm.nodup_iff.2 hl.1, ?_⟩
  obtain ⟨A, B, rfl, rfl, -, hadj⟩ := h
  obtain ⟨hA, hB, -⟩ := List.isChain_append.1 hl.2
  refine List.isChain_append.2 ⟨hA, ?_, ?_⟩
  · rw [List.isChain_reverse]
    exact hB.imp fun _ _ h => h.symm
  · intro a ha b hb
    rw [List.head?_reverse] at hb
    exact hadj a ha b hb

omit [Fintype V] in
theorem Reach.perm {l l' : List V} (h : Reach G l l') : l'.Perm l := by
  induction h with
  | refl => exact List.Perm.refl _
  | tail _ h2 ih => exact h2.perm.trans ih

omit [Fintype V] in
theorem Reach.head {l l' : List V} (h : Reach G l l') : l'.head? = l.head? := by
  induction h with
  | refl => rfl
  | tail _ h2 ih => exact h2.head.trans ih

omit [Fintype V] in
theorem Reach.isPathList {l l' : List V} (h : Reach G l l') (hl : IsPathList G l) :
    IsPathList G l' := by
  induction h with
  | refl => exact hl
  | tail _ h2 ih => exact h2.isPathList ih

theorem Reach.isLongest {l l' : List V} (h : Reach G l l') (hl : IsLongest G l) :
    IsLongest G l' :=
  ⟨h.isPathList hl.1, h.perm.length_eq.trans hl.2⟩

variable (G) in
open Classical in
/-- The set of last vertices of paths obtained from `P` by rotations. -/
noncomputable def endSet (P : List V) : Finset V :=
  univ.filter fun x => ∃ Q, Reach G P Q ∧ Q.getLast? = some x

theorem mem_endSet {P : List V} {x : V} :
    x ∈ endSet G P ↔ ∃ Q, Reach G P Q ∧ Q.getLast? = some x := by
  classical
  simp [endSet]

/-- A neighbour of the last vertex of a longest path lies on the path. -/
theorem mem_of_adj_getLast {Q : List V} (hQ : IsLongest G Q) {x y : V}
    (hx : Q.getLast? = some x) (hxy : G.Adj x y) : y ∈ Q := by
  by_contra hy
  have hpath : IsPathList G (Q ++ [y]) := by
    refine ⟨List.nodup_append.2 ⟨hQ.1.1, List.nodup_singleton y, ?_⟩, ?_⟩
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact fun h => hy (h ▸ ha)
    · refine List.isChain_append.2 ⟨hQ.1.2, List.isChain_singleton y, ?_⟩
      intro a ha b hb
      rw [hx, Option.mem_some_iff] at ha
      simp only [List.head?_cons, Option.mem_some_iff] at hb
      subst ha hb
      exact hxy
  have := hpath.length_le_maxPathLen
  rw [List.length_append, hQ.2] at this
  simp at this

omit [Fintype V] in
/-- Rotating at a neighbour `y` of the last vertex makes the successor of `y` the new end. -/
theorem exists_rot_succ {Q : List V} {x y : V} (hx : Q.getLast? = some x) (hxy : G.Adj x y)
    (hy : y ∈ Q) : ∃ Q' w, Rot G Q Q' ∧ Q'.getLast? = some w ∧ (y, w) ∈ cpairs Q := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hy
  cases t with
  | nil =>
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at hx
    exact absurd hx (G.ne_of_adj hxy).symm
  | cons w t =>
    refine ⟨(s ++ [y]) ++ (w :: t).reverse, w, ⟨s ++ [y], w :: t, by simp, rfl, by simp, ?_⟩,
      ?_, mem_cpairs_of_eq rfl⟩
    · intro a ha b hb
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.mem_some_iff] at ha
      have : (s ++ y :: w :: t).getLast? = (w :: t).getLast? := by
        rw [show s ++ y :: w :: t = (s ++ [y]) ++ (w :: t) by simp, List.getLast?_append]
        cases h : (w :: t).getLast? with
        | none => simp at h
        | some c => rfl
      rw [this, hb] at hx
      cases hx
      subst ha
      exact hxy.symm
    · rw [List.getLast?_append, List.getLast?_reverse]; rfl

/-- Neighbours along the path of a vertex that is neither in `END` nor next to `END` along `P`
are not changed by rotations. -/
theorem pAdj_reach_iff {P Q : List V} (hQ : Reach G P Q) {y : V} (hyE : y ∉ endSet G P)
    (hyN : ∀ z, PAdj P y z → z ∉ endSet G P) (z : V) : PAdj Q y z ↔ PAdj P y z := by
  induction hQ generalizing z with
  | refl => rfl
  | @tail Q R hPQ hQR ih =>
    rw [← ih]
    rcases hQR with ⟨A, B, rfl, rfl, hA, hadj⟩
    have hRend : ∀ w, B.head? = some w → w ∈ endSet G P := by
      intro w hw
      refine mem_endSet.2 ⟨A ++ B.reverse, hPQ.tail ⟨A, B, rfl, rfl, hA, hadj⟩, ?_⟩
      rw [List.getLast?_append, List.getLast?_reverse, hw]; rfl
    have hQend : ∀ w, B.getLast? = some w → w ∈ endSet G P := by
      intro w hw
      refine mem_endSet.2 ⟨A ++ B, hPQ, ?_⟩
      rw [List.getLast?_append, hw]; rfl
    have h1 : B.getLast? ≠ some y := fun h => hyE (hQend y h)
    have h2 : B.head? ≠ some y := fun h => hyE (hRend y h)
    have h3 : A.getLast? ≠ some y := by
      intro h
      cases hB : B.head? with
      | none =>
        have : B = [] := List.head?_eq_none_iff.1 hB
        subst this
        exact hyE (mem_endSet.2 ⟨A ++ [], hPQ, by simpa using h⟩)
      | some w =>
        have hw : PAdj (A ++ B) y w := Or.inl (mem_cpairs_append.2 (Or.inr (Or.inr ⟨h, hB⟩)))
        exact hyN w ((ih w).1 hw) (hRend w hB)
    simp only [PAdj, mem_cpairs_append, mem_cpairs_reverse, List.head?_reverse]
    have h1' : ∀ c, ¬ (A.getLast? = some c ∧ B.getLast? = some y) := fun c h => h1 h.2
    have h2' : ∀ c, ¬ (A.getLast? = some c ∧ B.head? = some y) := fun c h => h2 h.2
    have h3' : ∀ c, ¬ (A.getLast? = some y ∧ c) := fun c h => h3 h.1
    tauto

/-- **Pósa's lemma**: a neighbour of `END` lies in `END` or next to `END` along `P`. -/
theorem posa_nbr {P : List V} (hP : IsLongest G P) {x y : V} (hx : x ∈ endSet G P)
    (hxy : G.Adj x y) : y ∈ endSet G P ∨ ∃ z ∈ endSet G P, PAdj P y z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hyE, hyN⟩ := hcon
  obtain ⟨Q, hPQ, hQx⟩ := mem_endSet.1 hx
  have hQ := hPQ.isLongest hP
  have hyQ := mem_of_adj_getLast hQ hQx hxy
  obtain ⟨Q', w, hrot, hw, hyw⟩ := exists_rot_succ hQx hxy hyQ
  have hwE : w ∈ endSet G P := mem_endSet.2 ⟨Q', hPQ.tail hrot, hw⟩
  have : PAdj P y w :=
    (pAdj_reach_iff hPQ hyE (fun z hz hzE => hyN z hzE hz) w).1 (Or.inl hyw)
  exact hyN w hwE this

theorem card_filter_cpairs_le_one {P : List V} (hP : P.Nodup) (z : V)
    [DecidablePred fun y => (y, z) ∈ cpairs P] [DecidablePred fun y => (z, y) ∈ cpairs P] :
    (univ.filter fun y => (y, z) ∈ cpairs P).card ≤ 1 ∧
      (univ.filter fun y => (z, y) ∈ cpairs P).card ≤ 1 := by
  constructor <;> refine Finset.card_le_one.2 fun a ha b hb => ?_ <;>
    simp only [mem_filter, mem_univ, true_and] at ha hb
  · exact cpairs_snd_unique hP ha hb
  · exact cpairs_fst_unique hP ha hb

open Classical in
/-- The vertices next to `E` along a path `P` number at most `2 |E| - 1` if `E` contains the last
vertex of `P`. -/
theorem card_pnbr_le {P : List V} (hP : P.Nodup) (E : Finset V) {v : V}
    (hv : P.getLast? = some v) (hvE : v ∈ E) :
    (univ.filter fun y => ∃ z ∈ E, PAdj P y z).card + 1 ≤ 2 * E.card := by
  classical
  have hsub : (univ.filter fun y => ∃ z ∈ E, PAdj P y z) ⊆
      E.biUnion (fun z => univ.filter fun y => (y, z) ∈ cpairs P) ∪
        (E.erase v).biUnion (fun z => univ.filter fun y => (z, y) ∈ cpairs P) := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    obtain ⟨z, hz, h | h⟩ := hy
    · exact mem_union_left _ (mem_biUnion.2 ⟨z, hz, by simpa using h⟩)
    · refine mem_union_right _ (mem_biUnion.2 ⟨z, mem_erase.2 ⟨?_, hz⟩, by simpa using h⟩)
      rintro rfl
      exact not_mem_cpairs_getLast hP hv h
  have h1 : (E.biUnion (fun z => univ.filter fun y => (y, z) ∈ cpairs P)).card ≤ E.card := by
    refine (card_biUnion_le).trans ?_
    calc ∑ z ∈ E, (univ.filter fun y => (y, z) ∈ cpairs P).card ≤ ∑ _z ∈ E, 1 :=
          sum_le_sum fun z _ => (card_filter_cpairs_le_one hP z).1
      _ = E.card := by simp
  have h2 : ((E.erase v).biUnion (fun z => univ.filter fun y => (z, y) ∈ cpairs P)).card ≤
      E.card - 1 := by
    refine (card_biUnion_le).trans ?_
    calc ∑ z ∈ E.erase v, (univ.filter fun y => (z, y) ∈ cpairs P).card ≤ ∑ _z ∈ E.erase v, 1 :=
          sum_le_sum fun z _ => (card_filter_cpairs_le_one hP z).2
      _ = E.card - 1 := by simp [card_erase_of_mem hvE]
  have h3 := (card_le_card hsub).trans (card_union_le _ _)
  have h4 : 1 ≤ E.card := card_pos.2 ⟨v, hvE⟩
  omega

/-- **Pósa's lemma**, counting form: in a graph where every set `S` with `|S| ≤ k` has
`|N(S) \ S| ≥ 2 |S|`, the set of rotation endpoints of a longest path has more than `k`
elements. -/
theorem posa_endSet_card [DecidableEq V] {k : ℕ} (hG : IsExpander G k) {P : List V}
    (hP : IsLongest G P) (hne : P ≠ []) : k + 1 ≤ (endSet G P).card := by
  classical
  by_contra h
  push Not at h
  set E := endSet G P with hE
  have h2 := hG E (by omega)
  obtain ⟨v, hv⟩ : ∃ v, P.getLast? = some v := ⟨P.getLast hne, List.getLast?_eq_some_getLast hne⟩
  have hvE : v ∈ E := mem_endSet.2 ⟨P, Relation.ReflTransGen.refl, hv⟩
  have hsub : nbhd G E \ E ⊆ univ.filter fun y => ∃ z ∈ E, PAdj P y z := by
    intro y hy
    simp only [nbhd, mem_sdiff, mem_filter, mem_univ, true_and] at hy
    obtain ⟨⟨x, hx, hxy⟩, hyE⟩ := hy
    rcases posa_nbr hP hx hxy with h | h
    · exact absurd h hyE
    · simpa using h
  have h3 := card_le_card hsub
  have h4 := card_pnbr_le hP.1.1 E hv hvE
  omega

end Pseudorandom.RandomGraphs
