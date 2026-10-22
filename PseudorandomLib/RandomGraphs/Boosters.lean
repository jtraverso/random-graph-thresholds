/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.RandomGraphs.Rotation

/-! # Boosters

A *booster* of a graph `G` is a non-edge `uv` such that `G + uv` has a Hamiltonian cycle or a
longer longest path than `G`.

* `booster_count`: a connected graph without Hamiltonian cycle in which every set `S` with
  `|S| ≤ k` has `|N(S) \ S| ≥ 2 |S|` has at least `(k + 1)² / 2` boosters (Pósa).
* `exists_boost_closure`: if `G₁ ⊔ G₂` has no Hamiltonian cycle, then adding at most `|V|` edges
  of `G₂` to `G₁` gives a graph without Hamiltonian cycle none of whose boosters is an edge
  of `G₂`.
-/

@[expose] public section

namespace Pseudorandom.RandomGraphs

open Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

variable (G) in
/-- `uv` is a booster of `G`. -/
def IsBooster (u v : V) : Prop :=
  ¬ G.Adj u v ∧ u ≠ v ∧
    (HasHamCycle (G ⊔ SimpleGraph.edge u v) ∨ maxPathLen G < maxPathLen (G ⊔ SimpleGraph.edge u v))

variable (G) in
open Classical in
/-- The set of boosters of `G`, as unordered pairs. -/
noncomputable def boosterSet : Finset (Sym2 V) :=
  univ.filter fun e => ∃ u v, e = s(u, v) ∧ IsBooster G u v

omit [Fintype V] in
/-- Closing a path into a cycle and leaving it along an edge gives a longer path. -/
theorem longer_of_cycle {R : List V} (hR : IsPathList G R)
    (hc : ∀ a ∈ R.getLast?, ∀ b ∈ R.head?, G.Adj a b) {w y : V} (hw : w ∈ R) (hy : y ∉ R)
    (hwy : G.Adj w y) : ∃ R', IsPathList G R' ∧ R'.length = R.length + 1 := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hw
  refine ⟨y :: ((w :: t) ++ s), ⟨?_, ?_⟩, by simp; omega⟩
  · refine List.nodup_cons.2 ⟨fun h => hy ?_, ?_⟩
    · simp only [List.mem_append, List.mem_cons] at h ⊢
      tauto
    · exact List.perm_append_comm.nodup_iff.1 hR.1
  · obtain ⟨hs, hwt, hj⟩ := List.isChain_append.1 hR.2
    refine List.isChain_cons.2 ⟨fun b hb => ?_, List.isChain_append.2 ⟨hwt, hs, ?_⟩⟩
    · simp only [List.cons_append, List.head?_cons, Option.mem_some_iff] at hb
      subst hb; exact hwy.symm
    · intro a ha b hb
      apply hc a _ b _
      · rw [List.getLast?_append, ha]; rfl
      · rw [List.head?_append, hb]; rfl

omit [Fintype V] in
/-- In a connected graph, a nonempty proper vertex subset is left by some edge. -/
theorem exists_exit {R : List V} (hconn : G.Connected) {a b : V} (ha : a ∈ R) (hb : b ∉ R) :
    ∃ w ∈ R, ∃ y ∉ R, G.Adj w y := by
  obtain ⟨p⟩ := hconn.preconnected a b
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ R} ha hb
  exact ⟨d.toProd.1, hd1, d.toProd.2, hd2, d.adj⟩

/-- Closing a longest path of a connected graph without Hamiltonian cycle: the two ends form a
booster. -/
theorem isBooster_of_longest (hconn : G.Connected) (hham : ¬ HasHamCycle G) {R : List V}
    (hR : IsLongest G R) (h2 : 2 ≤ R.length) {u v : V} (hv : R.head? = some v)
    (hu : R.getLast? = some u) : IsBooster G u v := by
  classical
  -- a path of a supergraph closing into a cycle covers everything or is not longest
  have key : ∀ H : SimpleGraph V, G ≤ H → H.Adj u v →
      HasHamCycle H ∨ ∃ R', IsPathList H R' ∧ R'.length = R.length + 1 := by
    intro H hGH huv
    have hRH := hR.1.mono hGH
    have hc : ∀ a ∈ R.getLast?, ∀ b ∈ R.head?, H.Adj a b := by
      intro a ha b hb
      rw [hu, Option.mem_some_iff] at ha
      rw [hv, Option.mem_some_iff] at hb
      subst ha hb; exact huv
    by_cases hall : ∀ x : V, x ∈ R
    · left
      refine ⟨R, hRH, le_antisymm hR.1.1.length_le_card ?_, hc⟩
      rw [← List.toFinset_card_of_nodup hR.1.1]
      exact (Finset.card_le_card fun x _ => List.mem_toFinset.2 (hall x)).trans_eq'
        (Finset.card_univ).symm
    · push Not at hall
      obtain ⟨b, hb⟩ := hall
      obtain ⟨w, hw, y, hy, hwy⟩ := exists_exit hconn (List.mem_of_getLast? hu) hb
      exact Or.inr (longer_of_cycle hRH hc hw hy (hGH hwy))
  have huv : u ≠ v := by
    intro h
    subst h
    obtain ⟨x, l, rfl⟩ : ∃ x l, R = x :: l := by
      cases R with
      | nil => simp at h2
      | cons x l => exact ⟨x, l, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at hv
    subst hv
    cases l with
    | nil => simp at h2
    | cons y l =>
      rw [List.getLast?_cons_cons] at hu
      exact (List.nodup_cons.1 hR.1.1).1 (List.mem_of_getLast? hu)
  refine ⟨fun hadj => ?_, huv, ?_⟩
  · rcases key G le_rfl hadj with h | ⟨R', hR', hlen⟩
    · exact hham h
    · have := hR'.length_le_maxPathLen
      rw [hlen, hR.2] at this
      omega
  · have hadj : (G ⊔ SimpleGraph.edge u v).Adj u v := by
      rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
    rcases key _ le_sup_left hadj with h | ⟨R', hR', hlen⟩
    · exact Or.inl h
    · right
      have := hR'.length_le_maxPathLen
      rw [hlen, hR.2] at this
      omega

omit [Fintype V] in
theorem IsPathList.reverse {l : List V} (h : IsPathList G l) : IsPathList G l.reverse :=
  ⟨List.nodup_reverse.2 h.1, List.isChain_reverse.2 (h.2.imp fun _ _ h => h.symm)⟩

theorem IsLongest.reverse {l : List V} (h : IsLongest G l) : IsLongest G l.reverse :=
  ⟨h.1.reverse, by rw [List.length_reverse]; exact h.2⟩

/-- Rotation endpoints lie on the path. -/
theorem endSet_subset {P : List V} [DecidableEq V] : endSet G P ⊆ P.toFinset := by
  intro x hx
  obtain ⟨Q, hPQ, hQ⟩ := mem_endSet.1 hx
  exact List.mem_toFinset.2 (hPQ.perm.subset (List.mem_of_getLast? hQ))

/-- **Pósa**: a connected graph without Hamiltonian cycle in which every set `S` with `|S| ≤ k`
has `|N(S) \ S| ≥ 2 |S|` has at least `(k + 1)² / 2` boosters. -/
theorem booster_count [DecidableEq V] {k : ℕ} (hk : 1 ≤ k) (hG : IsExpander G k)
    (hconn : G.Connected) (hham : ¬ HasHamCycle G) : (k + 1) ^ 2 ≤ 2 * (boosterSet G).card := by
  classical
  obtain ⟨P, hP⟩ := exists_isLongest G
  obtain ⟨a⟩ := hconn.nonempty
  have hPne : P ≠ [] := by
    intro h
    have := (show IsPathList G [a] from ⟨List.nodup_singleton a, List.isChain_singleton a⟩)
      |>.length_le_maxPathLen
    rw [← hP.2, h] at this
    simp at this
  have hE := posa_endSet_card hG hP hPne
  have hlen : 2 ≤ maxPathLen G := by
    have h1 := card_le_card (endSet_subset (G := G) (P := P))
    have h2 := List.toFinset_card_le P
    rw [hP.2] at h2
    omega
  set T : Finset (V × V) := univ.filter fun x =>
    ∃ R, IsLongest G R ∧ R.head? = some x.1 ∧ R.getLast? = some x.2 with hT
  -- rows of `T` are large
  have hrow : ∀ v ∈ endSet G P, k + 1 ≤ (T.filter fun x => x.1 = v).card := by
    intro v hv
    obtain ⟨Q, hPQ, hQv⟩ := mem_endSet.1 hv
    have hQ := (hPQ.isLongest hP).reverse
    have hQne : Q.reverse ≠ [] := by
      intro h; rw [List.reverse_eq_nil_iff] at h; subst h; simp at hQv
    refine (posa_endSet_card hG hQ hQne).trans ?_
    refine card_le_card_of_injOn (fun u => (v, u)) (fun u hu => ?_) (fun _ _ _ _ h => ?_)
    · obtain ⟨R, hQR, hRu⟩ := mem_endSet.1 hu
      refine mem_coe.2 (mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, R, hQR.isLongest hQ, ?_, hRu⟩, rfl⟩)
      rw [hQR.head, List.head?_reverse, hQv]
    · simpa using h
  have hTcard : (k + 1) ^ 2 ≤ T.card := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
    calc (k + 1) ^ 2 ≤ ∑ _v ∈ endSet G P, (k + 1) := by
          rw [sum_const, smul_eq_mul, sq]; exact Nat.mul_le_mul_right _ hE
      _ ≤ ∑ v ∈ endSet G P, (T.filter fun x => x.1 = v).card := sum_le_sum hrow
      _ ≤ ∑ v, (T.filter fun x => x.1 = v).card :=
          sum_le_sum_of_subset (subset_univ _)
  have himage : T.image (fun x => s(x.1, x.2)) ⊆ boosterSet G := by
    intro e he
    obtain ⟨⟨v, u⟩, hx, rfl⟩ := mem_image.1 he
    simp only [hT, mem_filter, mem_univ, true_and] at hx
    obtain ⟨R, hR, hRv, hRu⟩ := hx
    simp only [boosterSet, mem_filter, mem_univ, true_and]
    exact ⟨u, v, Sym2.eq_swap, isBooster_of_longest hconn hham hR (hR.2 ▸ hlen) hRv hRu⟩
  have hfib : T.card ≤ 2 * (T.image fun x => s(x.1, x.2)).card := by
    refine card_le_mul_card_image _ 2 fun e he => ?_
    obtain ⟨⟨v, u⟩, -, rfl⟩ := mem_image.1 he
    calc (T.filter fun x => s(x.1, x.2) = s(v, u)).card ≤ ({(v, u), (u, v)} : Finset _).card := by
          refine card_le_card fun x hx => ?_
          simp only [mem_filter] at hx
          rcases Sym2.eq_iff.1 hx.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp [Prod.ext_iff, h1, h2]
          · simp [Prod.ext_iff, h1, h2]
      _ ≤ 2 := card_le_two
  exact hTcard.trans (hfib.trans (Nat.mul_le_mul_left _ (card_le_card himage)))

/-- Iterated boosting: if `G₁ ⊔ G₂` has no Hamiltonian cycle, adding at most `|V|` edges of `G₂`
to `G₁` gives a graph without Hamiltonian cycle none of whose boosters is an edge of `G₂`. -/
theorem exists_boost_closure (G₁ G₂ : SimpleGraph V) (hH : ¬ HasHamCycle (G₁ ⊔ G₂)) :
    ∃ F : Finset (Sym2 V), F.card ≤ Fintype.card V ∧ (∀ e ∈ F, e ∈ G₂.edgeSet) ∧
      ¬ HasHamCycle (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) ∧
      ∀ u v, IsBooster (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) u v → ¬ G₂.Adj u v := by
  classical
  have hle : ∀ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G₂.edgeSet) →
      G₁ ⊔ SimpleGraph.fromEdgeSet ↑F ≤ G₁ ⊔ G₂ := by
    intro F hF
    refine sup_le_sup_left (fun a b hab => ?_) _
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    exact (SimpleGraph.mem_edgeSet _).1 (hF _ hab.1)
  suffices h : ∀ m, ∀ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G₂.edgeSet) →
      F.card ≤ maxPathLen (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) →
      Fintype.card V - maxPathLen (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) ≤ m →
      ∃ F : Finset (Sym2 V), F.card ≤ Fintype.card V ∧ (∀ e ∈ F, e ∈ G₂.edgeSet) ∧
        ¬ HasHamCycle (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) ∧
        ∀ u v, IsBooster (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) u v → ¬ G₂.Adj u v from
    h _ ∅ (by simp) (by simp) le_rfl
  have step : ∀ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G₂.edgeSet) →
      F.card ≤ maxPathLen (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) →
      (∃ u v, IsBooster (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) u v ∧ G₂.Adj u v) →
      ∃ F' : Finset (Sym2 V), (∀ e ∈ F', e ∈ G₂.edgeSet) ∧
        F'.card ≤ maxPathLen (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F') ∧
        maxPathLen (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) <
          maxPathLen (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F') := by
    rintro F hF hcard ⟨u, v, ⟨-, huv, hb⟩, hadj⟩
    set F' := insert s(u, v) F with hF'def
    have hF' : ∀ e ∈ F', e ∈ G₂.edgeSet := by
      intro e he
      rcases mem_insert.1 he with rfl | he
      · exact hadj
      · exact hF e he
    have hsub : G₁ ⊔ SimpleGraph.fromEdgeSet ↑F ⊔ SimpleGraph.edge u v ≤
        G₁ ⊔ SimpleGraph.fromEdgeSet ↑F' := by
      intro a b hab
      simp only [SimpleGraph.sup_adj, SimpleGraph.edge_adj, SimpleGraph.fromEdgeSet_adj] at hab ⊢
      rcases hab with (h | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [hF'def, h1], h2⟩
      · refine Or.inr ⟨?_, h2⟩
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [hF'def]
        · simp [hF'def, Sym2.eq_swap]
    have hmono := maxPathLen_mono hsub
    have hlt : maxPathLen (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) <
        maxPathLen (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F ⊔ SimpleGraph.edge u v) := by
      rcases hb with h | h
      · exact absurd ((h.mono hsub).mono (hle F' hF')) hH
      · exact h
    refine ⟨F', hF', ?_, lt_of_lt_of_le hlt hmono⟩
    have : F'.card ≤ F.card + 1 := card_insert_le _ _
    omega
  intro m
  induction m with
  | zero =>
    intro F hF hcard hm
    by_cases hb : ∀ u v, IsBooster (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) u v → ¬ G₂.Adj u v
    · exact ⟨F, hcard.trans (maxPathLen_le_card _), hF, fun h => hH (h.mono (hle F hF)), hb⟩
    · push Not at hb
      obtain ⟨F', -, -, hlt⟩ := step F hF hcard hb
      have := maxPathLen_le_card (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F')
      omega
  | succ m ih =>
    intro F hF hcard hm
    by_cases hb : ∀ u v, IsBooster (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F) u v → ¬ G₂.Adj u v
    · exact ⟨F, hcard.trans (maxPathLen_le_card _), hF, fun h => hH (h.mono (hle F hF)), hb⟩
    · push Not at hb
      obtain ⟨F', hF', hcard', hlt⟩ := step F hF hcard hb
      have := maxPathLen_le_card (G₁ ⊔ SimpleGraph.fromEdgeSet ↑F')
      exact ih F' hF' hcard' (by omega)

end Pseudorandom.RandomGraphs
