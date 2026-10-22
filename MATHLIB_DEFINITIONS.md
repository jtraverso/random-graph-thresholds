# Mathlib definitions used in Challenge.lean (random graph thresholds)

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## Finset.card

`Mathlib/Data/Finset/Card.lean`, line 47:

```lean
/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## Finset.filter

`Mathlib/Data/Finset/Filter.lean`, line 52:

```lean
/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`.

For example, one can use `s.filter (· ∈ t)` to get the intersection of `s` with `t : Set α`
as a `Finset α` (when a `DecidablePred (· ∈ t)` instance is available). -/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩
```

## Real.exp

`Mathlib/Analysis/Complex/Exponential.lean`, line 80:

```lean
/-- The real exponential function, defined as the real part of the complex exponential -/
@[pp_nodot, wikidata Q168698]
nonrec def exp (x : ℝ) : ℝ :=
  (exp x).re
```

## Real.log

`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`, line 44:

```lean
/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
@[pp_nodot, wikidata Q11197]
noncomputable def log (x : ℝ) : ℝ :=
  if hx : x = 0 then 0 else expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩
```

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.fromRel

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 137:

```lean
/-- Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive. -/
def SimpleGraph.fromRel {V : Type u} (r : V → V → Prop) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)
```

## SimpleGraph.Walk

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 54:

```lean
/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq
```

## SimpleGraph.Reachable

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 52:

```lean
/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)
```

## SimpleGraph.Preconnected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 228:

```lean
/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v
```

## SimpleGraph.Connected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 314:

```lean
/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]
```

## SimpleGraph.Walk.IsHamiltonian

`Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean`, line 38:

```lean

/-- A Hamiltonian path is a walk `p` that visits every vertex exactly once. Note that while
this definition doesn't contain that `p` is a path, `p.isPath` gives that. -/
def IsHamiltonian (p : G.Walk a b) : Prop := ∀ a, p.support.count a = 1
```

## SimpleGraph.Walk.IsHamiltonianCycle

`Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean`, line 155:

```lean
/-- A Hamiltonian cycle is a cycle that visits every vertex once. -/
structure IsHamiltonianCycle (p : G.Walk a a) : Prop extends p.IsCycle where
  isHamiltonian_tail : p.tail.IsHamiltonian
```

## SimpleGraph.IsHamiltonian

`Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean`, line 248:

```lean
/-- A Hamiltonian graph is a graph that contains a Hamiltonian cycle.

This is equivalent to there being an Hamiltonian cycle based at each vertex.
See `IsHamiltonian.exists_isHamiltonianCycle`.

By convention, the singleton graph is considered to be Hamiltonian and the empty graph is not. -/
def IsHamiltonian (G : SimpleGraph α) : Prop :=
  Fintype.card α ≠ 1 → ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle
```

