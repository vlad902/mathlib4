/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card

/-!
# Vertex cover

A *vertex cover* of a simple graph is a set of vertices such that every edge is incident to at least
one of the vertices in the set.

## Main definitions

* `SimpleGraph.IsVertexCover G C`: Predicate that `C` is a vertex cover of `G`.
* `SimpleGraph.minVertexCover G`: The size of the minimal vertex cover for `G`.
-/

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

section IsVertexCover

/-- `C` is a vertex cover of `G` if every edge in `G` is incident to at least one vertex in `C`. -/
def IsVertexCover (G : SimpleGraph V) (c : Set V) : Prop :=
  ∀ v w : V, G.Adj v w → v ∈ c ∨ w ∈ c

theorem isVertexCover_iff {c : Set V} :
  IsVertexCover G c ↔ ∀ v w : V, G.Adj v w → v ∈ c ∨ w ∈ c := Iff.rfl

end IsVertexCover

section minVertexCover

/-- The minimal number of vertices in a vertex cover of `G`. -/
noncomputable def minVertexCover (G : SimpleGraph V) : ℕ∞ :=
  ⨅ s : {s : Set V // IsVertexCover G s}, s.val.encard

theorem minVertexCover_eq_biInf :
  minVertexCover G = ⨅ s : {s : Set V // IsVertexCover G s}, s.val.encard := rfl

end minVertexCover
end SimpleGraph
