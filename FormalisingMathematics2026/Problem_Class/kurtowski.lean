/-
Kuratowski's theorem, Part 1: edge-contraction, minors and subdivisions
(M. Kroeker, *Structural and Algorithmic Graph Theory II*, Lecture Notes 2026, Section 1).
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.style.header false

/-!
# Kuratowski's theorem, Part 1: edge-contraction, minors and subdivisions

This file formalises Section 1 of the lecture notes (`Lecture_Notes.pdf` in this folder):
the definitions, remarks and propositions about minors and subdivisions that are needed for
the proof of Kuratowski's theorem.

**Kuratowski's Theorem** (notes, p. 3). *The following are equivalent for any graph `G`:*
1. *`G` is planar;*
2. *`G` has no `K₅`- or `K₃,₃`-subdivision;*
3. *`G` has no `K₅`- or `K₃,₃`-minor.*

The equivalence (1) ↔ (2) is the theorem of last semester, and (1) ↔ (3) is proved in Section 4 (Tutte's Wheel Theorem). Section 1 proves (2) ↔ (3), i.e. that the "minor
version" and the "subdivision version" of Kuratowski's theorem are equivalent. The direction
(3) → (2) is Remark 1.1 (2) (*a subdivision gives a minor*); the direction (2) → (3) is
Proposition 1.5 together with Proposition 1.6.

## Simple graphs

The notes allow loops and parallel edges. In this file every graph is a `SimpleGraph` of Mathlib:
no loops, no parallel edges. For Kuratowski's theorem nothing is lost: a graph is planar, or has
a `K₅`- or `K₃,₃`-minor or -subdivision, if and only if the simple graph obtained by deleting
loops and merging parallel edges does. Consequently, when we contract an edge `uv`, an edge `vb`
and an edge `ub` become *one* edge `ub` of `G / uv`, and a loop is never created.

## Dictionary between the notes and this file

| notes                                            | this file                                 |
| ------------------------------------------------ | ----------------------------------------- |
| a graph `G = (V, E, φ)`                          | `G : SimpleGraph V`                       |
| `K₅`, `K₃,₃`                                     | `K5`, `K33`                               |
| a subgraph `H` of `G` (same vertices)            | `H ≤ G`                                   |
| `G[S]`, the induced subgraph on `S ⊆ V`          | `G.induce S`                              |
| `G - v`, vertex deletion                         | `G.deleteVert v`                          |
| `G \ e`, edge deletion                           | `G.deleteEdges {e}`                       |
| `G / e`, contraction of the edge `e = uv`        | `G.contract u v`                          |
| Definition 1.3: an `X`-model with branch sets    | `Model X G`, `Model.branch`               |
| `G` has an `X`-minor                             | `X.IsMinor G`                             |
| a sequence of deletions and contractions         | `IsMinorOp X G` (Proposition 1.4)         |
| `G` contains an `X`-subdivision                  | `Subdivision X G`, `X.HasSubdivision G`   |
| a minor-closed class, an excluded minor          | `MinorClosed P`, `IsExcludedMinor P H`    |

## What is proved in this file

* Parts 1 - 3: the basic objects (graphs, `K₅`, `K₃,₃`, subgraphs, deletion, contraction),
  Remark 1.2 (1) (`contractContractIso`) and Remark 1.2 (2) (`deleteEdges_contract`).
* Part 4: models and minors, Remark 1.1 (1) (`isMinor_of_copy`), "`G / e` is a minor of `G`"
  (`isMinor_contract`), transitivity (`IsMinor.trans`), and `IsMinor.card_le`.
* Part 5: Proposition 1.4 in both directions: a sequence of deletions and contractions gives a
  model (`IsMinorOp.isMinor`), and a model in a finite graph gives a sequence of deletions and
  contractions (`IsMinor.isMinorOp`).
* Part 6: subdivisions, Remark 1.1 (2) (`Subdivision.isMinor`).
* Part 7: Propositions 1.5 and 1.6 are stated with their proof sketches and left as `sorry`:
  their proofs need spanning trees and minimal models, which are beyond Lectures 1 - 6.
* Part 8: Kuratowski's theorem, (2) ↔ (3): `no_K5_K33_subdivision_iff_no_K5_K33_minor`.
  The direction (3) → (2) is proved completely; (2) → (3) uses Propositions 1.5 and 1.6.
  Finally `kuratowski` derives the minor version of Kuratowski's theorem from the subdivision
  version of last semester, and Remark 1.7 is formalised.

## Revision of Lectures 1 - 6

Wherever possible the proofs use only the tactics of Lectures 1 - 6:

* Lecture 1: `exact`, `intro`
* Lecture 2: `apply`, `specialize`, `have`, `suffices`, `left`, `right`, `constructor`,
  `rcases`, `by_contra`, `by_cases`
* Lecture 3: `use`, `def`, `theorem`, `#check`, `∃`, `∀`, types and terms
* Lecture 4: `rfl`, `rw`, `induction`, `↔`
* Lecture 5: `refine`, term mode, anonymous constructors `⟨_, _⟩`, `fun x ↦ _`
* Lecture 6: functions, `ext`, sets (`s ⊆ t`, `a ∈ {x | P x}`, `f '' s`), `simp`, `exact?`

The only other tactics are `rintro`/`obtain` (short forms of `intro` + `rcases`), `decide`
(checks a statement about a small concrete object by computation), `subst` (a `rw` with a
hypothesis `x = a` that also removes `x`), `push Not` (moves a `¬` inwards, e.g. turning
`¬ ∃ x, P x` into `∀ x, ¬ P x`), `omega` (linear arithmetic in `ℕ`), and `grind` (propositional
logic, once).
-/

open Finset

namespace SimpleGraph

universe u

variable {V W U : Type*}

/-! ## Part 1: graphs, `K₅` and `K₃,₃`

In the notes a graph is a triple `G = (V, E, φ)`. In Lean the vertices form a *type* `V`, and a
(simple) graph on `V` is a term `G : SimpleGraph V`, consisting of

* `G.Adj : V → V → Prop`      -- `G.Adj x y` is the proposition "`xy` is an edge",
* a proof that `G.Adj` is symmetric (edges have no direction), and
* a proof that `G.Adj` is irreflexive (there are no loops).

So "`xy` is an edge" is a proposition, like the `P` and `Q` of Lecture 2.
-/

#check SimpleGraph
#check SimpleGraph.Adj
#check SimpleGraph.adj_symm  -- `G.Adj u v → G.Adj v u`
#check SimpleGraph.irrefl    -- `¬ G.Adj v v`
#check SimpleGraph.ne_of_adj -- `G.Adj u v → u ≠ v`

/-- The complete graph `K₅` on the five vertices `0, 1, 2, 3, 4`. In Lean the complete graph on a
type is called `⊤`: two vertices are adjacent if and only if they are different. -/
abbrev K5 : SimpleGraph (Fin 5) := ⊤

/-- The complete bipartite graph `K₃,₃`. Its vertices are `Sum.inl 0, Sum.inl 1, Sum.inl 2`
(the left side) and `Sum.inr 0, Sum.inr 1, Sum.inr 2` (the right side). Two vertices are adjacent
if and only if they lie on different sides. -/
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

/-- Adjacency in `K₅` *is* inequality. (Lecture 4: `rfl` proves definitional equalities, and
also definitional `↔`s.) -/
theorem K5_adj (x y : Fin 5) : K5.Adj x y ↔ x ≠ y := Iff.rfl

/-- Adjacency in `K₃,₃`: one vertex on the left, the other on the right. -/
theorem K33_adj (x y : Fin 3 ⊕ Fin 3) :
    K33.Adj x y ↔ (x.isLeft ∧ y.isRight) ∨ (x.isRight ∧ y.isLeft) := Iff.rfl

/-- `0` and `1` are adjacent in `K₅`. (Lecture 4: `rw`; `decide` checks `0 ≠ 1` by computing.) -/
example : K5.Adj 0 1 := by
  rw [K5_adj]
  decide

/-- There are no loops. Remember that `¬ P` means `P → False` (Lecture 2). -/
example : ¬ K5.Adj 2 2 := by
  intro h
  exact K5.irrefl h

/-- The left vertex `0` is adjacent to the right vertex `2` in `K₃,₃`.
(Lecture 2: `left` and `constructor`.) -/
example : K33.Adj (Sum.inl 0) (Sum.inr 2) := by
  rw [K33_adj]
  left
  constructor
  · rfl
  · rfl

/-
Lean must be able to *decide* whether two vertices of `K₃,₃` are adjacent in order to count
edges and neighbours. For `K₅` Mathlib already knows this; for `K₃,₃` we say it once.
-/
instance : DecidableRel K33.Adj := fun v w ↦
  inferInstanceAs (Decidable ((v.isLeft ∧ w.isRight) ∨ (v.isRight ∧ w.isLeft)))


/-- Two vertices on the same side of `K₃,₃` are not adjacent. -/
example : ¬ K33.Adj (Sum.inl 0) (Sum.inl 1) := by
  decide

/-- Adjacency is symmetric. (Lecture 1: `intro` and `exact`.) -/
example (G : SimpleGraph V) (x y : V) : G.Adj x y → G.Adj y x := by
  intro h
  exact G.adj_symm h

/-- The same statement in term mode (Lecture 5). -/
example (G : SimpleGraph V) (x y : V) : G.Adj x y → G.Adj y x :=
  fun h ↦ G.adj_symm h

/-- Every vertex of `K₅` has degree `4`. Since both graphs are tiny, `decide` can simply compute
all five degrees. -/
theorem K5_degree (v : Fin 5) : K5.degree v = 4 := by
  revert v
  decide

/-- Every vertex of `K₃,₃` has degree `3`. -/
theorem K33_degree (v : Fin 3 ⊕ Fin 3) : K33.degree v = 3 := by
  revert v
  decide

/-- `K₃,₃` has maximum degree `3`. This is the hypothesis of Proposition 1.5 for `X = K₃,₃`. -/
theorem K33_degree_le_three (v : Fin 3 ⊕ Fin 3) : K33.degree v ≤ 3 :=
  (K33_degree v).le

/-- `K₅` has `10 = (5 choose 2)` edges and `K₃,₃` has `9 = 3 · 3` edges. -/
theorem card_edgeFinset_K5 : #K5.edgeFinset = 10 := by
  decide

theorem card_edgeFinset_K33 : #K33.edgeFinset = 9 := by
  decide

/-- `K₅` has `5` vertices and `K₃,₃` has `6`. -/
theorem card_vertices_K5 : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5

theorem card_vertices_K33 : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by
  simp

/-! ## Part 2: subgraphs, vertex deletion and edge deletion

"`H` is a subgraph of `G`" has two forms in Lean.

* If `H` and `G` are graphs on the *same* vertex type `V`, then `H ≤ G` means that every edge
  of `H` is an edge of `G`. By definition, `H ≤ G` is `∀ x y, H.Adj x y → G.Adj x y`, so we can
  use `intro x y h` to prove it and `h hxy` or `apply h` to use it.
* `G.induce s` is the induced subgraph `G[s]` on a set `s : Set V` of vertices. Its vertex type
  is `↥s`, the type of terms `⟨x, hx⟩` with `x : V` and `hx : x ∈ s` (Lecture 6).

Recall from the notes: `H` is a subgraph of `G` iff `H` can be obtained from `G` by deleting
edges and vertices. Deleting the vertex `v` means passing to `G[V ∖ {v}]`.
-/

variable (G : SimpleGraph V)

/-- `H ≤ G` unfolds to "every edge of `H` is an edge of `G`". -/
theorem le_iff_forall_adj (H : SimpleGraph V) : H ≤ G ↔ ∀ x y, H.Adj x y → G.Adj x y :=
  Iff.rfl

/-- Using `H ≤ G`. (Lecture 2: `specialize` and `apply`.) -/
example (H : SimpleGraph V) (h : H ≤ G) (x y : V) (hxy : H.Adj x y) : G.Adj x y := by
  rw [le_iff_forall_adj] at h
  specialize h x y
  apply h
  exact hxy

/-- The same, in term mode: `h` is a function and we feed it `hxy` (Lecture 5). -/
example (H : SimpleGraph V) (h : H ≤ G) (x y : V) (hxy : H.Adj x y) : G.Adj x y :=
  h hxy

#check @SimpleGraph.induce      -- `G.induce s : SimpleGraph ↥s`
#check @SimpleGraph.induce_adj  -- `(G.induce s).Adj a b ↔ G.Adj ↑a ↑b`

/-- Two vertices of `G[s]` are adjacent iff they are adjacent in `G`: an induced subgraph keeps
*all* edges between its vertices. `↑a` is the vertex `a : ↥s` seen as a vertex of `G`. -/
example (s : Set V) (a b : s) : (G.induce s).Adj a b ↔ G.Adj a b :=
  Iff.rfl

/-- `G - v`: the graph obtained from `G` by deleting the vertex `v` (and all edges at `v`).
Its vertices are the terms `⟨w, hw⟩` with `w : V` and `hw : w ≠ v`. -/
def deleteVert (v : V) : SimpleGraph {w : V // w ≠ v} := G.induce {w | w ≠ v}

theorem deleteVert_adj (v : V) (a b : {w : V // w ≠ v}) :
    (G.deleteVert v).Adj a b ↔ G.Adj a b :=
  Iff.rfl

/-- Every vertex `w ≠ v` of `G` is still a vertex of `G - v`. (Lecture 3: `⟨w, h⟩` is a term of
the subtype `{x : V // x ≠ v}`.) -/
example (v w : V) (h : w ≠ v) : {x : V // x ≠ v} :=
  ⟨w, h⟩

/-
Edge deletion is already in Mathlib: `G.deleteEdges s` deletes the set `s` of edges. An edge is
an unordered pair `s(x, y) : Sym2 V` (so `s(x, y) = s(y, x)`), and `G \ e` is
`G.deleteEdges {e}`.
-/

#check @SimpleGraph.deleteEdges
#check @SimpleGraph.deleteEdges_adj  -- `(G.deleteEdges s).Adj a b ↔ G.Adj a b ∧ s(a, b) ∉ s`

/-- `ab` is an edge of `G \ e` iff it is an edge of `G` different from `e`. -/
theorem deleteEdge_adj (e : Sym2 V) (a b : V) :
    (G.deleteEdges {e}).Adj a b ↔ G.Adj a b ∧ s(a, b) ≠ e := by
  rw [deleteEdges_adj, Set.mem_singleton_iff]


/-- `G \ e` is a subgraph of `G`. (This is `deleteEdges_le` in Mathlib.) -/
example (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := by
  intro x y h
  rw [deleteEdges_adj] at h
  rcases h with ⟨h, -⟩
  exact h

/-! ## Part 3: edge-contraction

Let `e = uv` be an edge of `G`. The notes define `G / e` by deleting `e`, identifying `u` and
`v` to a new vertex `w`, and letting `w` inherit all edges of `u` and of `v`.

In Lean we let the old vertex `u` play the role of `w` and delete `v`. So `G / uv` is a graph on
the vertex type `{w : V // w ≠ v}` (the same vertex type as `G - v`), and two vertices `a ≠ b`
are adjacent in `G / uv` iff

* `ab` is an edge of `G`, or
* `a = u` and `vb` is an edge of `G` (`u` inherits the neighbours of `v`), or
* `b = u` and `av` is an edge of `G`.

The definition makes sense for any two vertices `u`, `v`; for `uv ∉ E(G)` it is the
*identification* of `u` and `v`. The notes also set `G / e := G \ e` for a loop `e`; a simple
graph has no loops, so this case does not arise.
-/

/-- `G / uv`: contract the edge `uv` to the vertex `u`. -/
def contract (u v : V) : SimpleGraph {w : V // w ≠ v} where
  Adj a b :=
    a.1 ≠ b.1 ∧
      (G.Adj a.1 b.1 ∨
        (a.1 = u ∧ G.Adj v b.1) ∨
        (b.1 = u ∧ G.Adj a.1 v))

  symm := ⟨by
    rintro a b ⟨hab, h⟩
    refine ⟨hab.symm, ?_⟩
    rcases h with h | ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact Or.inl (G.adj_symm h)
    · exact Or.inr (Or.inr ⟨ha, G.adj_symm hb⟩)
    · exact Or.inr (Or.inl ⟨hb, G.adj_symm ha⟩)⟩

  loopless := ⟨by
    rintro a ⟨haa, _⟩
    exact haa rfl⟩

/-- The definition of adjacency in `G / uv`, as a rewriting rule. -/
theorem contract_adj (u v : V) (a b : {w : V // w ≠ v}) :
    (G.contract u v).Adj a b ↔
      a.1 ≠ b.1 ∧ (G.Adj a.1 b.1 ∨ (a.1 = u ∧ G.Adj v b.1) ∨ (b.1 = u ∧ G.Adj a.1 v)) :=
  Iff.rfl

/-- Edges of `G` not at `v` survive the contraction. (Lecture 5: an anonymous constructor
`⟨_, _⟩` proves an `∧`, and `Or.inl` proves an `∨`.) -/
theorem contract_adj_of_adj (u v : V) {a b : {w : V // w ≠ v}} (h : G.Adj a b) :
    (G.contract u v).Adj a b :=
  ⟨G.ne_of_adj h, Or.inl h⟩

/-- `G - v` is a subgraph of `G / uv`: contracting keeps every edge that deleting keeps. -/
theorem deleteVert_le_contract (u v : V) : G.deleteVert v ≤ G.contract u v := by
  intro a b h
  rw [deleteVert_adj] at h
  exact G.contract_adj_of_adj u v h

/-- The new vertex `u` inherits the neighbours of `v`: if `vb ∈ E(G)` and `b ≠ u`, then
`ub ∈ E(G / uv)`. -/
theorem contract_adj_of_adj_right (u v : V) (huv : u ≠ v) {b : {w : V // w ≠ v}} (hb : b.1 ≠ u)
    (h : G.Adj v b) : (G.contract u v).Adj ⟨u, huv⟩ b :=
  ⟨fun h' ↦ hb h'.symm, Or.inr (Or.inl ⟨rfl, h⟩)⟩

/-- **Remark 1.2 (2).** Edge-deletion commutes with edge-contraction: if no edge of `s` has
`u` or `v` as an end, then `(G \ s) / uv = (G / uv) \ s`. (On the right, `s` is read as a set
of edges of `G / uv` via `Sym2.map Subtype.val ⁻¹' s`, the preimage of `s` under the map that
forgets the proof `w ≠ v`, see Lecture 6.)

The proof is pure propositional logic (Lecture 2) after unfolding the definitions. -/
theorem deleteEdges_contract (u v : V) (s : Set (Sym2 V)) (hs : ∀ e ∈ s, u ∉ e ∧ v ∉ e) :
    (G.deleteEdges s).contract u v =
      (G.contract u v).deleteEdges (Sym2.map Subtype.val ⁻¹' s) := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  simp only [contract_adj, deleteEdges_adj, Set.mem_preimage, Sym2.map_mk]
  constructor
  · rintro ⟨hab, h⟩
    refine ⟨⟨hab, ?_⟩, ?_⟩
    · rcases h with ⟨h, -⟩ | ⟨hau, h, -⟩ | ⟨hbu, h, -⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hau, h⟩)
      · exact Or.inr (Or.inr ⟨hbu, h⟩)
    · rcases h with ⟨-, h⟩ | ⟨hau, -, -⟩ | ⟨hbu, -, -⟩
      · exact h
      · intro hmem
        apply (hs _ hmem).1
        rw [← hau]
        exact Sym2.mem_mk_left a b
      · intro hmem
        apply (hs _ hmem).1
        rw [← hbu]
        exact Sym2.mem_mk_right a b
  · rintro ⟨⟨hab, h⟩, hnot⟩
    refine ⟨hab, ?_⟩
    rcases h with h | ⟨hau, h⟩ | ⟨hbu, h⟩
    · exact Or.inl ⟨h, hnot⟩
    · refine Or.inr (Or.inl ⟨hau, h, ?_⟩)
      intro hmem
      exact (hs _ hmem).2 (Sym2.mem_mk_left v b)
    · refine Or.inr (Or.inr ⟨hbu, h, ?_⟩)
      intro hmem
      exact (hs _ hmem).2 (Sym2.mem_mk_right a v)

/-- **Remark 1.2 (1).** Edge-contraction is commutative up to the naming of the new vertices:
contracting first `uv` and then `xy` gives a graph isomorphic to the one obtained by contracting
first `xy` and then `uv`. We assume `v ∉ {x, y}` and `y ∉ {u, v}`, so that both orders make
sense (the two edges may still share the end `u = x`).

An isomorphism `≃g` consists of a bijection of the vertex types (`toFun`, `invFun`) and a proof
`map_rel_iff'` that it preserves adjacency in both directions. Here the bijection just reorders
the two proofs `w ≠ v` and `w ≠ y` attached to a vertex `w`; the adjacency condition unfolds to
a statement of propositional logic, which we leave to the tactic `grind`. -/
def contractContractIso (u v x y : V) (hxv : x ≠ v) (hyv : y ≠ v) (huy : u ≠ y) (hvy : v ≠ y) :
    (G.contract u v).contract ⟨x, hxv⟩ ⟨y, hyv⟩ ≃g
      (G.contract x y).contract ⟨u, huy⟩ ⟨v, hvy⟩ where
  toFun a := ⟨⟨a.1.1, fun h ↦ a.2 (Subtype.ext h)⟩, fun h ↦ a.1.2 (congrArg Subtype.val h)⟩
  invFun a := ⟨⟨a.1.1, fun h ↦ a.2 (Subtype.ext h)⟩, fun h ↦ a.1.2 (congrArg Subtype.val h)⟩
  left_inv a := rfl
  right_inv a := rfl
  map_rel_iff' := by
    rintro ⟨⟨a, hav⟩, hay⟩ ⟨⟨b, hbv⟩, hby⟩
    have hay' : a ≠ y := fun h ↦ hay (Subtype.ext h)
    have hby' : b ≠ y := fun h ↦ hby (Subtype.ext h)
    simp only [Equiv.coe_fn_mk, contract_adj, Subtype.mk.injEq]
    grind

/-! ## Part 4: models and minors

The notes define a minor of `G` as a graph obtained from `G` by a sequence of vertex-deletions,
edge-deletions and edge-contractions. For proofs a more structural description is better
(Definition 1.3 and Proposition 1.4): a *model* of `X` in `G`.

**Definition 1.3** (as we use it). An `X`-model in `G` is a family of *branch sets*
`V_x ⊆ V(G)`, one for each vertex `x` of `X`, such that

1. each `V_x` is nonempty, and the `V_x` are pairwise disjoint;
2. each induced subgraph `G[V_x]` is connected;
3. for every edge `xy` of `X` there is an edge of `G` between `V_x` and `V_y`.

The notes ask instead that a subgraph `H` of `G` has vertex set `⋃ V_x`, that each `H[V_x]` is
a *tree*, and that `H` has *exactly one* edge between `V_x` and `V_y`, and this iff `xy ∈ E(X)`.
The two are equivalent: from our data, choose a spanning tree of each connected graph `G[V_x]`
and one `G`-edge for each edge `xy` of `X`; this is an `X`-model in the sense of the notes.
Conversely such an `H` gives our data, since a tree is connected.

In Lean a model is a `structure` (Lecture 7 will say more about structures): a package of
data (the function `branch : W → Set V`) together with proofs of the three conditions.
-/

/-- Definition 1.3: an `X`-model in `G`, given by its branch sets `branch x ⊆ V(G)`. -/
structure Model (X : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set `V_x` of the vertex `x` of `X`. -/
  branch : W → Set V
  nonempty : ∀ x, (branch x).Nonempty
  disjoint : ∀ x y, x ≠ y → Disjoint (branch x) (branch y)
  connected : ∀ x, (G.induce (branch x)).Connected
  adj : ∀ x y, X.Adj x y → ∃ a ∈ branch x, ∃ b ∈ branch y, G.Adj a b

/-- `G` has an `X`-minor (`X` is a minor of `G`): there exists an `X`-model in `G`. By
Proposition 1.4 this is the same as saying that a graph isomorphic to `X` can be obtained from
`G` by deletions and contractions; see Part 5. -/
def IsMinor (X : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (X.Model G)

/-- A single vertex induces a connected graph. We use Mathlib's characterisation
`connected_iff_exists_forall_reachable`: a graph is connected iff some vertex `v` can reach
every vertex `w`. -/
theorem induce_singleton_connected (a : V) : (G.induce {a}).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨a, Set.mem_singleton a⟩, ?_⟩
  rintro ⟨b, hb⟩
  rw [Set.mem_singleton_iff] at hb
  subst hb
  exact Reachable.refl _

section minors

variable {G} {X : SimpleGraph W} {X' : SimpleGraph U}

/-- **Remark 1.1 (1)**, general form. A *copy* of `X` in `G` (Mathlib: `X.Copy G`) is an
injective graph homomorphism `f : X →g G`, i.e. a subgraph of `G` isomorphic to `X`. Every copy
gives an `X`-model: take the singletons `V_x = {f x}` as branch sets. -/
theorem isMinor_of_copy (f : X.Copy G) : X.IsMinor G := by
  refine ⟨⟨fun x ↦ {f x}, fun x ↦ ⟨f x, Set.mem_singleton _⟩, ?_,
    fun x ↦ G.induce_singleton_connected (f x), ?_⟩⟩
  · -- `{f x}` and `{f y}` are disjoint for `x ≠ y`, because `f` is injective (Lecture 6)
    intro x y hxy
    rw [Set.disjoint_singleton]
    intro h
    exact hxy (f.injective h)
  · -- an edge `xy` of `X` is mapped to the edge `f x f y` of `G`
    intro x y hxy
    exact ⟨f x, Set.mem_singleton _, f y, Set.mem_singleton _, f.toHom.map_adj hxy⟩

/-- Remark 1.1 (1): if `G` contains a subgraph isomorphic to `X` (Mathlib: `X ⊑ G`), then `G`
has an `X`-minor. -/
theorem IsContained.isMinor (h : X ⊑ G) : X.IsMinor G :=
  h.elim fun f ↦ isMinor_of_copy f

variable (G) in
/-- `G` is a minor of itself (Remark 1.1 (1), "including `G` itself"). -/
theorem isMinor_refl : G.IsMinor G :=
  isMinor_of_copy (Copy.ofLE G G le_rfl)

/-- A subgraph `H ≤ G` is a minor of `G`. -/
theorem isMinor_of_le {H : SimpleGraph V} (h : H ≤ G) : H.IsMinor G :=
  isMinor_of_copy (Copy.ofLE H G h)

variable (G) in
/-- An induced subgraph `G[s]` is a minor of `G`. -/
theorem isMinor_induce (s : Set V) : (G.induce s).IsMinor G :=
  isMinor_of_copy (Copy.induce G s)

variable (G) in
/-- Vertex deletion: `G - v` is a minor of `G`. -/
theorem isMinor_deleteVert (v : V) : (G.deleteVert v).IsMinor G :=
  isMinor_induce G {w | w ≠ v}

variable (G) in
/-- Edge deletion: `G \ s` is a minor of `G`. -/
theorem isMinor_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).IsMinor G :=
  isMinor_of_le (deleteEdges_le s)

/-- An isomorphic copy is a minor. -/
theorem Iso.isMinor (e : X ≃g G) : X.IsMinor G :=
  isMinor_of_copy e.toCopy

variable (G) in
/-- Edge contraction: `G / uv` is a minor of `G`. The branch set of the new vertex `u` is
`{u, v}`; every other vertex `a` has the branch set `{a}`. -/
theorem isMinor_contract {u v : V} (huv : G.Adj u v) : (G.contract u v).IsMinor G := by
  refine ⟨⟨fun a ↦ {w | w = a.1 ∨ (a.1 = u ∧ w = v)}, ?_, ?_, ?_, ?_⟩⟩
  · -- nonempty: `a` itself lies in its branch set
    intro a
    exact ⟨a.1, Or.inl rfl⟩
  · -- disjoint
    intro a b hab
    rw [Set.disjoint_left]
    rintro w (hw | ⟨hau, hw⟩) (hw' | ⟨hbu, hw'⟩)
    · exact hab (Subtype.ext (hw.symm.trans hw'))
    · exact a.2 (hw.symm.trans hw')
    · exact b.2 (hw'.symm.trans hw)
    · exact hab (Subtype.ext (hau.trans hbu.symm))
  · -- connected: the branch set is `{u, v}` (an edge of `G`) or a single vertex
    intro a
    show (G.induce {w | w = a.1 ∨ (a.1 = u ∧ w = v)}).Connected
    by_cases hau : a.1 = u
    · have hset : {w | w = a.1 ∨ (a.1 = u ∧ w = v)} = ({u, v} : Set V) := by
        ext w
        rw [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, hau]
        constructor
        · rintro (h | ⟨-, h⟩)
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr ⟨rfl, h⟩
      rw [hset]
      exact induce_pair_connected_of_adj huv
    · have hset : {w | w = a.1 ∨ (a.1 = u ∧ w = v)} = ({a.1} : Set V) := by
        ext w
        rw [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact h
          · exact absurd h hau
        · intro h
          exact Or.inl h
      rw [hset]
      exact G.induce_singleton_connected a.1
  · -- adjacency: unfold the three cases in the definition of `G / uv`
    rintro a b ⟨hab, h | ⟨hau, h⟩ | ⟨hbu, h⟩⟩
    · exact ⟨a.1, Or.inl rfl, b.1, Or.inl rfl, h⟩
    · exact ⟨v, Or.inr ⟨hau, rfl⟩, b.1, Or.inl rfl, h⟩
    · exact ⟨a.1, Or.inl rfl, v, Or.inr ⟨hbu, rfl⟩, h⟩

/-
To prove that a minor of a minor is a minor we need two small facts about walks in induced
subgraphs. A *walk* `p : G.Walk a b` is a sequence of adjacent vertices from `a` to `b`;
`p.support` is the list of its vertices, and `G.Reachable a b` means that some walk exists.
Walks are built like lists, with `Walk.nil` and `Walk.cons`, so we can prove things about them
by `induction` (Lecture 4).
-/

#check @SimpleGraph.Walk
#check @SimpleGraph.Walk.support
#check @SimpleGraph.Reachable

/-- A walk in `G` all of whose vertices lie in `s` is a walk in `G[s]`. -/
theorem reachable_induce_of_walk {s : Set V} {a b : V} (p : G.Walk a b)
    (hp : ∀ z ∈ p.support, z ∈ s) (ha : a ∈ s) (hb : b ∈ s) :
    (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons x m y h p ih =>
    have hm : m ∈ s := by
      apply hp m
      rw [Walk.support_cons]
      exact List.mem_cons_of_mem _ p.start_mem_support
    have h1 : (G.induce s).Adj ⟨x, ha⟩ ⟨m, hm⟩ := h
    exact h1.reachable.trans
      (ih (fun z hz ↦ hp z (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hz)) hm hb)

/-- If `s ⊆ t`, then vertices reachable in `G[s]` are reachable in `G[t]`. -/
theorem Reachable.induce_mono {s t : Set V} (hst : s ⊆ t) {a b : V} (ha : a ∈ s) (hb : b ∈ s)
    (h : (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    (G.induce t).Reachable ⟨a, hst ha⟩ ⟨b, hst hb⟩ :=
  h.map (G.induceHomOfLE hst).toHom

/-- A minor of a minor is a minor. If `X` has a model in `H` with branch sets `B₁ x ⊆ V(H)`
and `H` has a model in `G` with branch sets `B₂ h ⊆ V(G)`, then
`B x = ⋃ (h ∈ B₁ x), B₂ h` are the branch sets of a model of `X` in `G`. -/
theorem IsMinor.trans {H : SimpleGraph U} (hXH : X.IsMinor H) (hHG : H.IsMinor G) :
    X.IsMinor G := by
  obtain ⟨M⟩ := hXH
  obtain ⟨N⟩ := hHG
  let B : W → Set V := fun x ↦ {a | ∃ h ∈ M.branch x, a ∈ N.branch h}
  have hsub : ∀ x h, h ∈ M.branch x → N.branch h ⊆ B x := fun x h hh a ha ↦ ⟨h, hh, ha⟩
  refine ⟨⟨B, ?_, ?_, ?_, ?_⟩⟩
  · -- nonempty
    intro x
    obtain ⟨h, hh⟩ := M.nonempty x
    obtain ⟨a, ha⟩ := N.nonempty h
    exact ⟨a, h, hh, ha⟩
  · -- disjoint
    intro x y hxy
    rw [Set.disjoint_left]
    rintro a ⟨h, hh, ha⟩ ⟨h', hh', ha'⟩
    by_cases hhh' : h = h'
    · subst hhh'
      exact Set.disjoint_left.1 (M.disjoint x y hxy) hh hh'
    · exact Set.disjoint_left.1 (N.disjoint h h' hhh') ha ha'
  · -- connected
    intro x
    rw [connected_iff_exists_forall_reachable]
    obtain ⟨h₀, hh₀⟩ := M.nonempty x
    obtain ⟨a₀, ha₀⟩ := N.nonempty h₀
    -- Key claim: walk along a walk `q` in `H[B₁ x]`. Any vertex of `G` in the branch set of the
    -- start of `q` reaches any vertex in the branch set of the end of `q`, inside `G[B x]`.
    have key : ∀ (h₁ h₂ : M.branch x) (q : (H.induce (M.branch x)).Walk h₁ h₂)
        (a₁ : V) (ha₁ : a₁ ∈ N.branch h₁) (a₂ : V) (ha₂ : a₂ ∈ N.branch h₂),
        (G.induce (B x)).Reachable ⟨a₁, hsub x h₁ h₁.2 ha₁⟩ ⟨a₂, hsub x h₂ h₂.2 ha₂⟩ := by
      intro h₁ h₂ q
      induction q with
      | @nil h =>
        intro a₁ ha₁ a₂ ha₂
        exact Reachable.induce_mono (hsub x _ h.2) ha₁ ha₂ ((N.connected h) ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩)
      | @cons h₁ h' h₂ hadj q ih =>
        intro a₁ ha₁ a₂ ha₂
        -- the edge `h₁ h'` of `H` gives an edge `b₁ b'` of `G` between the two branch sets
        obtain ⟨b₁, hb₁, b', hb', hG⟩ := N.adj h₁ h' hadj
        have r1 := Reachable.induce_mono (hsub x _ h₁.2) ha₁ hb₁
          ((N.connected h₁) ⟨a₁, ha₁⟩ ⟨b₁, hb₁⟩)
        have r2 : (G.induce (B x)).Reachable ⟨b₁, hsub x _ h₁.2 hb₁⟩ ⟨b', hsub x _ h'.2 hb'⟩ :=
          Adj.reachable hG
        exact r1.trans (r2.trans (ih b' hb' a₂ ha₂))
    refine ⟨⟨a₀, hsub x h₀ hh₀ ha₀⟩, ?_⟩
    rintro ⟨a, h, hh, ha⟩
    obtain ⟨q⟩ := (M.connected x) ⟨h₀, hh₀⟩ ⟨h, hh⟩
    exact key ⟨h₀, hh₀⟩ ⟨h, hh⟩ q a₀ ha₀ a ha
  · -- adjacency
    intro x y hxy
    obtain ⟨h, hh, h', hh', hH⟩ := M.adj x y hxy
    obtain ⟨a, ha, a', ha', hG⟩ := N.adj h h' hH
    exact ⟨a, ⟨h, hh, ha⟩, a', ⟨h', hh', ha'⟩, hG⟩

/-- Having an `X`-minor only depends on `X` up to isomorphism. -/
theorem IsMinor.of_iso_left (e : X ≃g X') (h : X'.IsMinor G) : X.IsMinor G :=
  e.isMinor.trans h

/-- Having an `X`-minor only depends on `G` up to isomorphism. -/
theorem IsMinor.of_iso_right {G' : SimpleGraph U} (e : G ≃g G') (h : X.IsMinor G) :
    X.IsMinor G' :=
  h.trans e.isMinor

theorem IsMinor.congr_left (e : X ≃g X') : X.IsMinor G ↔ X'.IsMinor G :=
  ⟨fun h ↦ h.of_iso_left e.symm, fun h ↦ h.of_iso_left e⟩

/-- A minor has at most as many vertices as the graph: choosing one vertex in each branch set
gives an injective function `W → V` (Lecture 6). -/
theorem IsMinor.card_le [Fintype W] [Fintype V] (h : X.IsMinor G) :
    Fintype.card W ≤ Fintype.card V := by
  obtain ⟨M⟩ := h
  let f : W → V := fun x ↦ (M.nonempty x).some
  have hf : ∀ x, f x ∈ M.branch x := fun x ↦ (M.nonempty x).some_mem
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have h1 : f x ∈ M.branch x := hf x
    have h2 : f x ∈ M.branch y := by
      rw [hxy]
      exact hf y
    exact Set.disjoint_left.1 (M.disjoint x y hne) h1 h2
  exact Fintype.card_le_of_injective f hinj

/-- `K₅` is not a minor of `K₄`: a minor cannot have more vertices. -/
example : ¬ K5.IsMinor (⊤ : SimpleGraph (Fin 4)) := by
  intro h
  have h' := h.card_le
  rw [Fintype.card_fin, Fintype.card_fin] at h'
  omega

/-- `K₃,₃` is not a minor of `K₅`. -/
example : ¬ K33.IsMinor K5 := by
  intro h
  have h' := h.card_le
  rw [card_vertices_K33, card_vertices_K5] at h'
  omega

/-- `K₄` is a minor of `K₅`: the map `Fin.castSucc : Fin 4 → Fin 5`, `i ↦ i`, is an injective
graph homomorphism `K₄ →g K₅` (a copy of `K₄` in `K₅`). -/
example : (⊤ : SimpleGraph (Fin 4)).IsMinor K5 :=
  isMinor_of_copy ⟨⟨Fin.castSucc, fun h h' ↦ h (Fin.castSucc_injective 4 h')⟩,
    Fin.castSucc_injective 4⟩

end minors

/-! ## Part 5: minors as sequences of operations (Proposition 1.4)

Here is the definition of the notes: a minor of `G` is a graph obtained from `G` by a sequence
of vertex-deletions, edge-deletions and edge-contractions, in any order. "`G` has an `X`-minor"
then means that some graph in this sequence is isomorphic to `X`.

In Lean this is an *inductive* predicate `IsMinorOp X G` ("`X` is obtained from `G` by
operations"): the six rules below are the only ways to prove it. Deleting a set of vertices at
once (`induce`) and a set of edges at once (`deleteEdges`) is the same as deleting them one by
one (Remark 1.2). A single vertex- or edge-deletion is a special case, see
`IsMinorOp.deleteVert` and `IsMinorOp.deleteEdge`.

Since the operations change the vertex type (`V` becomes `↥s` or `{w // w ≠ v}`), all vertex
types are taken in one fixed universe `Type u`.
-/

/-- The definition of the notes: `IsMinorOp X G` says that `X` can be obtained from `G` by a
sequence of vertex-deletions, edge-deletions and edge-contractions, up to isomorphism. -/
inductive IsMinorOp : {α : Type u} → SimpleGraph α → {β : Type u} → SimpleGraph β → Prop
  /-- Doing nothing. -/
  | refl {α : Type u} (G : SimpleGraph α) : IsMinorOp G G
  /-- Deleting the vertices outside `s`. -/
  | induce {α : Type u} (G : SimpleGraph α) (s : Set α) : IsMinorOp (G.induce s) G
  /-- Deleting the edges in `s`. -/
  | deleteEdges {α : Type u} (G : SimpleGraph α) (s : Set (Sym2 α)) :
      IsMinorOp (G.deleteEdges s) G
  /-- Contracting the edge `uv`. -/
  | contract {α : Type u} (G : SimpleGraph α) {u v : α} (huv : G.Adj u v) :
      IsMinorOp (G.contract u v) G
  /-- Renaming the vertices. -/
  | iso {α α' β : Type u} {X : SimpleGraph α} {X' : SimpleGraph α'} {G : SimpleGraph β}
      (e : X ≃g X') : IsMinorOp X' G → IsMinorOp X G
  /-- Doing one sequence of operations after another. -/
  | trans {α α' β : Type u} {X : SimpleGraph α} {H : SimpleGraph α'} {G : SimpleGraph β} :
      IsMinorOp X H → IsMinorOp H G → IsMinorOp X G

/-- Deleting a single vertex. -/
theorem IsMinorOp.deleteVert {α : Type u} (G : SimpleGraph α) (v : α) :
    IsMinorOp (G.deleteVert v) G :=
  IsMinorOp.induce G {w | w ≠ v}

/-- Deleting a single edge. -/
theorem IsMinorOp.deleteEdge {α : Type u} (G : SimpleGraph α) (e : Sym2 α) :
    IsMinorOp (G.deleteEdges {e}) G :=
  IsMinorOp.deleteEdges G {e}

/-- **Proposition 1.4**, the direction "sequence of operations ⇒ model". Each operation produces
a minor in the sense of Part 4, and `IsMinor` is transitive and invariant under isomorphism.
The proof is an induction over the rules of `IsMinorOp`. -/
theorem IsMinorOp.isMinor {α β : Type u} {X : SimpleGraph α} {G : SimpleGraph β}
    (h : IsMinorOp X G) : X.IsMinor G := by
  induction h with
  | refl G => exact isMinor_refl G
  | induce G s => exact isMinor_induce G s
  | deleteEdges G s => exact isMinor_deleteEdges G s
  | contract G huv => exact isMinor_contract G huv
  | iso e _ ih => exact ih.of_iso_left e
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Proposition 1.4, converse: from a model to a sequence of operations

Let `V_x` (`x ∈ V(X)`) be the branch sets of an `X`-model in a finite graph `G`. We get rid of
the superfluous vertices of `G` one at a time:

* **Step A.** A vertex `v` of `G` in no branch set is deleted; the branch sets are still an
  `X`-model in `G - v` (`Model.deleteVert`).
* **Step B.** If a branch set `V_x` has two vertices, then `G[V_x]` (which is connected) has
  an edge `ac`, which we contract; the branch sets, with `c` removed, are an `X`-model in
  `G / ac` (`Model.contract`).
* **Step C.** If every vertex of `G` lies in a branch set and all branch sets are single
  vertices `{f x}`, then `f : V(X) → V(G)` is a bijection with `X.Adj x y → G.Adj (f x) (f y)`,
  so `X` is isomorphic to the graph obtained from `G` by deleting all edges not of the form
  `f x f y` (`Model.isMinorOp_of_singletons`).

Steps A and B decrease the number of vertices, so an induction on `Fintype.card V` finishes the
proof (`IsMinor.isMinorOp`).
-/

section converse

variable {G} {X : SimpleGraph W}

/-- Two branch sets with a common vertex are the same branch set. -/
theorem Model.eq_of_mem_of_mem (M : X.Model G) {y z : W} {w : V} (hy : w ∈ M.branch y)
    (hz : w ∈ M.branch z) : y = z := by
  by_contra hyz
  exact Set.disjoint_left.1 (M.disjoint y z hyz) hy hz

/-- Step A (vertex deletion). If the vertex `v` of `G` lies in no branch set, then the branch
sets are still an `X`-model in `G - v`. -/
def Model.deleteVert (M : X.Model G) (v : V) (hv : ∀ x, v ∉ M.branch x) :
    X.Model (G.deleteVert v) where
  branch x := {w | w.1 ∈ M.branch x}
  nonempty x := by
    obtain ⟨a, ha⟩ := M.nonempty x
    exact ⟨⟨a, fun h ↦ hv x (h ▸ ha)⟩, ha⟩
  disjoint x y hxy := by
    rw [Set.disjoint_left]
    intro w hw hw'
    exact Set.disjoint_left.1 (M.disjoint x y hxy) hw hw'
  connected x := by
    -- `⟨a, ha⟩ ↦ ⟨⟨a, _⟩, ha⟩` is a surjective homomorphism `G[V_x] →g (G - v)[V_x]`
    let f : G.induce (M.branch x) →g (G.deleteVert v).induce {w | w.1 ∈ M.branch x} :=
      ⟨fun a ↦ ⟨⟨a.1, fun h ↦ hv x (h ▸ a.2)⟩, a.2⟩, fun h ↦ h⟩
    refine (M.connected x).map f ?_
    rintro ⟨⟨a, hav⟩, ha⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  adj x y hxy := by
    obtain ⟨a, ha, b, hb, hab⟩ := M.adj x y hxy
    exact ⟨⟨a, fun h ↦ hv x (h ▸ ha)⟩, ha, ⟨b, fun h ↦ hv y (h ▸ hb)⟩, hb, hab⟩

/-- Step B (edge contraction). If `a` and `c` are adjacent vertices in the same branch set
`V_x`, then the branch sets (with `c` removed) are an `X`-model in `G / ac`. -/
def Model.contract (M : X.Model G) {x : W} {a c : V} (ha : a ∈ M.branch x)
    (hc : c ∈ M.branch x) (hac : G.Adj a c) : X.Model (G.contract a c) where
  branch y := {w | w.1 ∈ M.branch y}
  nonempty y := by
    obtain ⟨d, hd⟩ := M.nonempty y
    by_cases hdc : d = c
    · -- then `V_y = V_x`, which contains `a ≠ c`
      have hyx : y = x := M.eq_of_mem_of_mem hd (hdc ▸ hc)
      rw [hyx]
      exact ⟨⟨a, G.ne_of_adj hac⟩, ha⟩
    · exact ⟨⟨d, hdc⟩, hd⟩
  disjoint y z hyz := by
    rw [Set.disjoint_left]
    intro w hw hw'
    exact Set.disjoint_left.1 (M.disjoint y z hyz) hw hw'
  connected y := by
    classical
    have hac' : a ≠ c := G.ne_of_adj hac
    by_cases hyx : y = x
    · rw [hyx]
      -- `c ∈ V_x`: the vertex `c` of `G[V_x]` becomes `a` in `(G / ac)[V_x ∖ {c}]`
      let f : M.branch x → ↥{w : {w : V // w ≠ c} | w.1 ∈ M.branch x} :=
        fun p ↦ if hpc : p.1 = c then ⟨⟨a, hac'⟩, ha⟩ else ⟨⟨p.1, hpc⟩, p.2⟩
      -- adjacent vertices of `G[V_x]` have reachable images
      have hadj : ∀ p q : M.branch x, (G.induce (M.branch x)).Adj p q →
          ((G.contract a c).induce {w | w.1 ∈ M.branch x}).Reachable (f p) (f q) := by
        intro p q hpq
        have hpq' : G.Adj p.1 q.1 := hpq
        by_cases hpc : p.1 = c
        · have e1 : f p = ⟨⟨a, hac'⟩, ha⟩ := dite_eq_left hpc
          by_cases hqc : q.1 = c
          · exact absurd (hpc.trans hqc.symm) (G.ne_of_adj hpq')
          · have e2 : f q = ⟨⟨q.1, hqc⟩, q.2⟩ := dite_eq_right hqc
            rw [e1, e2]
            by_cases hqa : q.1 = a
            · have e3 : (⟨⟨q.1, hqc⟩, q.2⟩ : ↥{w : {w : V // w ≠ c} | w.1 ∈ M.branch x}) =
                  ⟨⟨a, hac'⟩, ha⟩ := Subtype.ext (Subtype.ext hqa)
              rw [e3]
            · exact Adj.reachable ⟨Ne.symm hqa, Or.inr (Or.inl ⟨rfl, hpc ▸ hpq'⟩)⟩
        · have e1 : f p = ⟨⟨p.1, hpc⟩, p.2⟩ := dite_eq_right hpc
          by_cases hqc : q.1 = c
          · have e2 : f q = ⟨⟨a, hac'⟩, ha⟩ := dite_eq_left hqc
            rw [e1, e2]
            by_cases hpa : p.1 = a
            · have e3 : (⟨⟨p.1, hpc⟩, p.2⟩ : ↥{w : {w : V // w ≠ c} | w.1 ∈ M.branch x}) =
                  ⟨⟨a, hac'⟩, ha⟩ := Subtype.ext (Subtype.ext hpa)
              rw [e3]
            · exact Adj.reachable ⟨hpa, Or.inr (Or.inr ⟨rfl, hqc ▸ hpq'⟩)⟩
          · have e2 : f q = ⟨⟨q.1, hqc⟩, q.2⟩ := dite_eq_right hqc
            rw [e1, e2]
            exact Adj.reachable (G.contract_adj_of_adj a c hpq')
      -- hence the images of the ends of any walk in `G[V_x]` are reachable from each other
      have hwalk : ∀ (p q : M.branch x) (w : (G.induce (M.branch x)).Walk p q),
          ((G.contract a c).induce {w | w.1 ∈ M.branch x}).Reachable (f p) (f q) := by
        intro p q w
        induction w with
        | nil => exact Reachable.refl _
        | cons h _ ih => exact (hadj _ _ h).trans ih
      rw [connected_iff_exists_forall_reachable]
      refine ⟨⟨⟨a, hac'⟩, ha⟩, ?_⟩
      rintro ⟨⟨q, hqc⟩, hq⟩
      have e1 : f ⟨a, ha⟩ = ⟨⟨a, hac'⟩, ha⟩ := dite_eq_right hac'
      have e2 : f ⟨q, hq⟩ = ⟨⟨q, hqc⟩, hq⟩ := dite_eq_right hqc
      rw [← e1, ← e2]
      obtain ⟨w⟩ := (M.connected x) ⟨a, ha⟩ ⟨q, hq⟩
      exact hwalk _ _ w
    · -- `c ∉ V_y`: `⟨p, hp⟩ ↦ ⟨⟨p, _⟩, hp⟩` is a surjective homomorphism
      have hcy : ∀ p, p ∈ M.branch y → p ≠ c :=
        fun p hp hpc ↦ hyx (M.eq_of_mem_of_mem hp (hpc ▸ hc))
      let g : G.induce (M.branch y) →g (G.contract a c).induce {w | w.1 ∈ M.branch y} :=
        ⟨fun p ↦ ⟨⟨p.1, hcy p.1 p.2⟩, p.2⟩, fun h ↦ G.contract_adj_of_adj a c h⟩
      refine (M.connected y).map g ?_
      rintro ⟨⟨p, hpc⟩, hp⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  adj y z hyz := by
    obtain ⟨p, hp, q, hq, hpq⟩ := M.adj y z hyz
    by_cases hpc : p = c
    · -- `p = c` is replaced by `a`
      have hyx : y = x := M.eq_of_mem_of_mem hp (hpc ▸ hc)
      have hqc : q ≠ c := fun h ↦ G.ne_of_adj hpq (hpc.trans h.symm)
      have haq : a ≠ q := fun h ↦
        X.ne_of_adj hyz (hyx.trans (M.eq_of_mem_of_mem ha (h ▸ hq)))
      refine ⟨⟨a, G.ne_of_adj hac⟩, hyx ▸ ha, ⟨q, hqc⟩, hq, ?_⟩
      exact ⟨haq, Or.inr (Or.inl ⟨rfl, hpc ▸ hpq⟩)⟩
    · by_cases hqc : q = c
      · have hzx : z = x := M.eq_of_mem_of_mem hq (hqc ▸ hc)
        have hpa : p ≠ a := fun h ↦
          X.ne_of_adj hyz ((M.eq_of_mem_of_mem hp (h ▸ ha)).trans hzx.symm)
        refine ⟨⟨p, hpc⟩, hp, ⟨a, G.ne_of_adj hac⟩, hzx ▸ ha, ?_⟩
        exact ⟨hpa, Or.inr (Or.inr ⟨rfl, hqc ▸ hpq⟩)⟩
      · exact ⟨⟨p, hpc⟩, hp, ⟨q, hqc⟩, hq, G.contract_adj_of_adj a c hpq⟩

end converse

/-- Step C. If every vertex of `G` lies in a branch set and every branch set is a single vertex,
then `X` is isomorphic to a spanning subgraph of `G`: delete the edges not coming from `X`. -/
theorem Model.isMinorOp_of_singletons {α β : Type u} {X : SimpleGraph α} {G : SimpleGraph β}
    (M : X.Model G) (hcover : ∀ v, ∃ x, v ∈ M.branch x)
    (hsingle : ∀ x, ∀ a ∈ M.branch x, ∀ b ∈ M.branch x, a = b) : IsMinorOp X G := by
  classical
  -- the bijection `e : V(X) ≃ V(G)`, `x ↦` the unique vertex of `V_x`
  let f : α → β := fun x ↦ (M.nonempty x).some
  have hf : ∀ x, f x ∈ M.branch x := fun x ↦ (M.nonempty x).some_mem
  let g : β → α := fun v ↦ (hcover v).choose
  have hg : ∀ v, v ∈ M.branch (g v) := fun v ↦ (hcover v).choose_spec
  let e : α ≃ β :=
    { toFun := f
      invFun := g
      left_inv := fun x ↦ M.eq_of_mem_of_mem (hg (f x)) (hf x)
      right_inv := fun v ↦ hsingle (g v) (f (g v)) (hf (g v)) v (hg v) }
  have hinj : Function.Injective f := e.injective
  have hadj : ∀ x y, X.Adj x y → G.Adj (f x) (f y) := by
    intro x y hxy
    obtain ⟨a, ha, b, hb, hab⟩ := M.adj x y hxy
    rw [hsingle x a ha (f x) (hf x), hsingle y b hb (f y) (hf y)] at hab
    exact hab
  -- the edges of `G` that do not come from an edge of `X`
  let S : Set (Sym2 β) := {s | ¬ ∃ x y, X.Adj x y ∧ s = s(f x, f y)}
  let iso : X ≃g G.deleteEdges S :=
    { e with
      map_rel_iff' := by
        intro x y
        change (G.deleteEdges S).Adj (f x) (f y) ↔ X.Adj x y
        rw [deleteEdges_adj]
        constructor
        · rintro ⟨-, hS⟩
          by_contra hxy
          apply hS
          rintro ⟨x', y', hxy', he⟩
          rw [Sym2.eq_iff] at he
          rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [hinj h1, hinj h2] at hxy
            exact hxy hxy'
          · rw [hinj h1, hinj h2] at hxy
            exact hxy (X.adj_symm hxy')
        · intro hxy
          refine ⟨hadj x y hxy, ?_⟩
          intro hS
          exact hS ⟨x, y, hxy, rfl⟩ }
  exact IsMinorOp.iso iso (IsMinorOp.deleteEdges G S)

/-- **Proposition 1.4**, the direction "model ⇒ sequence of operations", for a finite `G`.
Strong induction on the number of vertices of `G`, following Steps A, B and C above. -/
theorem IsMinor.isMinorOp {α β : Type u} [Fintype β] {X : SimpleGraph α} {G : SimpleGraph β}
    (h : X.IsMinor G) : IsMinorOp X G := by
  classical
  obtain ⟨M⟩ := h
  suffices key : ∀ (n : ℕ) (β : Type u) [Fintype β] (G : SimpleGraph β),
      Fintype.card β ≤ n → X.Model G → IsMinorOp X G from key _ β G le_rfl M
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro β _ G hcard N
  by_cases hdel : ∃ v, ∀ x, v ∉ N.branch x
  · -- Step A: delete a vertex outside all branch sets
    obtain ⟨v, hv⟩ := hdel
    have hlt : Fintype.card {w : β // w ≠ v} < Fintype.card β :=
      Fintype.card_subtype_lt (x := v) (fun h ↦ h rfl)
    have := ih (Fintype.card β - 1) (by omega) {w : β // w ≠ v} (G.deleteVert v) (by omega)
      (N.deleteVert v hv)
    exact this.trans (IsMinorOp.deleteVert G v)
  · push Not at hdel
    by_cases hcon : ∃ x, ∃ a ∈ N.branch x, ∃ c ∈ N.branch x, a ≠ c
    · -- Step B: contract an edge inside a branch set with two vertices
      obtain ⟨x, a, ha, c, hc, hac⟩ := hcon
      -- `G[V_x]` is connected and `a ≠ c`, so some edge of `G[V_x]` starts at `a`
      obtain ⟨c', hc', hadj⟩ : ∃ c' ∈ N.branch x, G.Adj a c' := by
        obtain ⟨w⟩ := (N.connected x) ⟨a, ha⟩ ⟨c, hc⟩
        obtain ⟨d, -, hd1, hd2⟩ := w.exists_boundary_dart {⟨a, ha⟩} (Set.mem_singleton _)
          (fun h ↦ hac (congrArg Subtype.val (Set.mem_singleton_iff.1 h)).symm)
        have hadj := d.adj
        rw [Set.mem_singleton_iff.1 hd1] at hadj
        exact ⟨d.snd.1, d.snd.2, hadj⟩
      have hlt : Fintype.card {w : β // w ≠ c'} < Fintype.card β :=
        Fintype.card_subtype_lt (x := c') (fun h ↦ h rfl)
      have := ih (Fintype.card β - 1) (by omega) {w : β // w ≠ c'} (G.contract a c') (by omega)
        (N.contract ha hc' hadj)
      exact this.trans (IsMinorOp.contract G hadj)
    · -- Step C: all branch sets are single vertices and cover `G`
      push Not at hcon
      exact N.isMinorOp_of_singletons hdel hcon

/-- **Proposition 1.4.** For a finite graph `G`, `G` has an `X`-minor (there is an `X`-model in
`G`) if and only if `X` can be obtained from `G` by deletions and contractions. -/
theorem isMinor_iff_isMinorOp {α β : Type u} [Fintype β] {X : SimpleGraph α}
    {G : SimpleGraph β} : X.IsMinor G ↔ IsMinorOp X G :=
  ⟨fun h ↦ h.isMinorOp, fun h ↦ h.isMinor⟩

/-! ## Part 6: subdivisions (Remark 1.1 (2))

A *subdivision* of `X` replaces every edge `xy` of `X` by a path from `x` to `y`, where
different paths meet only in their ends and no path passes through a vertex of `X`. "`G`
contains an `X`-subdivision" means that `G` has a subgraph which is a subdivision of `X`; the
vertices of `X` are then called *branch vertices*.

In Lean (Lecture 6: functions) this is a function `vert : V(X) → V(G)`, injective, together
with, for every edge `xy` of `X`, a path `path x y h : G.Walk (vert x) (vert y)` such that

* `path y x` is `path x y` read backwards (the path belongs to the *unordered* edge `xy`),
* no vertex in the interior of a path is a branch vertex, and
* the interior of a path meets no other path.

The *interior* of the path `P x y` is the set of vertices `z ∈ P x y` with `z ≠ vert x` and
`z ≠ vert y`.
-/

/-- An `X`-subdivision in `G` (`X` is a *topological minor* of `G`). -/
structure Subdivision (X : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch vertex of `G` corresponding to the vertex `x` of `X`. -/
  vert : W → V
  injective : Function.Injective vert
  /-- The path of `G` replacing the edge `xy` of `X`. -/
  path : ∀ x y, X.Adj x y → G.Walk (vert x) (vert y)
  isPath : ∀ x y (h : X.Adj x y), (path x y h).IsPath
  path_symm : ∀ x y (h : X.Adj x y), path y x (X.adj_symm h) = (path x y h).reverse
  interior_ne_vert : ∀ x y (h : X.Adj x y) z, z ∈ (path x y h).support →
    z ≠ vert x → z ≠ vert y → ∀ w, z ≠ vert w
  interior_disjoint : ∀ x y (h : X.Adj x y) x' y' (h' : X.Adj x' y'), s(x, y) ≠ s(x', y') →
    ∀ z, z ∈ (path x y h).support → z ≠ vert x → z ≠ vert y → z ∉ (path x' y' h').support

/-- `G` contains an `X`-subdivision. -/
def HasSubdivision (X : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (X.Subdivision G)

section subdivisions

variable {G} {X : SimpleGraph W}

/-- A copy of `X` in `G` is an `X`-subdivision in which every path has length one.
(Lecture 5: the fields of a structure can be given one by one with `where`.) -/
def Copy.toSubdivision (f : X.Copy G) : X.Subdivision G where
  vert := f
  injective := f.injective
  path x y h := Walk.cons (f.toHom.map_adj h) Walk.nil
  isPath x y h := by
    -- a single edge `f x f y` is a path because `f x ≠ f y`
    apply Walk.IsPath.nil.cons
    rw [Walk.support_nil, List.mem_singleton]
    exact G.ne_of_adj (f.toHom.map_adj h)
  path_symm x y h := rfl
  interior_ne_vert x y h z hz hzx hzy := by
    -- a path of length one has no interior vertex
    exfalso
    rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hz
    rcases hz with hz | hz
    · exact hzx hz
    · exact hzy hz
  interior_disjoint x y h x' y' h' hne z hz hzx hzy := by
    exfalso
    rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hz
    rcases hz with hz | hz
    · exact hzx hz
    · exact hzy hz

/-- If `G` contains a subgraph isomorphic to `X`, then `G` contains an `X`-subdivision. -/
theorem IsContained.hasSubdivision (h : X ⊑ G) : X.HasSubdivision G :=
  h.elim fun f ↦ ⟨f.toSubdivision⟩

variable (G) in
theorem hasSubdivision_refl : G.HasSubdivision G :=
  ⟨(Copy.ofLE G G le_rfl).toSubdivision⟩

/-- On a path `p` from `a` to `b` and a vertex `z ≠ b` of `p`, the initial segment
`p.takeUntil z` of `p` ending at `z` does not contain `b`. (A path visits no vertex twice.) -/
theorem not_mem_support_takeUntil_of_isPath [DecidableEq V] {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) {z : V} (hz : z ∈ p.support) (hzb : z ≠ b) :
    b ∉ (p.takeUntil z hz).support := by
  intro hb
  -- `p = (p.takeUntil z) ++ (p.dropUntil z)`, and the vertices of a path are pairwise distinct
  have hnodup : ((p.takeUntil z hz).append (p.dropUntil z hz)).support.Nodup := by
    rw [Walk.take_spec]
    exact hp.support_nodup
  rw [Walk.support_append] at hnodup
  -- `b` is the last vertex of `p.dropUntil z`, and `b ≠ z` is not its first vertex
  have hb' : b ∈ (p.dropUntil z hz).support.tail := by
    have hend := (p.dropUntil z hz).end_mem_support
    rw [← Walk.cons_tail_support, List.mem_cons] at hend
    rcases hend with h | h
    · exact absurd h hzb.symm
    · exact h
  exact List.disjoint_of_nodup_append hnodup hb hb'

/-- **Remark 1.1 (2).** If `G` contains an `X`-subdivision, then `G` has an `X`-minor.

*Proof.* Give every edge `xy` of `X` to one of its two ends, its *owner*. The branch set of a
vertex `x` of `X` consists of the branch vertex `vert x` together with the interiors of all
paths that `x` owns. Each branch set is connected (it is a union of initial segments of paths
starting at `vert x`), the branch sets are disjoint because different paths have disjoint
interiors, and the path `P x y` contains an edge from the branch set of `x` to the branch set
of `y`, namely the first edge of `P x y` that leaves the branch set of `x`. -/
theorem Subdivision.isMinor (S : X.Subdivision G) : X.IsMinor G := by
  classical
  -- Step 0: every edge `xy` of `X` is owned by one of its ends. We take the first component of
  -- Mathlib's canonical representative `(s(x, y)).out : W × W` of the unordered pair.
  let own : W → W → Prop := fun x y ↦ (s(x, y)).out.1 = x
  have own_or : ∀ x y, own x y ∨ own y x := by
    intro x y
    have h := Sym2.out_fst_mem (s(x, y))
    rw [Sym2.mem_iff] at h
    rcases h with h | h
    · exact Or.inl h
    · right
      change (s(y, x)).out.1 = y
      rw [Sym2.eq_swap]
      exact h
  have own_eq : ∀ x y x' y', own x y → own x' y' → s(x, y) = s(x', y') → x = x' := by
    intro x y x' y' h h' he
    exact h.symm.trans ((congrArg (fun e : Sym2 W ↦ e.out.1) he).trans h')
  -- Step 1: the branch sets
  let B : W → Set V := fun x ↦ {z | z = S.vert x ∨ ∃ y, ∃ h : X.Adj x y, own x y ∧
    z ∈ (S.path x y h).support ∧ z ≠ S.vert x ∧ z ≠ S.vert y}
  have hvert : ∀ x, S.vert x ∈ B x := fun x ↦ Or.inl rfl
  have hvert_not : ∀ x x', x ≠ x' → S.vert x ∉ B x' := by
    rintro x x' hxx' (h | ⟨y, hy, -, hmem, hne1, hne2⟩)
    · exact hxx' (S.injective h)
    · exact S.interior_ne_vert x' y hy (S.vert x) hmem hne1 hne2 x rfl
  refine ⟨⟨B, fun x ↦ ⟨S.vert x, hvert x⟩, ?_, ?_, ?_⟩⟩
  · -- Step 2: the branch sets are disjoint
    intro x x' hxx'
    rw [Set.disjoint_left]
    rintro z (hz | ⟨y, hy, hown, hmem, hzx, hzy⟩) hz'
    · -- the branch vertex of `x` is not in `B x'`
      rw [hz] at hz'
      exact hvert_not x x' hxx' hz'
    · rcases hz' with hz' | ⟨y', hy', hown', hmem', hzx', hzy'⟩
      · -- an interior vertex is not a branch vertex
        exact S.interior_ne_vert x y hy z hmem hzx hzy x' hz'
      · -- an interior vertex of two paths: the paths are equal, so their owners agree
        by_cases he : s(x, y) = s(x', y')
        · exact hxx' (own_eq x y x' y' hown hown' he)
        · exact S.interior_disjoint x y hy x' y' hy' he z hmem hzx hzy hmem'
  · -- Step 3: each branch set is connected
    intro x
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨S.vert x, hvert x⟩, ?_⟩
    rintro ⟨z, hz | ⟨y, hy, hown, hmem, hzx, hzy⟩⟩
    · subst hz
      exact Reachable.refl _
    · -- walk from `vert x` to `z` along the initial segment of the path `P x y`
      have hyP : S.vert y ∉ ((S.path x y hy).takeUntil z hmem).support :=
        not_mem_support_takeUntil_of_isPath (S.isPath x y hy) hmem hzy
      apply reachable_induce_of_walk ((S.path x y hy).takeUntil z hmem)
      intro w hw
      have hwP : w ∈ (S.path x y hy).support :=
        (S.path x y hy).support_takeUntil_subset_support hmem hw
      by_cases hwx : w = S.vert x
      · exact Or.inl hwx
      · have hwy : w ≠ S.vert y := fun h ↦ hyP (h ▸ hw)
        exact Or.inr ⟨y, hy, hown, hwP, hwx, hwy⟩
  · -- Step 4: an edge `xy` of `X` gives an edge of `G` between `B x` and `B y`
    have key : ∀ x y (h : X.Adj x y), own x y → ∃ a ∈ B x, ∃ b ∈ B y, G.Adj a b := by
      intro x y h hown
      have hy : S.vert y ∉ B x := hvert_not y x (X.ne_of_adj h).symm
      -- the path `P x y` starts in `B x` and ends outside; take the first edge `ab` leaving `B x`
      obtain ⟨d, hd, hdx, hdy⟩ := (S.path x y h).exists_boundary_dart (B x) (hvert x) hy
      refine ⟨d.fst, hdx, d.snd, ?_, d.adj⟩
      -- `b = d.snd` lies on the path but not in `B x`, so it is the end `vert y` of the path
      have hmem : d.snd ∈ (S.path x y h).support :=
        (S.path x y h).dart_snd_mem_support_of_mem_darts hd
      by_contra hne
      apply hdy
      have hsx : d.snd ≠ S.vert x := fun h' ↦ hdy (h' ▸ hvert x)
      have hsy : d.snd ≠ S.vert y := fun h' ↦ hne (h' ▸ hvert y)
      exact Or.inr ⟨y, h, hown, hmem, hsx, hsy⟩
    intro x y h
    rcases own_or x y with hown | hown
    · exact key x y h hown
    · obtain ⟨a, ha, b, hb, hab⟩ := key y x (X.adj_symm h) hown
      exact ⟨b, hb, a, ha, G.adj_symm hab⟩

/-- Remark 1.1 (2): `G` contains an `X`-subdivision → `G` has an `X`-minor. -/
theorem HasSubdivision.isMinor (h : X.HasSubdivision G) : X.IsMinor G :=
  h.elim fun S ↦ S.isMinor

end subdivisions

/-! ## Part 7: Propositions 1.5 and 1.6

These two propositions say that for `X = K₃,₃` and `X = K₅` the converse of Remark 1.1 (2)
*does* hold. Their proofs choose an `X`-model `H` with as few vertices as possible and analyse
the trees `H[V_x]` (a tree with at most three leaves is a path or a subdivided `K₁,₃`). This
needs spanning trees, leaves and a minimality argument, which go beyond Lectures 1 - 6; we
state the propositions and leave the proofs as `sorry`.
-/

section propositions

variable {G} {X : SimpleGraph W}

/-- **Proposition 1.5.** Let `X` be a graph with maximum degree at most three. If `G` has an
`X`-minor, then `G` contains an `X`-subdivision.

*Proof sketch* (notes, p. 3). Let `H` be an `X`-model in `G` with as few vertices as possible,
with branch sets `V_x`. For each `x`, let `T_x` be the tree obtained from `H[V_x]` by adding,
for each neighbour `y` of `x` in `X`, the unique vertex of `V_y` adjacent to `V_x`. By
minimality of `H`, `T_x` is a tree with exactly `d_X(x) ≤ 3` leaves, hence a path or a
subdivision of `K₁,₃`. It follows that `H` is a subdivision of `X`. -/
theorem IsMinor.hasSubdivision_of_degree_le_three [Fintype V] [Fintype W] [DecidableRel X.Adj]
    (hX : ∀ x, X.degree x ≤ 3) (h : X.IsMinor G) : X.HasSubdivision G := by
  sorry

/-- **Proposition 1.6.** If `G` has a `K₅`-minor, then `G` contains a `K₅`- or a
`K₃,₃`-subdivision.

*Proof sketch* (notes, p. 3). Let `H` be a minimal `K₅`-model with branch sets `X₁, …, X₅`
and trees `T₁, …, T₅` as in Proposition 1.5; each `T_i` has exactly four leaves. If every `T_i`
has a vertex of degree four, `H` is a `K₅`-subdivision. Otherwise some `T₁` has maximum degree
three and is a subdivision of the "split `K₁,₄`"; contracting the other four branch sets to
single vertices gives a minor of `H` containing a `K₃,₃`-subdivision, so `G` has a
`K₃,₃`-minor, and by Proposition 1.5 (`K₃,₃` has maximum degree three) a `K₃,₃`-subdivision. -/
theorem hasSubdivision_or_of_K5_isMinor [Fintype V] (h : K5.IsMinor G) :
    K5.HasSubdivision G ∨ K33.HasSubdivision G := by
  sorry

end propositions

/-! ## Part 8: Kuratowski's theorem, minor version ↔ subdivision version

We can now prove the conclusion of Section 1 of the notes: "the minor version of Kuratowski's
Theorem is equivalent to the characterization in terms of subdivisions", i.e. (2) ↔ (3).
-/

section kuratowski

variable {G}

/-- Kuratowski's theorem, (3) → (2): if `G` has no `K₅`- and no `K₃,₃`-minor, then `G` contains
no `K₅`- and no `K₃,₃`-subdivision. This direction uses only Remark 1.1 (2) and is proved
completely. -/
theorem not_hasSubdivision_of_not_isMinor (h5 : ¬ K5.IsMinor G) (h33 : ¬ K33.IsMinor G) :
    ¬ K5.HasSubdivision G ∧ ¬ K33.HasSubdivision G := by
  constructor
  · intro h
    exact h5 h.isMinor
  · intro h
    exact h33 h.isMinor

/-- Kuratowski's theorem, (2) → (3): if `G` contains no `K₅`- and no `K₃,₃`-subdivision, then
`G` has no `K₅`- and no `K₃,₃`-minor. This direction uses Propositions 1.5 and 1.6. -/
theorem not_isMinor_of_not_hasSubdivision [Fintype V] (h5 : ¬ K5.HasSubdivision G)
    (h33 : ¬ K33.HasSubdivision G) : ¬ K5.IsMinor G ∧ ¬ K33.IsMinor G := by
  constructor
  · -- a `K₅`-minor gives a `K₅`- or a `K₃,₃`-subdivision (Proposition 1.6)
    intro h
    rcases hasSubdivision_or_of_K5_isMinor h with h' | h'
    · exact h5 h'
    · exact h33 h'
  · -- a `K₃,₃`-minor gives a `K₃,₃`-subdivision (Proposition 1.5, as `Δ(K₃,₃) = 3`)
    intro h
    exact h33 (h.hasSubdivision_of_degree_le_three K33_degree_le_three)

/-- **Kuratowski's theorem, (2) ↔ (3).** `G` has no `K₅`- or `K₃,₃`-subdivision if and only if
`G` has no `K₅`- or `K₃,₃`-minor. -/
theorem no_K5_K33_subdivision_iff_no_K5_K33_minor [Fintype V] :
    (¬ K5.HasSubdivision G ∧ ¬ K33.HasSubdivision G) ↔
      (¬ K5.IsMinor G ∧ ¬ K33.IsMinor G) := by
  constructor
  · rintro ⟨h5, h33⟩
    exact not_isMinor_of_not_hasSubdivision h5 h33
  · rintro ⟨h5, h33⟩
    exact not_hasSubdivision_of_not_isMinor h5 h33

/-- **Kuratowski's theorem**, minor version. Planarity is a topological notion (an embedding of
`G` in the plane) which is not part of this file. So we take any property `Planar` of graphs on
`V` and the theorem of last semester, (1) ↔ (2), as a hypothesis; the conclusion is the minor
version (1) ↔ (3). This is exactly the logical content of Section 1 of the notes. -/
theorem kuratowski [Fintype V] (Planar : SimpleGraph V → Prop)
    (kuratowski_subdivision : ∀ H : SimpleGraph V,
      Planar H ↔ ¬ K5.HasSubdivision H ∧ ¬ K33.HasSubdivision H) :
    Planar G ↔ ¬ K5.IsMinor G ∧ ¬ K33.IsMinor G := by
  rw [kuratowski_subdivision G]
  exact no_K5_K33_subdivision_iff_no_K5_K33_minor

end kuratowski

/-! ### Remark 1.7: minor-closed classes and excluded minors

A class of graphs is a property `P` of graphs (on vertex types in a fixed universe). -/

/-- `P` is *minor-closed* if every minor of a graph with property `P` has property `P`. -/
def MinorClosed (P : ∀ {α : Type u}, SimpleGraph α → Prop) : Prop :=
  ∀ {α β : Type u} (G : SimpleGraph α) (H : SimpleGraph β), P G → H.IsMinor G → P H

/-- `H` is an *excluded minor* for `P` if `H` does not have property `P` but every proper minor
of `H` (a minor not isomorphic to `H`) does. -/
def IsExcludedMinor (P : ∀ {α : Type u}, SimpleGraph α → Prop) {β : Type u}
    (H : SimpleGraph β) : Prop :=
  ¬ P H ∧ ∀ {γ : Type u} (H' : SimpleGraph γ), H'.IsMinor H → IsEmpty (H' ≃g H) → P H'

/-- Remark 1.7, the easy direction: a graph with property `P` has no excluded minor of `P` as
a minor. (The converse needs a minimal-counterexample argument over finite graphs.)

Kuratowski's theorem says, in this language, that the excluded minors for planarity are
exactly `K₅` and `K₃,₃` (Theorem 4.11 of the notes), and the Robertson–Seymour theorem says
that every minor-closed class has only finitely many excluded minors up to isomorphism. -/
theorem MinorClosed.not_isMinor_of_isExcludedMinor {P : ∀ {α : Type u}, SimpleGraph α → Prop}
    (hP : MinorClosed P) {α β : Type u} {G : SimpleGraph α} {H : SimpleGraph β} (hG : P G)
    (hH : IsExcludedMinor P H) : ¬ H.IsMinor G :=
  fun h ↦ hH.1 (hP G H hG h)

/-! ## Part 9: examples for you to try

Delete the `sorry`s. Everything can be done with the tactics of Lectures 1 - 6 and the lemmas
of this file. Solutions are at the end of the file.
-/

section exercises

variable {G} {X : SimpleGraph W}

/-- 1. In `G / uv`, the old neighbours `a` of `v` (with `a ≠ u`) are adjacent to `u`. -/
example (u v : V) (huv : u ≠ v) (a : {w : V // w ≠ v}) (hau : a.1 ≠ u) (h : G.Adj a v) :
    (G.contract u v).Adj a ⟨u, huv⟩ := by
  sorry

/-- 2. A minor of a subgraph is a minor. -/
example (H : SimpleGraph V) (hHG : H ≤ G) (hX : X.IsMinor H) : X.IsMinor G := by
  sorry

/-- 3. Contracting an edge and then deleting a vertex gives a minor. -/
example {u v : V} (huv : G.Adj u v) (a : {w : V // w ≠ v}) :
    ((G.contract u v).deleteVert a).IsMinor G := by
  sorry

/-- 4. If `G` contains no `X`-subdivision, then `G` contains no subgraph isomorphic to `X`. -/
example (h : ¬ X.HasSubdivision G) : ¬ X ⊑ G := by
  sorry

/-- 5. A graph with four vertices has no `K₅`-minor. -/
example (H : SimpleGraph (Fin 4)) : ¬ K5.IsMinor H := by
  sorry

/-! ### Solutions -/

/-- 1. -/
example (u v : V) (huv : u ≠ v) (a : {w : V // w ≠ v}) (hau : a.1 ≠ u) (h : G.Adj a v) :
    (G.contract u v).Adj a ⟨u, huv⟩ := by
  rw [contract_adj]
  constructor
  · exact hau
  · right
    right
    constructor
    · rfl
    · exact h

/-- 2. -/
example (H : SimpleGraph V) (hHG : H ≤ G) (hX : X.IsMinor H) : X.IsMinor G :=
  hX.trans (isMinor_of_le hHG)

/-- 3. -/
example {u v : V} (huv : G.Adj u v) (a : {w : V // w ≠ v}) :
    ((G.contract u v).deleteVert a).IsMinor G :=
  (isMinor_deleteVert (G.contract u v) a).trans (isMinor_contract G huv)

/-- 4. -/
example (h : ¬ X.HasSubdivision G) : ¬ X ⊑ G := by
  intro hX
  apply h
  exact hX.hasSubdivision

/-- 5. -/
example (H : SimpleGraph (Fin 4)) : ¬ K5.IsMinor H := by
  intro h
  have h' := h.card_le
  rw [Fintype.card_fin, Fintype.card_fin] at h'
  omega

end exercises

end SimpleGraph
