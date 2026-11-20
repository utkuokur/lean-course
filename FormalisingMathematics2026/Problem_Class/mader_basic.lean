/-
Basics for Mader's theorem
(R. Diestel, *Graph Theory*, 5th ed., Sections 1.1 - 1.4).

This file is a slow warm-up for `mader.lean`. It is self-contained: it repeats the definitions
of `mader.lean` (with the same names), so do not import both files at the same time.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.style.header false

/-!
# Basics for Mader's theorem

`mader.lean` starts with six definitions and five basic facts, and then the real proof begins.
In this file we go through exactly that first part again, but slowly.

**Revision of lecture  1 to 5.** In Parts 1 - 5 every proof uses only the tactics of Lectures 1 - 5:

* Lecture 1: `exact`, `intro`
* Lecture 2: `apply`, `specialize`, `have`, `suffices`, `left`, `right`, `constructor`,
  `rcases`, `by_contra`, `by_cases`
* Lecture 3: `use`, `def`, `theorem`, `#check`
* Lecture 4: `rfl`, `rw`
* Lecture 5: `refine`, term mode (`fun h ↦ ...`, `⟨_, _⟩`)

The only thing we add is *names of lemmas from Mathlib*, which we use with `rw`, `apply` and
`exact`, just as we used `add_comm` and `mul_add` in Lecture 4.

`mader.lean` also uses a few tactics that we have not met in Lectures 1 - 5 (`simp`, `linarith`,
`push_cast`, `exact_mod_cast`, `omega`, `calc`, ...). They are introduced in Part 6, one small
example each, and Part 7 uses them to explain the last proof we saw, `card_edgesIn_le`.

## Contents

* Part 1: what is a simple graph in Lean?
* Part 2: finite sets of vertices (`Finset`)
* Part 3: edges, neighbours and degrees
* Part 4: counting with fractions: `ε(G)` and `d(G)`
* Part 5: the remaining definitions of `mader.lean`: `edgesIn`, `nbrsIn`, `StarCond`,
  `IsKConnected`
* Part 6: the new tactics of `mader.lean`
* Part 7: the proof of `card_edgesIn_le`, line by line
* Part 8: examples for you to try
-/

open Finset

namespace SimpleGraph

/-! ## Part 1: what is a simple graph in Lean?

In Diestel a graph is a pair `G = (V, E)`. In Lean the vertices form a *type* `V`,
and a graph on `V` is a term `G : SimpleGraph V`. Such a `G` consists of three things:

* `G.Adj : V → V → Prop`   -- `G.Adj x y` is the proposition "`x` and `y` are adjacent"
* a proof that `G.Adj` is symmetric   -- edges have no direction
* a proof that `G.Adj` is irreflexive -- there are no loops

So a graph is just a relation, and "`xy` is an edge" is a proposition, exactly like the
`P` and `Q` of Lecture 2.
-/

#check SimpleGraph
#check SimpleGraph.Adj
#check SimpleGraph.adj_symm  -- `G.Adj u v → G.Adj v u`
#check SimpleGraph.irrefl    -- `¬ G.Adj v v`

/-
The next line is copied from `mader.lean`. It fixes the setting for the whole file:

* `{V : Type*}`           -- `V` is the type of vertices
* `[Fintype V]`           -- `V` has only finitely many terms, so `|G|` makes sense
* `[DecidableEq V]`       -- Lean can decide whether `x = y`      (needed for counting)
* `(G : SimpleGraph V)`   -- `G` is a graph on `V`
* `[DecidableRel G.Adj]`  -- Lean can decide whether `G.Adj x y`  (needed for counting)

The square brackets are assumptions that Lean handles by itself; you can ignore them.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edges have no direction. (Lecture 1: `intro` and `exact`.) -/
example (x y : V) : G.Adj x y → G.Adj y x := by
  intro h
  exact G.adj_symm h

/-- The same statement as an "if and only if". (Lecture 4: `constructor` on `↔`.) -/
example (x y : V) : G.Adj x y ↔ G.Adj y x := by
  constructor
  · intro h
    exact G.adj_symm h
  · intro h
    exact G.adj_symm h

/-- There are no loops. Remember that `¬ P` means `P → False`. (Lecture 2.) -/
example (v : V) : ¬ G.Adj v v := by
  intro h
  exact G.irrefl h

/-- Adjacent vertices are different. `x ≠ y` means `x = y → False`, so we can `intro`.
(Lecture 4: `rw ... at`.) -/
example (x y : V) : G.Adj x y → x ≠ y := by
  intro h hxy
  rw [hxy] at h
  exact G.irrefl h

/-- The same proof in term mode, using the Mathlib name of this fact. (Lecture 5.) -/
example (x y : V) : G.Adj x y → x ≠ y :=
  fun h ↦ G.ne_of_adj h

/-
A concrete graph to keep in mind: the complete graph `K₄` on the four vertices `0, 1, 2, 3`.
In Lean the complete graph is called `⊤`, and `Fin 4` is the type with terms `0, 1, 2, 3`.
In `K₄` two vertices are adjacent if and only if they are different.
-/

example (x y : Fin 4) : (⊤ : SimpleGraph (Fin 4)).Adj x y ↔ x ≠ y := by
  rw [top_adj]

/-! ## Part 2: finite sets of vertices (`Finset`)

Mader's proof is about vertex sets `U ⊆ V` and the induced subgraphs `G[U]`.
In Lean a finite set of vertices is a term `U : Finset V`.

* `x ∈ U`     -- a proposition
* `U ⊆ W`     -- *by definition* `∀ x, x ∈ U → x ∈ W`, so we can use `intro x hx`
* `U ∩ W`, `U ∪ W`, `U \ W`, `U.erase v`  -- new finite sets
* `univ`      -- the set of all vertices
* `#U`        -- the number of elements of `U`, a natural number (Diestel: `|U|`)

Each construction comes with a *membership lemma*. We use them with `rw` (Lecture 4),
and after that only logic (Lecture 2) is left.
-/

#check @Finset.mem_inter   -- `a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t`
#check @Finset.mem_union   -- `a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t`
#check @Finset.mem_sdiff   -- `a ∈ s \ t ↔ a ∈ s ∧ a ∉ t`
#check @Finset.mem_erase   -- `a ∈ s.erase b ↔ a ≠ b ∧ a ∈ s`
#check @Finset.mem_filter  -- `a ∈ {x ∈ s | p x} ↔ a ∈ s ∧ p a`
#check @Finset.mem_univ    -- `a ∈ univ`

example (U W : Finset V) : U ∩ W ⊆ U := by
  intro x hx
  rw [mem_inter] at hx
  rcases hx with ⟨hxU, hxW⟩
  exact hxU

example (U W : Finset V) : U ⊆ U ∪ W := by
  intro x hx
  rw [mem_union]
  left
  exact hx

example (U W : Finset V) : U \ W ⊆ U := by
  intro x hx
  rw [mem_sdiff] at hx
  rcases hx with ⟨hxU, hxW⟩
  exact hxU

/-- Every set of vertices is contained in the set of all vertices. -/
example (U : Finset V) : U ⊆ univ := by
  intro x hx
  exact mem_univ x

/-- `{x ∈ U | P x}` is the set of those `x ∈ U` with the property `P`. -/
example (U : Finset V) (P : V → Prop) [DecidablePred P] : {x ∈ U | P x} ⊆ U := by
  intro x hx
  rw [mem_filter] at hx
  rcases hx with ⟨hxU, hPx⟩
  exact hxU

/-- Two finite sets are equal if they have the same elements: this is `Finset.ext`.
After `apply Finset.ext` we must prove an `↔` for every `x`. -/
example (U : Finset V) : U ∩ univ = U := by
  apply Finset.ext
  intro x
  rw [mem_inter]
  constructor
  · intro h
    rcases h with ⟨hxU, hx⟩
    exact hxU
  · intro h
    constructor
    · exact h
    · exact mem_univ x

/-- `|G|`, the number of vertices of `G`, is `Fintype.card V`. It is also `#univ`. -/
example : #(univ : Finset V) = Fintype.card V := by
  rw [card_univ]

/-! ## Part 3: edges, neighbours and degrees

* An edge is an unordered pair. The type of unordered pairs of vertices is `Sym2 V`, and the
  unordered pair `{x, y}` is written `s(x, y)`. So `s(x, y) = s(y, x)`.
* `G.edgeFinset : Finset (Sym2 V)` is the edge set `E(G)`; so `‖G‖ = #G.edgeFinset`.
* `G.neighborFinset v : Finset V` is the set `N(v)` of neighbours of `v`.
* `G.degree v : ℕ` is the degree `d(v)`.
-/

#check @Sym2.eq_swap                  -- `s(a, b) = s(b, a)`
#check @SimpleGraph.mem_edgeFinset    -- `e ∈ G.edgeFinset ↔ e ∈ G.edgeSet`
#check @SimpleGraph.mem_edgeSet       -- `s(v, w) ∈ G.edgeSet ↔ G.Adj v w`
#check @SimpleGraph.mem_neighborFinset  -- `w ∈ G.neighborFinset v ↔ G.Adj v w`

/-- `{x, y}` is an edge of `G` if and only if `x` and `y` are adjacent. -/
theorem mk_mem_edgeFinset (x y : V) : s(x, y) ∈ G.edgeFinset ↔ G.Adj x y := by
  rw [mem_edgeFinset, mem_edgeSet]

/-- An unordered pair does not care about the order. -/
example (x y : V) : s(x, y) ∈ G.edgeFinset → s(y, x) ∈ G.edgeFinset := by
  intro h
  rw [Sym2.eq_swap]
  exact h

/-- The degree of `v` is *by definition* the number of neighbours of `v`. -/
theorem degree_def (v : V) : G.degree v = #(G.neighborFinset v) := by
  rfl

/-- `w` is a neighbour of `v` if and only if `v` is a neighbour of `w`. -/
example (v w : V) : w ∈ G.neighborFinset v ↔ v ∈ G.neighborFinset w := by
  rw [mem_neighborFinset, mem_neighborFinset]
  constructor
  · intro h
    exact G.adj_symm h
  · intro h
    exact G.adj_symm h

/-- A vertex is not its own neighbour. -/
example (v : V) : v ∉ G.neighborFinset v := by
  intro h
  rw [mem_neighborFinset] at h
  exact G.irrefl h

/-- Every neighbour of `v` is different from `v`: `N(v) ⊆ V - v`. -/
example (v : V) : G.neighborFinset v ⊆ univ.erase v := by
  intro w hw
  rw [mem_neighborFinset] at hw
  rw [mem_erase]
  constructor
  · intro hwv
    rw [hwv] at hw
    exact G.irrefl hw
  · exact mem_univ w

/-
In `K₄` every vertex has degree `3` and there are `6` edges. The tactic `decide` asks Lean to
simply compute both sides. (It only works for small concrete examples like this one.)
-/

example : (⊤ : SimpleGraph (Fin 4)).degree 0 = 3 := by
  decide

example : #(⊤ : SimpleGraph (Fin 4)).edgeFinset = 6 := by
  decide

/-
The **handshake lemma** (Diestel, Section 1.2): the sum of all degrees is twice the number of
edges, because every edge is counted once from each of its two ends.
`∑ v, f v` is the sum of `f v` over all vertices `v`. This lemma is already in Mathlib:
-/

#check @SimpleGraph.sum_degrees_eq_twice_card_edges  -- `∑ v, G.degree v = 2 * #G.edgeFinset`

/-! ## Part 4: counting with fractions: `ε(G)` and `d(G)`

Diestel defines

* `ε(G) = ‖G‖ / |G|`               -- the number of edges per vertex
* `d(G) = (1 / |G|) ∑ᵥ d(v)`       -- the average degree

These are fractions, but `‖G‖`, `|G|` and `d(v)` are natural numbers. Recall from Lecture 3
that every term has exactly one type: `(7 : ℕ)` and `(7 : ℚ)` are different terms.
And division of natural numbers in Lean rounds down!
-/

#eval (7 / 2 : ℕ)  -- `3`
#eval (7 / 2 : ℚ)  -- `7/2`

/-
So before we divide we must move our numbers from `ℕ` to `ℚ`. This is written `(n : ℚ)`,
and the infoview shows it as an arrow `↑n`. It is called a *cast* (or coercion).
In the two definitions below, the `: ℚ` after `noncomputable def ...` and the `(... : ℚ)`
inside are exactly these casts.

(`noncomputable` only tells Lean that we will not run this definition as a program.)
-/

/-- The average degree `d(G) = (1 / |G|) ∑ᵥ d(v)` of `G` (Diestel, Section 1.2). -/
noncomputable def avgDegree : ℚ := (∑ v, (G.degree v : ℚ)) / Fintype.card V

/-- The number of edges per vertex, `ε(G) = ‖G‖ / |G|` (Diestel, Section 1.2) -/
noncomputable def edgeRatio : ℚ := ((G.edgeFinset.card : ℚ) / Fintype.card V)

/-
Since `G` is the first explicit argument, we may write `G.avgDegree` instead of `avgDegree G`.

A definition is just an abbreviation. Lecture 4: `rfl` proves an equality when both sides
agree after unfolding all definitions. So each definition gives us a rewriting rule for free.
-/

theorem avgDegree_def : G.avgDegree = (∑ v, (G.degree v : ℚ)) / Fintype.card V := by
  rfl

theorem edgeRatio_def : G.edgeRatio = (#G.edgeFinset : ℚ) / Fintype.card V := by
  rfl

/-- In `K₄` we have `ε = 6 / 4 = 3 / 2`. (`norm_num` does arithmetic with concrete numbers,
see Part 6.) -/
example : (⊤ : SimpleGraph (Fin 4)).edgeRatio = 3 / 2 := by
  have h : #(⊤ : SimpleGraph (Fin 4)).edgeFinset = 6 := by
    decide
  rw [edgeRatio_def, h, Fintype.card_fin]
  norm_num

/-
Casts obey the rules you expect, and each rule has a name:
-/

#check @Nat.cast_sum    -- `↑(∑ x ∈ s, f x) = ∑ x ∈ s, ↑(f x)`
#check @Nat.cast_mul    -- `↑(m * n) = ↑m * ↑n`
#check @Nat.cast_add    -- `↑(m + n) = ↑m + ↑n`
#check @Nat.cast_ofNat  -- `↑2 = 2`  (the natural number `2` becomes the rational number `2`)
#check @mul_div_assoc   -- `a * b / c = a * (b / c)`

/-- `d(G) = 2 ε(G)`, by the handshake lemma (Diestel, (1.2.2)).

This is the first theorem of `mader.lean`. Here it is proved with `rw` only (Lecture 4).
Put your cursor after each comma and watch the goal change:

* `avgDegree_def`, `edgeRatio_def`  -- unfold the two definitions
* `← Nat.cast_sum`                  -- `∑ v, ↑(d v)` becomes `↑(∑ v, d v)`
* `sum_degrees_eq_twice_card_edges` -- handshake: `∑ v, d v` becomes `2 * ‖G‖`
* `Nat.cast_mul`, `Nat.cast_ofNat`  -- `↑(2 * ‖G‖)` becomes `2 * ↑‖G‖`
* `mul_div_assoc`                   -- `2 * ↑‖G‖ / ↑|G|` becomes `2 * (↑‖G‖ / ↑|G|)`

Now both sides are the same, and `rw` closes the goal with `rfl`. -/
theorem avgDegree_eq_two_mul_edgeRatio : G.avgDegree = 2 * G.edgeRatio := by
  rw [avgDegree_def, edgeRatio_def, ← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges,
    Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc]

/-- The hypothesis `d(G) ≥ 4k` of Mader's theorem only enters through this theorem: it says
`ε(G) ≥ 2k`. For example, if `d(G) = 4k` then `ε(G) = 2k`. -/
example (k : ℚ) (h : G.avgDegree = 2 * (2 * k)) : 2 * G.edgeRatio = 2 * (2 * k) := by
  rw [avgDegree_eq_two_mul_edgeRatio] at h
  exact h

/-! ## Part 5: the remaining definitions of `mader.lean`

### `edgesIn`: the edges of `G[U]`

For `U ⊆ V`, Diestel writes `G[U]` for the induced subgraph: its vertices are `U` and its edges
are all edges of `G` with both ends in `U`. We do not build a new graph; we just *select* those
edges of `G`. For an edge `e`, the finite set `e.toFinset` is the set of its (two) ends.
-/

/-- The edges of `G` with both ends in `U`; these are exactly the edges of `G[U]`. -/
def edgesIn (U : Finset V) : Finset (Sym2 V) := {e ∈ G.edgeFinset | e.toFinset ⊆ U}

#check @Sym2.toFinset_mk_eq            -- `s(a, b).toFinset = {a, b}`
#check @Finset.insert_subset_iff       -- `insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t`
#check @Finset.singleton_subset_iff    -- `{a} ⊆ s ↔ a ∈ s`

/-- The membership lemma for `edgesIn`: unfold the definition, then use `mem_filter`. -/
theorem mem_edgesIn {U : Finset V} {e : Sym2 V} :
    e ∈ G.edgesIn U ↔ e ∈ G.edgeFinset ∧ e.toFinset ⊆ U := by
  rw [edgesIn, mem_filter]

/-- `{x, y}` is an edge of `G[U]` iff `x`, `y` are adjacent and both lie in `U`.

In `mader.lean` this is proved by `simp`. Here we do the same steps by hand with `rw`.
(The set `{x, y}` is `insert x {y}`, which is why `insert_subset_iff` appears.) -/
theorem mk_mem_edgesIn {U : Finset V} {x y : V} :
    s(x, y) ∈ G.edgesIn U ↔ G.Adj x y ∧ x ∈ U ∧ y ∈ U := by
  rw [mem_edgesIn, mem_edgeFinset, mem_edgeSet, Sym2.toFinset_mk_eq, insert_subset_iff,
    singleton_subset_iff]

/-- Every edge of `G[U]` is an edge of `G`. -/
theorem edgesIn_subset_edgeFinset (U : Finset V) : G.edgesIn U ⊆ G.edgeFinset := by
  intro e he
  rw [mem_edgesIn] at he
  rcases he with ⟨heG, heU⟩
  exact heG

/-- A bigger vertex set induces more edges: if `U ⊆ W` then `E(G[U]) ⊆ E(G[W])`. -/
theorem edgesIn_mono {U W : Finset V} (hUW : U ⊆ W) : G.edgesIn U ⊆ G.edgesIn W := by
  intro e he
  rw [mem_edgesIn] at he
  rw [mem_edgesIn]
  rcases he with ⟨heG, heU⟩
  constructor
  · exact heG
  · intro x hx
    apply hUW
    apply heU
    exact hx

/-- `G[V] = G`: if `U` is the set of all vertices, we select all edges. -/
theorem edgesIn_univ : G.edgesIn univ = G.edgeFinset := by
  apply Finset.ext
  intro e
  rw [mem_edgesIn]
  constructor
  · intro h
    rcases h with ⟨heG, heU⟩
    exact heG
  · intro h
    constructor
    · exact h
    · intro x hx
      exact mem_univ x

/-- An edge with an end outside `U` is not an edge of `G[U]`. -/
example (U : Finset V) (x y : V) (hx : x ∉ U) : s(x, y) ∉ G.edgesIn U := by
  intro h
  rw [mk_mem_edgesIn] at h
  rcases h with ⟨hadj, hxU, hyU⟩
  exact hx hxU

/-! ### `nbrsIn`: the neighbours inside `U`

The degree of `v` in `G[U]` is the number of neighbours of `v` that lie in `U`.
-/

/-- The neighbours of `v` lying in `U`; their number is the degree of `v` in `G[U]`. -/
def nbrsIn (U : Finset V) (v : V) : Finset V := G.neighborFinset v ∩ U

/-- The membership lemma for `nbrsIn`. -/
theorem mem_nbrsIn {U : Finset V} {v w : V} : w ∈ G.nbrsIn U v ↔ G.Adj v w ∧ w ∈ U := by
  rw [nbrsIn, mem_inter, mem_neighborFinset]

theorem nbrsIn_subset (U : Finset V) (v : V) : G.nbrsIn U v ⊆ U := by
  intro w hw
  rw [mem_nbrsIn] at hw
  rcases hw with ⟨hadj, hwU⟩
  exact hwU


/-- A vertex is not its own neighbour, so `d_{G[U]}(v) ≤ |U| - 1`.

This is the *next* theorem of `mader.lean` (the first one we have not yet discussed).
It needs nothing beyond Lectures 1 - 5. -/
theorem nbrsIn_subset_erase (U : Finset V) (v : V) : G.nbrsIn U v ⊆ U.erase v := by
  intro w hw
  rw [mem_nbrsIn] at hw
  rcases hw with ⟨hadj, hwU⟩
  rw [mem_erase]
  constructor
  · intro hwv
    rw [hwv] at hadj
    exact G.irrefl hadj
  · exact hwU

/-! ### `StarCond`: condition `(∗)` of Diestel's proof

Diestel puts `γ := ε(G)` and looks at the subgraphs `G' = G[U]` of `G` such that

  `(∗)`   `|G'| ≥ 2k`   and   `‖G'‖ > γ (|G'| - k)`.

In Lean this is a *predicate* on vertex sets: for every `U`, `G.StarCond k U` is a proposition.
Compare with `P : α → Prop` in Lecture 3.

Look at the types: `2 * k ≤ #U` is an inequality in `ℕ`. The second part is an inequality in
`ℚ`, because `G.edgeRatio : ℚ`; Lean inserts the casts `↑#U`, `↑k` and `↑#(G.edgesIn U)`
automatically. This matters: in `ℕ` the subtraction `#U - k` would be truncated (Lecture 3).
-/

/-- Condition `(∗)` of Diestel's proof, with `γ = ε(G)`: `|U| ≥ 2k` and `‖G[U]‖ > γ (|U| - k)`. -/
def StarCond (k : ℕ) (U : Finset V) : Prop :=
  2 * k ≤ #U ∧ G.edgeRatio * (#U - k) < #(G.edgesIn U)

theorem starCond_def (k : ℕ) (U : Finset V) :
    G.StarCond k U ↔ 2 * k ≤ #U ∧ G.edgeRatio * (#U - k) < #(G.edgesIn U) := by
  rfl

/-- `StarCond` is an "and", so `rcases` splits a hypothesis `h : G.StarCond k U` in two. -/
example (k : ℕ) (U : Finset V) (h : G.StarCond k U) : 2 * k ≤ #U := by
  rcases h with ⟨h1, h2⟩
  exact h1

/-- To *prove* `(∗)` we first rewrite with `starCond_def`, then `constructor` gives two goals. -/
example (k : ℕ) (U : Finset V) (h1 : 2 * k ≤ #U)
    (h2 : G.edgeRatio * (#U - k) < #(G.edgesIn U)) : G.StarCond k U := by
  rw [starCond_def]
  constructor
  · exact h1
  · exact h2

/-- The same in term mode (Lecture 5). -/
example (k : ℕ) (U : Finset V) (h1 : 2 * k ≤ #U)
    (h2 : G.edgeRatio * (#U - k) < #(G.edgesIn U)) : G.StarCond k U :=
  ⟨h1, h2⟩

/-- For `U = V` condition `(∗)` talks about `G` itself: `|G| ≥ 2k` and `‖G‖ > γ (|G| - k)`.
(That `G` really satisfies this is `starCond_univ` in `mader.lean`.) -/
example (k : ℕ) (h : G.StarCond k univ) :
    2 * k ≤ Fintype.card V ∧ G.edgeRatio * (Fintype.card V - k) < #G.edgeFinset := by
  rw [starCond_def, edgesIn_univ, card_univ] at h
  exact h

/-! ### `IsKConnected`: `k`-connected graphs

Diestel, Section 1.4: `H` is `k`-connected if `|H| > k` and `H - X` is connected for every set
`X` of fewer than `k` vertices.

* `H.induce S` is the induced subgraph `H[S]` on a set `S` of vertices (a new graph!).
* `Xᶜ` is the complement of `X`, so `H.induce Xᶜ` is `H - X`.
* `X.ncard` is the number of elements of the set `X`.
* `.Connected` is Mathlib's definition of a connected graph.
-/

#check @SimpleGraph.induce
#check @SimpleGraph.Connected

/-- Diestel, Section 1.4: a graph `H` is `k`-connected if `|H| > k` and `H - X` is connected for
every set `X` of fewer than `k` vertices. Here `H - X` is the induced subgraph `H.induce Xᶜ`. -/
def IsKConnected {W : Type*} [Fintype W] (H : SimpleGraph W) (k : ℕ) : Prop :=
  k < Fintype.card W ∧ ∀ X : Set W, X.ncard < k → (H.induce Xᶜ).Connected

theorem isKConnected_def {W : Type*} [Fintype W] (H : SimpleGraph W) (k : ℕ) :
    H.IsKConnected k ↔
      k < Fintype.card W ∧ ∀ X : Set W, X.ncard < k → (H.induce Xᶜ).Connected := by
  rfl


/-- A `k`-connected graph has more than `k` vertices. -/
example {W : Type*} [Fintype W] (H : SimpleGraph W) (k : ℕ) (h : H.IsKConnected k) :
    k < Fintype.card W := by
  rcases h with ⟨hcard, hconn⟩
  exact hcard

/-- The second half of the definition is a `∀`, so we use it with `specialize` (Lecture 3):
in a `2`-connected graph, deleting one vertex set `X` with `|X| < 2` leaves a connected graph. -/
example {W : Type*} [Fintype W] (H : SimpleGraph W) (h : H.IsKConnected 2)
    (X : Set W) (hX : X.ncard < 2) : (H.induce Xᶜ).Connected := by
  rcases h with ⟨hcard, hconn⟩
  specialize hconn X
  apply hconn
  exact hX

#check @lt_trans         -- `a < b → b < c → a < c`
#check @Nat.lt_succ_self -- `n < n + 1`

/-- A `(k + 1)`-connected graph is `k`-connected: deleting fewer than `k` vertices is in
particular deleting fewer than `k + 1` vertices. -/
theorem IsKConnected.of_succ {W : Type*} [Fintype W] {H : SimpleGraph W} {k : ℕ}
    (h : H.IsKConnected (k + 1)) : H.IsKConnected k := by
  rcases h with ⟨hcard, hconn⟩
  rw [isKConnected_def]
  constructor
  · exact lt_trans (Nat.lt_succ_self k) hcard
  · intro X hX
    apply hconn
    exact lt_trans hX (Nat.lt_succ_self k)

/-! ## Part 6: the new tactics of `mader.lean`

Everything above used only Lectures 1 - 5. But proving every inequality between numbers by
naming lemmas is painful. `mader.lean` therefore uses some *automation*: tactics that search
for the proof themselves. You do not need to know how they work, only **what kind of goal each
of them closes**. Here is each of them in one small example.
-/

/-- `unfold d` replaces the name `d` by its definition (like our `rw [edgeRatio_def]`). -/
example : G.edgeRatio = (#G.edgeFinset : ℚ) / Fintype.card V := by
  unfold edgeRatio
  rfl

/-- `simp` rewrites again and again with hundreds of Mathlib lemmas marked "simplification
lemma", until nothing changes. Compare with our seven-line proof of the same fact in Part 2. -/
example (U : Finset V) : U ∩ univ = U := by
  simp

/-- `simp [a, b]` also uses the definitions/lemmas `a`, `b` that we hand to it.
Compare with our proof of `edgesIn_univ` in Part 5. -/
example : G.edgesIn univ = G.edgeFinset := by
  simp [edgesIn]

/-- `ring` proves equations that follow from the rules of `+`, `*`, `-`, `/` alone. -/
example (a b : ℚ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- `norm_num` does arithmetic with concrete numbers. -/
example : (6 : ℚ) / 4 = 3 / 2 := by
  norm_num

/-- `linarith` proves linear inequalities from the hypotheses (add them up, multiply them by
constants). You may also pass extra facts: `linarith [h3]`. -/
example (x y : ℚ) (h1 : x ≤ y) (h2 : 2 * y < 6) : x < 3 := by
  linarith

/-- `nlinarith` is `linarith` that also tries multiplying hypotheses with each other. -/
example (x y : ℚ) (hx : 0 ≤ x) (hxy : x ≤ y) : x * x ≤ y * y := by
  nlinarith

/-- `omega` is `linarith` for the natural numbers and integers. It knows that in `ℕ` there is
nothing between `n` and `n + 1`, and it understands truncated subtraction. -/
example (n k : ℕ) (hk : 1 ≤ k) (h : 2 * k < n) : k + 1 < n := by
  omega

/-- `push_cast` moves the casts `↑` towards the leaves, using `Nat.cast_add`, `Nat.cast_mul`,
... for us. Compare with `Nat.cast_mul, Nat.cast_ofNat` in `avgDegree_eq_two_mul_edgeRatio`. -/
example (a b : ℕ) : ((2 * a + b : ℕ) : ℚ) = 2 * (a : ℚ) + (b : ℚ) := by
  push_cast
  rfl

/-- `exact_mod_cast h` is `exact h`, "up to casts": `h` is a fact about natural numbers,
the goal is the same fact about their casts to `ℚ`. -/
example (a b : ℕ) (h : a ≤ b) : (a : ℚ) ≤ (b : ℚ) := by
  exact_mod_cast h

/-- `calc` writes a chain `a ≤ b ≤ c` as on paper; each step gets its own small proof. -/
example (a b c : ℚ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  calc a ≤ b := by exact h1
    _ ≤ c := by exact h2

/-- `obtain ⟨hP, hQ⟩ := h` is the same as `rcases h with ⟨hP, hQ⟩`. And for `h : P ∧ Q`,
`h.1 : P` and `h.2 : Q` are its two parts. -/
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  exact ⟨hQ, hP⟩

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  ⟨h.2, h.1⟩

/-- `simpa using h` means: simplify `h`, simplify the goal, and then `exact h`. -/
example (U : Finset V) (x : V) (h : x ∈ U ∩ univ) : x ∈ U := by
  simpa using h

/-! ## Part 7: the proof of `card_edgesIn_le`, line by line

We now reread the last two facts from the previous lecture.

The first one says that our hand-made `G.edgesIn U` has as many elements as the edge set of the
"official" induced subgraph `G.induce ↑U` of Mathlib. (`↑U` is `U` viewed as a `Set V`.)
This is exactly a lemma of Mathlib, so the proof is just its name (term mode, Lecture 5).
-/

/-- `#(G.edgesIn U)` really is the number of edges of the induced subgraph `G[U]`. -/
theorem card_edgesIn (U : Finset V) : #(G.edgesIn U) = #(G.induce ↑U).edgeFinset :=
  G.card_filter_edgeFinset_toFinset_subset U

/-
The second one is the bound `‖G[U]‖ ≤ (|U| choose 2) ≤ |U|² / 2`:
a graph on `n` vertices has at most `n (n - 1) / 2 ≤ n² / 2` edges.

The two ingredients are in Mathlib:
-/

#check @SimpleGraph.card_edgeFinset_le_card_choose_two  -- `#G.edgeFinset ≤ (|G|).choose 2`
#check @Nat.choose_le_pow_div                           -- `↑(n.choose r) ≤ ↑n ^ r / ↑r !`

/-- `‖G[U]‖ ≤ (|U| choose 2) ≤ |U|² / 2`. -/
theorem card_edgesIn_le (U : Finset V) : (#(G.edgesIn U) : ℚ) ≤ (#U : ℚ) ^ 2 / 2 := by
  -- Step 1, in `ℕ`: `‖G[U]‖ ≤ (|U| choose 2)`.
  have h1 : #(G.edgesIn U) ≤ (#U).choose 2 := by
    -- replace `#(G.edgesIn U)` by the number of edges of the graph `G.induce ↑U`
    rw [card_edgesIn]
    -- Mathlib's lemma for the graph `G.induce ↑U` says `‖G[U]‖ ≤ (|G[U]| choose 2)`;
    -- `simpa` simplifies the number of vertices `|G[U]|` to `#U`
    simpa using (G.induce ↑U).card_edgeFinset_le_card_choose_two
  -- Step 2, in `ℚ`: `(|U| choose 2) ≤ |U|² / 2!`.
  have h2 := Nat.choose_le_pow_div (α := ℚ) 2 (#U)
  -- compute `2! = 2` inside `h2`
  norm_num [Nat.factorial] at h2
  -- Step 3: chain the two inequalities, as on paper.
  calc (#(G.edgesIn U) : ℚ) ≤ (#U).choose 2 := by exact_mod_cast h1  -- `h1`, moved to `ℚ`
    _ ≤ (#U : ℚ) ^ 2 / 2 := by linarith                               -- this is `h2`

/-! ## Part 8: examples for you to try

Delete the `sorry`s. Everything can be done with the tactics of Lectures 1 - 5 and the
membership lemmas `mem_inter`, `mem_neighborFinset`, `mem_nbrsIn`, `mk_mem_edgesIn`, ...
Solutions are at the end of the file.
-/

/-- 1. Adjacent vertices are neighbours of each other. -/
example (x y : V) (h : G.Adj x y) : y ∈ G.neighborFinset x ∧ x ∈ G.neighborFinset y := by
 sorry
--solved
example (x y : V) (h : G.Adj x y) : y ∈ G.neighborFinset x ∧ x ∈ G.neighborFinset y := by
  rw [mem_neighborFinset, mem_neighborFinset]
  constructor
  · exact h
  · exact G.adj_symm h


/-- 2. Non-adjacent vertices do not form an edge of `G[U]`. -/
example (U : Finset V) (x y : V) (h : ¬ G.Adj x y) : s(x, y) ∉ G.edgesIn U := by
  sorry

example (U : Finset V) (x y : V) (h : ¬ G.Adj x y) : s(x, y) ∉ G.edgesIn U := by
  intro he
  rw [mk_mem_edgesIn] at he
  rcases he with ⟨hadj, hx, hy⟩
  exact h hadj

/-- 3. A smaller vertex set contains fewer neighbours. -/
example (U W : Finset V) (v : V) : G.nbrsIn (U ∩ W) v ⊆ G.nbrsIn U v := by
  sorry
example (U W : Finset V) (v : V) : G.nbrsIn (U ∩ W) v ⊆ G.nbrsIn U v := by
  intro w hw
  rw [mem_nbrsIn, mem_inter] at hw
  rw [mem_nbrsIn]
  rcases hw with ⟨hadj, hwU, hwW⟩
  constructor
  · exact hadj
  · exact hwU


/-- 4. If `v ∈ U` and `w` is a neighbour of `v` in `G[U]`, then `vw` is an edge of `G[U]`.
(This is used in `card_edgesIn_erase`, the next big step of `mader.lean`.) -/
example (U : Finset V) (v w : V) (hv : v ∈ U) (hw : w ∈ G.nbrsIn U v) :
    s(v, w) ∈ G.edgesIn U := by
  sorry

example (U : Finset V) (v w : V) (hv : v ∈ U) (hw : w ∈ G.nbrsIn U v) :
    s(v, w) ∈ G.edgesIn U := by
  rw [mem_nbrsIn] at hw
  rcases hw with ⟨hadj, hwU⟩
  rw [mk_mem_edgesIn]
  exact ⟨hadj, hv, hwU⟩

/-- 5. Being neighbours inside `U` is symmetric. -/
example (U : Finset V) (v w : V) (hv : v ∈ U) (hw : w ∈ G.nbrsIn U v) : v ∈ G.nbrsIn U w := by
  sorry
example (U : Finset V) (v w : V) (hv : v ∈ U) (hw : w ∈ G.nbrsIn U v) : v ∈ G.nbrsIn U w := by
  rw [mem_nbrsIn] at hw
  rcases hw with ⟨hadj, hwU⟩
  rw [mem_nbrsIn]
  constructor
  · exact G.adj_symm hadj
  · exact hv

/-- 6. An edge of `G[U]` and of `G[W]` is an edge of `G[U ∩ W]`. -/
example (U W : Finset V) (x y : V) (hU : s(x, y) ∈ G.edgesIn U) (hW : s(x, y) ∈ G.edgesIn W) :
    s(x, y) ∈ G.edgesIn (U ∩ W) := by
  sorry

/-- 7. If `d(G) = 4k` then `ε(G) = 2k`... written without division. -/
example (k : ℚ) (h : 2 * (2 * k) = G.avgDegree) : 2 * (2 * k) = 2 * G.edgeRatio := by
  sorry

/-! ### Solutions -/

/-- 1. -/
example (x y : V) (h : G.Adj x y) : y ∈ G.neighborFinset x ∧ x ∈ G.neighborFinset y := by
  rw [mem_neighborFinset, mem_neighborFinset]
  constructor
  · exact h
  · exact G.adj_symm h

/-- 2. -/
example (U : Finset V) (x y : V) (h : ¬ G.Adj x y) : s(x, y) ∉ G.edgesIn U := by
  intro he
  rw [mk_mem_edgesIn] at he
  rcases he with ⟨hadj, hx, hy⟩
  exact h hadj

/-- 3. -/
example (U W : Finset V) (v : V) : G.nbrsIn (U ∩ W) v ⊆ G.nbrsIn U v := by
  intro w hw
  rw [mem_nbrsIn, mem_inter] at hw
  rw [mem_nbrsIn]
  rcases hw with ⟨hadj, hwU, hwW⟩
  constructor
  · exact hadj
  · exact hwU

/-- 4. -/
example (U : Finset V) (v w : V) (hv : v ∈ U) (hw : w ∈ G.nbrsIn U v) :
    s(v, w) ∈ G.edgesIn U := by
  rw [mem_nbrsIn] at hw
  rcases hw with ⟨hadj, hwU⟩
  rw [mk_mem_edgesIn]
  exact ⟨hadj, hv, hwU⟩

/-- 5. -/
example (U : Finset V) (v w : V) (hv : v ∈ U) (hw : w ∈ G.nbrsIn U v) : v ∈ G.nbrsIn U w := by
  rw [mem_nbrsIn] at hw
  rcases hw with ⟨hadj, hwU⟩
  rw [mem_nbrsIn]
  constructor
  · exact G.adj_symm hadj
  · exact hv

/-- 6. -/
example (U W : Finset V) (x y : V) (hU : s(x, y) ∈ G.edgesIn U) (hW : s(x, y) ∈ G.edgesIn W) :
    s(x, y) ∈ G.edgesIn (U ∩ W) := by
  rw [mk_mem_edgesIn] at hU
  rw [mk_mem_edgesIn] at hW
  rcases hU with ⟨hadj, hxU, hyU⟩
  rcases hW with ⟨hadj', hxW, hyW⟩
  rw [mk_mem_edgesIn, mem_inter, mem_inter]
  exact ⟨hadj, ⟨hxU, hxW⟩, ⟨hyU, hyW⟩⟩

/-- 7. -/
example (k : ℚ) (h : 2 * (2 * k) = G.avgDegree) : 2 * (2 * k) = 2 * G.edgeRatio := by
  rw [avgDegree_eq_two_mul_edgeRatio] at h
  exact h

end SimpleGraph
