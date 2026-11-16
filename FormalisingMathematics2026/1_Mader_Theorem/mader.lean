/-
Mader's theorem on highly connected subgraphs
(R. Diestel, *Graph Theory*, 5th ed., Theorem 1.4.3; W. Mader, 1972).
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic
import Mathlib.Data.Set.Finite.Basic

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.header false
/-!
# Mader's theorem (Diestel, Theorem 1.4.3)

**Theorem (Mader 1972).** Let `0 ≠ k ∈ ℕ`. Every graph `G` with average degree `d(G) ≥ 4k`
has a `(k + 1)`-connected subgraph `H` such that `ε(H) > ε(G) - k`.

Notation, as in Diestel, Chapter 1:
* `|G|` is the number of vertices and `‖G‖` the number of edges of `G`;
* `ε(G) = ‖G‖ / |G|` is the number of edges per vertex (`SimpleGraph.edgeRatio`);
* `d(G) = (1 / |G|) ∑ᵥ d(v) = 2 ε(G)` is the average degree (`SimpleGraph.avgDegree`);
* `G` is `k`-connected if `|G| > k` and `G - X` is connected for every vertex set `X` with
  `|X| < k` (`SimpleGraph.IsKConnected`).

## Dictionary between Diestel's proof and this file

| Diestel                                     | this file                                   |
| ------------------------------------------- | ------------------------------------------- |
| `γ := ε(G)`                                 | `G.edgeRatio`                               |
| the subgraph `G' = G[U]` induced on `U`     | `G.induce ↑U` with `U : Finset V`           |
| `‖G[U]‖`                                    | `#(G.edgesIn U)` (see `card_edgesIn`)       |
| `d_{G[U]}(v)`, the degree of `v` in `G[U]`  | `#(G.nbrsIn U v)`                           |
| condition `(∗)` on `G'`                     | `G.StarCond k U`                            |
| `H`: a graph of smallest order with `(∗)`   | `exists_min_starCond`                       |
| no graph with `(∗)` has order exactly `2k`  | `hne` in `mader_aux`                        |
| `δ(H) > γ`                                  | `hdeg` in `mader_aux`                       |
| `|H| ≥ γ` and `ε(H) > γ - k`                | `hγU` and the first bullet of `mader_aux`   |
| a proper separation `{U₁, U₂}` of `H`       | `exists_component_of_not_connected`         |
| `|H₁|, |H₂| ≥ 2k` and `‖H‖ ≤ ‖H₁‖ + ‖H₂‖`  | `hA2k`, `hB2k`, `hsplit` in `mader_aux`     |

The combinatorial heart of the argument is `mader_aux`, which works entirely with finite sets of
vertices of `G` and produces the vertex set `U` of `H`. The final theorem `mader` repackages its
conclusion in terms of the induced subgraph `G.induce ↑U`, `IsKConnected` and `edgeRatio`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Definitions -/

/-- The average degree `d(G) = (1 / |G|) ∑ᵥ d(v)` of `G` (Diestel, Section 1.2). -/
noncomputable def avgDegree : ℚ := (∑ v, (G.degree v : ℚ)) / Fintype.card V

/-- The number of edges per vertex, `ε(G) = ‖G‖ / |G|` (Diestel, Section 1.2) -/
noncomputable def edgeRatio : ℚ := ((G.edgeFinset.card : ℚ) / Fintype.card V)

/-- Diestel, Section 1.4: a graph `H` is `k`-connected if `|H| > k` and `H - X` is connected for
every set `X` of fewer than `k` vertices. Here `H - X` is the induced subgraph `H.induce Xᶜ`. -/
def IsKConnected {W : Type*} [Fintype W] (H : SimpleGraph W) (k : ℕ) : Prop :=
  k < Fintype.card W ∧ ∀ X : Set W, X.ncard < k → (H.induce Xᶜ).Connected

/-- The edges of `G` with both ends in `U`; these are exactly the edges of `G[U]`. -/
def edgesIn (U : Finset V) : Finset (Sym2 V) := {e ∈ G.edgeFinset | e.toFinset ⊆ U}

/-- The neighbours of `v` lying in `U`; their number is the degree of `v` in `G[U]`. -/
def nbrsIn (U : Finset V) (v : V) : Finset V := G.neighborFinset v ∩ U

/-- Condition `(∗)` of Diestel's proof, with `γ = ε(G)`: `|U| ≥ 2k` and `‖G[U]‖ > γ (|U| - k)`. -/
def StarCond (k : ℕ) (U : Finset V) : Prop :=
  2 * k ≤ #U ∧ G.edgeRatio * (#U - k) < #(G.edgesIn U)

/-! ### Basic facts about `d(G)`, `ε(G)`, `‖G[U]‖` and `d_{G[U]}(v)` -/

/- `d(G) = 2 ε(G)`, by the handshake lemma (Diestel, (1.2.2)). -/
theorem avgDegree_eq_two_mul_edgeRatio : G.avgDegree = 2 * G.edgeRatio := by
  unfold avgDegree edgeRatio
  rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
  push_cast
  ring

theorem mk_mem_edgesIn {U : Finset V} {x y : V} :
    s(x, y) ∈ G.edgesIn U ↔ G.Adj x y ∧ x ∈ U ∧ y ∈ U := by
  simp [edgesIn, Sym2.toFinset_mk_eq, insert_subset_iff]

theorem edgesIn_univ : G.edgesIn univ = G.edgeFinset := by
  simp [edgesIn]

/-- `#(G.edgesIn U)` really is the number of edges of the induced subgraph `G[U]`. -/
theorem card_edgesIn (U : Finset V) : #(G.edgesIn U) = #(G.induce ↑U).edgeFinset :=
  G.card_filter_edgeFinset_toFinset_subset U

/-- `‖G[U]‖ ≤ (|U| choose 2) ≤ |U|² / 2`. -/
theorem card_edgesIn_le (U : Finset V) : (#(G.edgesIn U) : ℚ) ≤ (#U : ℚ) ^ 2 / 2 := by
  have h1 : #(G.edgesIn U) ≤ (#U).choose 2 := by
    rw [card_edgesIn]
    simpa using (G.induce ↑U).card_edgeFinset_le_card_choose_two
  have h2 := Nat.choose_le_pow_div (α := ℚ) 2 (#U)
  norm_num [Nat.factorial] at h2
  calc (#(G.edgesIn U) : ℚ) ≤ (#U).choose 2 := by exact_mod_cast h1
    _ ≤ (#U : ℚ) ^ 2 / 2 := by linarith
/-==================================================================-/
/-- A vertex is not its own neighbour, so `d_{G[U]}(v) ≤ |U| - 1`. -/
theorem nbrsIn_subset_erase (U : Finset V) (v : V) : G.nbrsIn U v ⊆ U.erase v := by
  intro w hw
  rw [nbrsIn, mem_inter, mem_neighborFinset] at hw
  exact mem_erase.2 ⟨(G.ne_of_adj hw.1).symm, hw.2⟩

/-- Deleting a vertex `v` from `G[U]` deletes exactly `d_{G[U]}(v)` edges:
`‖G[U - v]‖ + d_{G[U]}(v) = ‖G[U]‖`. -/
theorem card_edgesIn_erase {U : Finset V} {v : V} (hv : v ∈ U) :
    #(G.edgesIn (U.erase v)) + #(G.nbrsIn U v) = #(G.edgesIn U) := by
  -- the edges of `G[U]` are those avoiding `v` together with those through `v`
  have hsplit :
      G.edgesIn U = G.edgesIn (U.erase v) ∪ (G.nbrsIn U v).image (fun w ↦ s(v, w)) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [mem_union, mk_mem_edgesIn, mem_image, nbrsIn, mem_inter, mem_neighborFinset,
        mem_erase, Sym2.eq_iff]
      constructor
      · rintro ⟨hadj, hx, hy⟩
        by_cases hxv : x = v
        · subst hxv
          exact Or.inr ⟨y, ⟨hadj, hy⟩, Or.inl ⟨rfl, rfl⟩⟩
        by_cases hyv : y = v
        · subst hyv
          exact Or.inr ⟨x, ⟨hadj.symm, hx⟩, Or.inr ⟨rfl, rfl⟩⟩
        · exact Or.inl ⟨hadj, ⟨hxv, hx⟩, ⟨hyv, hy⟩⟩
      · rintro (⟨hadj, ⟨-, hx⟩, ⟨-, hy⟩⟩ | ⟨w, ⟨hadj, hw⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
        · exact ⟨hadj, hx, hy⟩
        · exact ⟨hadj, hv, hw⟩
        · exact ⟨hadj.symm, hw, hv⟩
  -- the two parts are disjoint ...
  have hdisj : Disjoint (G.edgesIn (U.erase v)) ((G.nbrsIn U v).image (fun w ↦ s(v, w))) := by
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨w, -, rfl⟩ := mem_image.1 he'
    rw [mk_mem_edgesIn] at he
    exact (mem_erase.1 he.2.1).1 rfl
  -- ... and `w ↦ s(v, w)` is injective, so the second part has `d_{G[U]}(v)` elements
  have hinj : Function.Injective (fun w : V ↦ s(v, w)) := fun a b h ↦ Sym2.congr_right.1 h
  have hcard := card_union_add_card_inter (G.edgesIn (U.erase v))
    ((G.nbrsIn U v).image (fun w ↦ s(v, w)))
  rw [disjoint_iff_inter_eq_empty.1 hdisj, card_empty, add_zero, card_image_of_injective _ hinj]
    at hcard
  rw [hsplit, hcard]

/-- If all neighbours (inside `U`) of the vertices of `C` lie in `C ∪ X`, then every edge of
`G[U]` is an edge of `G[C ∪ X]` or of `G[U \ C]`. -/
theorem edgesIn_subset_union {U X C : Finset V}
    (hclosed : ∀ a ∈ C, ∀ b ∈ U, G.Adj a b → b ∈ C ∨ b ∈ X) :
    G.edgesIn U ⊆ G.edgesIn (C ∪ X) ∪ G.edgesIn (U \ C) := by
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    rw [mk_mem_edgesIn] at he
    obtain ⟨hadj, hx, hy⟩ := he
    rw [mem_union, mk_mem_edgesIn, mk_mem_edgesIn]
    by_cases hxC : x ∈ C
    · -- `x ∈ C`, so `y ∈ C ∪ X` as well
      refine Or.inl ⟨hadj, mem_union_left _ hxC, ?_⟩
      rcases hclosed x hxC y hy hadj with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ h
    by_cases hyC : y ∈ C
    · -- `y ∈ C`, so `x ∈ C ∪ X` as well
      refine Or.inl ⟨hadj, ?_, mem_union_left _ hyC⟩
      rcases hclosed y hyC x hx hadj.symm with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ h
    · -- neither end is in `C`
      exact Or.inr ⟨hadj, mem_sdiff.2 ⟨hx, hxC⟩, mem_sdiff.2 ⟨hy, hyC⟩⟩

/-! ### Separations -/

/-- If `G[U - X]` is not connected, then the vertex set `C` of a component of `G[U - X]`
satisfies: `C` and `(U - X) - C` are both nonempty, and all neighbours of `C` inside `U` lie in
`C ∪ X`. In Diestel's words, `{C ∪ X, U - C}` is a proper separation of `G[U]` of order `|X|`. -/
theorem exists_component_of_not_connected {U X : Finset V} (hne : (U \ X).Nonempty)
    (hnc : ¬ (G.induce ↑(U \ X)).Connected) :
    ∃ C : Finset V, C ⊆ U \ X ∧ C.Nonempty ∧ ((U \ X) \ C).Nonempty ∧
      ∀ a ∈ C, ∀ b ∈ U, G.Adj a b → b ∈ C ∨ b ∈ X := by
  classical
  have : Nonempty (↑(U \ X) : Set V) := Set.nonempty_coe_sort.2 (coe_nonempty.2 hne)
  -- `G[U - X]` has a vertex, so it is not preconnected: pick `u`, `v` with no walk from `u` to `v`
  have hpre : ¬ (G.induce ↑(U \ X)).Preconnected := fun h ↦ hnc ⟨h⟩
  unfold Preconnected at hpre
  push Not at hpre
  obtain ⟨u, v, huv⟩ := hpre
  -- `C` := the vertices of `U - X` that can be reached from `u` inside `G[U - X]`
  refine ⟨(U \ X).filter (fun w ↦ ∃ (hw : w ∈ U \ X), (G.induce ↑(U \ X)).Reachable u ⟨w, hw⟩),
    filter_subset _ _, ?_, ?_, ?_⟩
  · -- `u ∈ C`
    exact ⟨u.1, mem_filter.2 ⟨u.2, u.2, Reachable.refl u⟩⟩
  · -- `v ∉ C`
    refine ⟨v.1, mem_sdiff.2 ⟨v.2, fun hv ↦ ?_⟩⟩
    obtain ⟨-, _, hr⟩ := mem_filter.1 hv
    exact huv hr
  · -- a neighbour `b ∈ U` of some `a ∈ C` lies in `X`, or else is reachable from `u` as well
    intro a ha b hb hadj
    obtain ⟨-, ha', hr⟩ := mem_filter.1 ha
    by_cases hbX : b ∈ X
    · exact Or.inr hbX
    · have hb' : b ∈ U \ X := mem_sdiff.2 ⟨hb, hbX⟩
      refine Or.inl (mem_filter.2 ⟨hb', hb', hr.trans (Adj.reachable ?_)⟩)
      exact induce_adj.2 hadj

/-! ### The graphs satisfying `(∗)` -/

/-- `G` itself satisfies `(∗)`: `|G| ≥ 2k` and `‖G‖ > γ (|G| - k)`. This needs `k ≠ 0` and
`γ = ε(G) ≥ 2k`. -/
theorem starCond_univ (k : ℕ) (hk : k ≠ 0) (hγ : (2 * k : ℚ) ≤ G.edgeRatio) :
    G.StarCond k univ := by
  have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  -- `G` has a vertex, for otherwise `ε(G) = 0 < 2k`
  have hn : 0 < Fintype.card V := by
    by_contra h
    have h0 : G.edgeRatio = 0 := by simp [edgeRatio, Nat.eq_zero_of_not_pos h]
    linarith
  have hnQ : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
  -- `γ |G| = ‖G‖`
  have hE : G.edgeRatio * Fintype.card V = #G.edgeFinset := by
    unfold edgeRatio
    exact div_mul_cancel₀ _ hnQ.ne'
  have hle := G.card_edgesIn_le univ
  rw [edgesIn_univ, card_univ] at hle
  have hγn : (2 * k : ℚ) * Fintype.card V ≤ G.edgeRatio * Fintype.card V :=
    mul_le_mul_of_nonneg_right hγ hnQ.le
  unfold StarCond
  constructor
  · -- `2k |G| ≤ γ |G| = ‖G‖ ≤ |G|² / 2`, hence `4k ≤ |G|`
    have h1 : (4 * k : ℚ) * Fintype.card V ≤ Fintype.card V * Fintype.card V := by nlinarith
    have h2 : (4 * k : ℚ) ≤ Fintype.card V := le_of_mul_le_mul_right h1 hnQ
    have h3 : (2 * k : ℚ) ≤ Fintype.card V := by linarith
    rw [card_univ]
    exact_mod_cast h3
  · -- `γ (|G| - k) = ‖G‖ - γ k < ‖G‖`
    have hpos : 0 < G.edgeRatio * k := mul_pos (by linarith) (by linarith)
    rw [edgesIn_univ, card_univ]
    nlinarith

/-- Among the vertex sets satisfying `(∗)`, choose one of smallest order: Diestel's `H`. -/
theorem exists_min_starCond (k : ℕ) (hk : k ≠ 0) (hγ : (2 * k : ℚ) ≤ G.edgeRatio) :
    ∃ U : Finset V, G.StarCond k U ∧ ∀ U' : Finset V, G.StarCond k U' → #U ≤ #U' := by
  classical
  obtain ⟨U, hU, hmin⟩ := exists_min_image (univ.filter (G.StarCond k)) Finset.card
    ⟨univ, mem_filter.2 ⟨mem_univ _, G.starCond_univ k hk hγ⟩⟩
  exact ⟨U, (mem_filter.1 hU).2, fun U' hU' ↦ hmin U' (mem_filter.2 ⟨mem_univ _, hU'⟩)⟩

/-! ### The main argument -/

/-- The combinatorial core of Mader's theorem. If `k ≠ 0` and `ε(G) ≥ 2k`, there is a vertex
set `U` such that `H = G[U]` has `|H| > k + 1`, `ε(H) > ε(G) - k`, and `H - X` is connected for
every `X ⊆ U` with `|X| ≤ k`. -/
theorem mader_aux (k : ℕ) (hk : k ≠ 0) (hγ : (2 * k : ℚ) ≤ G.edgeRatio) :
    ∃ U : Finset V, k + 1 < #U ∧ G.edgeRatio - k < #(G.edgesIn U) / #U ∧
      ∀ X ⊆ U, #X ≤ k → (G.induce ↑(U \ X)).Connected := by
  classical
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
  have hk1Q : (1 : ℚ) ≤ k := by exact_mod_cast hk1
  have hγ0 : 0 < G.edgeRatio := by linarith
  -- `H = G[U]`, where `U` is of smallest order among the vertex sets satisfying `(∗)`
  obtain ⟨U, ⟨hU1, hU2⟩, hmin⟩ := G.exists_min_starCond k hk hγ
  -- Step 1: `|U| ≠ 2k`, since otherwise `‖G[U]‖ > γ k ≥ 2k² ≥ (2k choose 2)`
  have hne : #U ≠ 2 * k := by
    intro h
    have h1 := G.card_edgesIn_le U
    rw [h] at h1 hU2
    push_cast at h1 hU2
    have h2 : (2 * k : ℚ) * k ≤ G.edgeRatio * k := mul_le_mul_of_nonneg_right hγ (by linarith)
    nlinarith
  have hcard : 2 * k < #U := lt_of_le_of_ne hU1 (Ne.symm hne)
  have hUpos : 0 < #U := by omega
  have hUposQ : (0 : ℚ) < #U := by exact_mod_cast hUpos
  -- Step 2: `δ(H) > γ`. Otherwise delete a vertex `v` of degree `≤ γ`: the smaller set
  -- `U - v` still satisfies `(∗)`, contradicting the minimality of `U`.
  have hdeg : ∀ v ∈ U, G.edgeRatio < #(G.nbrsIn U v) := by
    intro v hv
    by_contra hle
    push Not at hle
    have h1 : (#(G.edgesIn (U.erase v)) : ℚ) + #(G.nbrsIn U v) = #(G.edgesIn U) := by
      exact_mod_cast G.card_edgesIn_erase hv
    have h2 : #(U.erase v) + 1 = #U := card_erase_add_one hv
    have h2Q : (#(U.erase v) : ℚ) + 1 = #U := by exact_mod_cast h2
    have hstar : G.StarCond k (U.erase v) := by
      refine ⟨by omega, ?_⟩
      have h3 : G.edgeRatio * ((#(U.erase v) : ℚ) - k) =
          G.edgeRatio * ((#U : ℚ) - k) - G.edgeRatio := by
        rw [← h2Q]
        ring
      linarith
    have := hmin _ hstar
    omega
  -- Step 3: `γ + 1 ≤ |U|` (in particular `γ ≤ |U|`), since `γ < d_H(v) ≤ |U| - 1` for `v ∈ U`
  obtain ⟨v₀, hv₀⟩ : U.Nonempty := card_pos.1 hUpos
  have hγU : G.edgeRatio + 1 ≤ #U := by
    have h1 := hdeg v₀ hv₀
    have h2 : (#(G.nbrsIn U v₀) : ℚ) ≤ #(U.erase v₀) := by
      exact_mod_cast card_le_card (G.nbrsIn_subset_erase U v₀)
    have h3 : (#(U.erase v₀) : ℚ) + 1 = #U := by exact_mod_cast card_erase_add_one hv₀
    linarith
  refine ⟨U, by omega, ?_, ?_⟩
  · -- `ε(H) > γ - k`: divide `‖H‖ > γ (|H| - k)` by `|H|` and use `γ ≤ |H|`
    rw [lt_div_iff₀ hUposQ]
    have h1 : (k : ℚ) * G.edgeRatio ≤ k * #U :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  · -- Step 4: `H` is `(k + 1)`-connected. Suppose `H - X` is disconnected for some `X ⊆ U`
    -- with `|X| ≤ k`.
    intro X hXU hXk
    by_contra hnc
    -- `H - X` is nonempty, so it has a component `C`; this gives the separation
    -- `{H₁, H₂} = {G[C ∪ X], G[U \ C]}` of `H` of order `|X| ≤ k`
    have hUX : (U \ X).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset hXU]
      omega
    obtain ⟨C, hC, ⟨a, ha⟩, ⟨b, hb⟩, hclosed⟩ := G.exists_component_of_not_connected hUX hnc
    have hCU : C ⊆ U := hC.trans sdiff_subset
    have hCX : Disjoint C X := by
      rw [Finset.disjoint_left]
      intro x hx hxX
      exact (mem_sdiff.1 (hC hx)).2 hxX
    have hbU : b ∈ U := (mem_sdiff.1 (mem_sdiff.1 hb).1).1
    have hbX : b ∉ X := (mem_sdiff.1 (mem_sdiff.1 hb).1).2
    have hbC : b ∉ C := (mem_sdiff.1 hb).2
    -- both sides of the separation are proper subsets of `U`
    have hAU : C ∪ X ⊆ U := union_subset hCU hXU
    have hAlt : #(C ∪ X) < #U := by
      refine card_lt_card ((ssubset_iff_of_subset hAU).2 ⟨b, hbU, ?_⟩)
      rw [mem_union]
      exact fun h ↦ h.elim hbC hbX
    have hBlt : #(U \ C) < #U :=
      card_lt_card ((ssubset_iff_of_subset sdiff_subset).2
        ⟨a, hCU ha, fun h ↦ (mem_sdiff.1 h).2 ha⟩)
    -- `|H₁| + |H₂| = |H| + |X|`, as `H₁ ∩ H₂ = X`
    have hAB : #(C ∪ X) + #(U \ C) = #U + #X := by
      have h1 : #(C ∪ X) + #(C ∩ X) = #C + #X := card_union_add_card_inter C X
      rw [disjoint_iff_inter_eq_empty.1 hCX, card_empty, add_zero] at h1
      have h2 : #(U \ C) + #C = #U := card_sdiff_add_card_eq_card hCU
      omega
    -- a vertex `a ∈ C` has all its `d_H(a) > γ` neighbours in `H₁`, so `|H₁| > γ + 1 ≥ 2k`
    have hA2k : 2 * k ≤ #(C ∪ X) := by
      have hsub : G.nbrsIn U a ⊆ (C ∪ X).erase a := by
        intro w hw
        rw [nbrsIn, mem_inter, mem_neighborFinset] at hw
        refine mem_erase.2 ⟨(G.ne_of_adj hw.1).symm, ?_⟩
        rcases hclosed a ha w hw.2 hw.1 with h | h
        · exact mem_union_left _ h
        · exact mem_union_right _ h
      have h1 := hdeg a (hCU ha)
      have h2 : (#(G.nbrsIn U a) : ℚ) ≤ #((C ∪ X).erase a) := by
        exact_mod_cast card_le_card hsub
      have h3 : (#((C ∪ X).erase a) : ℚ) + 1 = #(C ∪ X) := by
        exact_mod_cast card_erase_add_one (mem_union_left X ha)
      have : (2 * k : ℚ) ≤ #(C ∪ X) := by linarith
      exact_mod_cast this
    -- likewise a vertex `b ∈ (U - X) - C` has all its neighbours in `H₂`, so `|H₂| ≥ 2k`
    have hB2k : 2 * k ≤ #(U \ C) := by
      have hsub : G.nbrsIn U b ⊆ (U \ C).erase b := by
        intro w hw
        rw [nbrsIn, mem_inter, mem_neighborFinset] at hw
        refine mem_erase.2 ⟨(G.ne_of_adj hw.1).symm, mem_sdiff.2 ⟨hw.2, fun hwC ↦ ?_⟩⟩
        rcases hclosed w hwC b hbU hw.1.symm with h | h
        · exact hbC h
        · exact hbX h
      have h1 := hdeg b hbU
      have h2 : (#(G.nbrsIn U b) : ℚ) ≤ #((U \ C).erase b) := by
        exact_mod_cast card_le_card hsub
      have h3 : (#((U \ C).erase b) : ℚ) + 1 = #(U \ C) := by
        exact_mod_cast card_erase_add_one (mem_sdiff.2 ⟨hbU, hbC⟩)
      have : (2 * k : ℚ) ≤ #(U \ C) := by linarith
      exact_mod_cast this
    -- by the minimality of `U`, neither `H₁` nor `H₂` satisfies `(∗)`
    have hAstar : (#(G.edgesIn (C ∪ X)) : ℚ) ≤ G.edgeRatio * (#(C ∪ X) - k) := by
      by_contra h
      push Not at h
      have := hmin _ ⟨hA2k, h⟩
      omega
    have hBstar : (#(G.edgesIn (U \ C)) : ℚ) ≤ G.edgeRatio * (#(U \ C) - k) := by
      by_contra h
      push Not at h
      have := hmin _ ⟨hB2k, h⟩
      omega
    -- but then `‖H‖ ≤ ‖H₁‖ + ‖H₂‖ ≤ γ (|H₁| + |H₂| - 2k) = γ (|H| + |X| - 2k) ≤ γ (|H| - k)`,
    -- contradicting `(∗)` for `U`
    have hsplit : (#(G.edgesIn U) : ℚ) ≤ #(G.edgesIn (C ∪ X)) + #(G.edgesIn (U \ C)) := by
      exact_mod_cast (card_le_card (G.edgesIn_subset_union hclosed)).trans
        (card_union_le _ _)
    have hABQ : G.edgeRatio * ((#(C ∪ X) : ℚ) + #(U \ C)) = G.edgeRatio * ((#U : ℚ) + #X) := by
      congr 1
      exact_mod_cast hAB
    have hXkQ : (#X : ℚ) ≤ k := by exact_mod_cast hXk
    have hXγ : 0 ≤ G.edgeRatio * (k - #X) := mul_nonneg hγ0.le (by linarith)
    linarith

/-! ### Mader's theorem -/

/-- An induced subgraph of an induced subgraph is an induced subgraph:
`(G[s])[t] ≅ G[t]`, where `t ⊆ s` is viewed as a set of vertices of `G`. -/
noncomputable def induceInduceIso (s : Set V) (t : Set s) :
    (G.induce s).induce t ≃g G.induce (Subtype.val '' t) where
  toEquiv := Equiv.Set.image Subtype.val t Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- **Mader's theorem** (Diestel, Theorem 1.4.3). Let `0 ≠ k ∈ ℕ`. Every graph `G` with
`d(G) ≥ 4k` has a `(k + 1)`-connected subgraph `H` such that `ε(H) > ε(G) - k`.
The subgraph is the induced subgraph `H = G[U] = G.induce ↑U` on a suitable vertex set `U`. -/
theorem mader (k : ℕ) (hk : k ≠ 0) (hG : (4 * k : ℚ) ≤ G.avgDegree) :
    ∃ U : Finset V, (G.induce ↑U).IsKConnected (k + 1) ∧
      G.edgeRatio - k < (G.induce ↑U).edgeRatio := by
  classical
  -- `d(G) ≥ 4k` says exactly `γ = ε(G) ≥ 2k`
  have hγ : (2 * k : ℚ) ≤ G.edgeRatio := by
    rw [avgDegree_eq_two_mul_edgeRatio] at hG
    linarith
  obtain ⟨U, hcard, hε, hconn⟩ := G.mader_aux k hk hγ
  refine ⟨U, ⟨by simpa using hcard, fun X hX ↦ ?_⟩, ?_⟩
  · -- `(k + 1)`-connectivity: a set `X` of at most `k` vertices of `G[U]` is a set `X'` of at
    -- most `k` vertices of `G` inside `U`, and `G[U] - X ≅ G[U \ X']`
    set X' : Finset V := (Subtype.val '' X).toFinset with hX'
    have hX'U : X' ⊆ U := by
      intro x hx
      rw [hX', Set.mem_toFinset] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have hX'k : #X' ≤ k := by
      rw [hX', ← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ Subtype.val_injective]
      omega
    have hset : (Subtype.val '' Xᶜ : Set V) = ↑(U \ X') := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : y ∉ X := hy
        refine mem_coe.2 (mem_sdiff.2 ⟨y.2, fun h ↦ hy' ?_⟩)
        rw [hX', Set.mem_toFinset] at h
        obtain ⟨z, hz, hzy⟩ := h
        rw [← Subtype.val_injective hzy]
        exact hz
      · intro hx
        obtain ⟨hxU, hxX'⟩ := mem_sdiff.1 (mem_coe.1 hx)
        refine ⟨⟨x, hxU⟩, fun h ↦ hxX' ?_, rfl⟩
        rw [hX', Set.mem_toFinset]
        exact ⟨⟨x, hxU⟩, h, rfl⟩
    rw [(G.induceInduceIso ↑U Xᶜ).connected_iff, hset]
    exact hconn X' hX'U hX'k
  · -- `ε(G[U]) = ‖G[U]‖ / |U|`
    have h : (G.induce ↑U).edgeRatio = #(G.edgesIn U) / #U := by
      simp [edgeRatio, card_edgesIn]
    rw [h]
    exact hε

end SimpleGraph
