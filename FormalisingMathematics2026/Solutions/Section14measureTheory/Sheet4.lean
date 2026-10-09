/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jason Kexing Ying, Kevin Buzzard
-/
-- Modified by Utku Okur, 2026
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option linter.all false  -- comment out this line to see Mathlib's style warnings

/-

# Measures

Recall that Lean calls a space equipped with
a sigma algebra a "MeasurableSpace". We will go with this language
and call sets in the sigma algebra "measurable sets".

Given a measurable space, a *measure* on the measurable space is a function from
the measurable sets to `[0,∞]` which is countably additive (i.e.,
the measure of a countable disjoint union of measurable sets is the sum of the measures).
This is not the *definition* of a measure in Lean, but it is mathematically equivalent to the
definition.

For what it's worth, the actual definition of a measure in Lean is this: an `OuterMeasure`
on a type `α` is this:

```lean
structure OuterMeasure (α : Type*) where
  measureOf : Set α → ℝ≥0∞
  empty : measureOf ∅ = 0
  mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  iUnion_nat : ∀ s : ℕ → Set α, measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)
```

So it attaches an element of `[0,∞]` to *every* subset of α, satisfying some natural axioms;
note in particular it is countably *sub*additive, meaning that the measure of a countable
union of open sets, even if they're pairwise disjoint, is only assumed to be at most the sum of the measures.

And if `α` has a measurable space structure then a measure on `α` is an outer measure satisfying
some axioms, which boil down to "the restriction of the outer measure is a measure on the measurable
sets, and the extension of this measure to an outer measure agrees with the outer measure we started with".
The advantage of doing it this way is that given a measure, we can evaluate it on *any* subset
(getting the outer measure of the subset) rather than having to supply a proof that the subset
is measurable. This coincides with Lean's "make functions total" philosophy (the same reason that 1/0=0).

-/

section Section13Sheet3

open Filter

open scoped NNReal ENNReal MeasureTheory BigOperators Topology

-- note to self: removed `probability_theory`
namespace MeasureTheory

-- Let Ω be a set equipped with a sigma algebra.
variable {Ω : Type} [MeasurableSpace Ω]

-- Now let's add a measure `μ` on `Ω`
variable {μ : Measure Ω}

/-
Try proving the following:
-/
example (S T : Set Ω) (hS : μ S ≠ ∞) (hT : MeasurableSet T) :
    μ (S ∪ T) = μ S + μ T - μ (S ∩ T) := by
  rw [← measure_union_add_inter S hT]
  rw [ENNReal.add_sub_cancel_right]
  exact measure_ne_top_of_subset Set.inter_subset_left hS

/-!
## Measurable functions

So far we've worked in the space `Ω` though with all mathematical objects, we
want to map between them. In measure theory, the correct notion of maps is
measurable functions. If you have seen continuity in topology, they are quite
similar, namely, a function `f` between two measurable spaces is said to be
measurable if the preimages of all measurable sets along `f` is measurable.
-/


/-
*Remark*: while proving the above, you might have noticed I've added the
condition `hS` (think about what is a + ∞ - ∞). In particular, subtraction in
extended non-negative reals (`ℝ≥0∞`) might not be what you expect,
e.g. 1 - 2 = 0 in `ℝ≥0∞`. For this reason, the above lemma is better phrased as
`μ (S ∪ T) + μ (S ∩ T) = μ S + μ T` for which we can omit the condition `hS`.
-/
/-
If you go to the definition of measurable you will find what you expect.
However, of course, measure theory in Lean is a bit more complicated. As we
shall see, in contrast to maths, there are 3 additional notions of measurability
in mathlib. These are:
- `AEMeasurable`
- `StronglyMeasurable`
- `AEStronglyMeasurable`
The reasons for their existence is technical but TLDR: `ae_foo f` is the predicate
that `f` is almost everywhere equal to some function satisfying `foo` (see the
a.e. filter section) while `StronglyMeasurable f` is saying `f` is the limit
of a sequence of simple functions.

Alongside `measurable`, we also see them quite often in the mathlib, although
all you have to know is in most cases (range is metrizable and second-countable),
`Measurable` and `StronglyMeasurable` are equivalent.
-/
example : Measurable (id : Ω → Ω) :=
  measurable_id

example {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (f : X → Y) (g : Y → Z) (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) :=
  hg.comp hf

/-!
## Integration

One of the primary motivations of measure theory is to introduce a more
satisfactory theory of integration. If you recall the definition of the
Darboux-Riemann integral, we cannot integrate the indicator function of
`ℚ ∩ [0, 1]` despite, intuitively, the set of rationals in the unit interval
is much "smaller" (rationals is countable while the irrationals are not.
In contrast, measure theory allows us to construct the Lebesgue integral
which can deal with integrals such as this one.

Lean uses a even more general notion of integration known as Bochner integration
which allows us to integrate Banach-space valued functions. Its construction
is similar to the Lebesgue integral.

Read page 5-6 of https://arxiv.org/pdf/2102.07636.pdf
if you want to know the details.
-/


-- Suppose now `X` is another measurable space
variable {X : Type} [MeasurableSpace X]

-- and suppose it's also a Banach space (i.e. a vector space and a complete metric space)
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

-- If `f : Ω → X` is a function, then the integral of `f` is written as
-- `∫ x, f x ∂μ`. If you want to integrate over the set `s : set Ω` then write
-- `∫ x in s, f x ∂μ`.
-- Try looking in mathlib
example {f g : Ω → X} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ :=
  integral_add hf hg

example (a : X) (s : Set Ω) : ∫ _ in s, a ∂μ = (μ s).toReal • a :=
  setIntegral_const a

-- Harder
example
    {f : Ω → ℝ} (hf : Measurable f)
    (hint : Integrable f μ) (hμ : 0 < μ {ω | 0 < f ω}) :
    (0 : ℝ) < ∫ ω in {ω | 0 < f ω}, f ω ∂μ := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rwa [Set.inter_eq_self_of_subset_right]
    intro x hx
    exact ne_of_gt hx
  · exact ae_restrict_of_forall_mem (measurableSet_lt measurable_const hf) fun x hx => le_of_lt hx
  · exact hint.integrableOn

/-!
## ae filter

Now we have come to a very important section of working with measure theory
in Lean.

In measure theory we have a notion known as almost everywhere (a.e.). In
probability this is known as almost surely however we will stick with
almost everywhere in this project. Namely, a predicate `P` on `Ω` is said to
be true almost everywhere if the set for which `P` holds is co-null, i.e.
`μ {ω : Ω | P ω}ᶜ = 0`.

As examples, we say:
- given functions `f, g`, `f` equals `g` a.e. if `μ {ω : Ω | f ω ≠ g ω} = 0`;
- `f` is less equal to `g` a.e. if `μ {ω : Ω | ¬ f ω ≤ g ω} = 0` etc.

Often, showing that a property holds a.e. is the best we can do in
measure/probability theory.

In Lean, the notion of a.e. is handled by the `Measure.ae` filter.
Let's construct that filter ourselves.
-/


/-
*Remark* It's a common myth that Lebesgue integration is strictly better than
the Darboux-Riemann integral. This is true for integration on bounded intervals
though it is not true when considering improper integrals. A common example
for this is, while `∫ x in [0, ∞), sin x / x dx` is Darboux-Riemann integrable
(in fact it equals `π / 2`) it is not Lebesgue integrable as
`∫ x in [0, ∞), |sin x / x| dx = ∞`.
-/
example (X : Type) [MeasurableSpace X] (μ : Measure X) : Filter X :=
  ae μ

-- say `f` and `g` are measurable functions `Ω → X`
variable (f g : Ω → X)

-- The following is a proposition that `f` and `g` are almost everywhere equal
-- it's **not** a proof that `f` and `g` are a.e. equal but simply a statement
example : Prop :=
  ∀ᵐ ω ∂μ, f ω = g ω

-- Here's another example on how to state `f` is almost everywhere less equal
-- than `g`
-- To be able to formulate this we need a notion of inequality on `X` so we
-- will add the `LE` instance on `X`, i.e. equip `X` with a inequality
example [LE X] : Prop :=
  ∀ᵐ ω ∂μ, f ω ≤ g ω

-- Since the above two cases come up quite often, there are special notations
-- for them. See if you can guess what they mean
example : Prop :=
  f =ᵐ[μ] g

example [LE X] : Prop :=
  f ≤ᵐ[μ] g

-- In general, if `P : Ω → Prop` is a predicate on `Ω`, we write `∀ᵐ ω ∂μ, P ω`
-- for the statement that `P` holds a.e.
example (P : Ω → Prop) : Prop :=
  ∀ᵐ ω ∂μ, P ω

-- Sanity check: the above notation actually means what we think
example (P : Ω → Prop) : (∀ᵐ ω ∂μ, P ω) ↔ μ ({ω | P ω}ᶜ) = 0 := by rfl

-- Here's a more convoluted example. See if you can figure what it means
example (f : ℕ → Ω → ℝ) (s : Set Ω) :=
  ∀ᵐ ω ∂μ.restrict s, ∃ l : ℝ, Tendsto (fun n ↦ f n ω) atTop (𝓝 l)

-- Now to do some exercises: you will need to dig into the source code to see
-- what the definitions are and search for helpful lemmas
-- *Hint*: try out the `measurability` tactic. It should be able to solve simple
-- goals of the form `MeasurableSet s` and `Measurable f`
example (s : Set Ω) (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ ω ∈ s, f ω = g ω) : f =ᵐ[μ.restrict s] g := by
  rw [Filter.EventuallyEq, ae_restrict_iff (measurableSet_eq_fun hf hg)]
  exact Eventually.of_forall hfg

example (f g h : Ω → ℝ)
    (h₁ : f ≤ᵐ[μ] g) (h₂ : f ≤ᵐ[μ] h) : 2 * f ≤ᵐ[μ] g + h := by
  filter_upwards [h₁, h₂] with ω hω₁ hω₂
  simp only [Pi.mul_apply, Pi.add_apply, Pi.ofNat_apply]
  linarith

example (f g : Ω → ℝ) (h : f =ᵐ[μ] g) (hg : ∀ᵐ ω ∂μ, 2 * g ω + 1 ≤ 0) :
    ∀ᵐ ω ∂μ, f ω ≤ -1 / 2 := by
  filter_upwards [h, hg] with ω hω hωg
  linarith

example (f g : ℕ → Ω → ℝ) (a b : ℝ)
    (hf : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 a))
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 b)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω + g n ω) atTop (𝓝 (a + b)) := by
  filter_upwards [hf, hg] with ω hωf hωg
  exact hωf.add hωg

/-
I hope that you found the above examples slightly annoying, especially the
third example: why can't we just `rw h`?! Of course, while we often do do so on
paper, rigorously, such a rewrite require some logic. Luckily, what we normally
do on paper is most often ok and we would like to do so in Lean as well. While
we can't directly rewrite almost everywhere equalities, we have the next best
thing: the `filter_upwards` tactic. See the tactic documentation here:
https://leanprover-community.github.io/mathlib_docs/tactics.html#filter_upwards

The `filter_upwards` tactic is much more powerful than simply rewriting a.e.
equalities and is helpful in many situations, e.g. the above second, third
and fourth examples are all easily solvable with this tactic. Let us see how
it works in action.
-/
-- Hover over each line and see how the goal changes
example (f₁ f₂ g₁ g₂ : Ω → ℝ)
    (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ := by
  filter_upwards [h₁, h₂]
  intro ω hω₁ hω₂
  exact add_le_add hω₁ hω₂

-- Here's an even shorter proof using additional parameters of `filter_upwards`
example (f₁ f₂ g₁ g₂ : Ω → ℝ) (h₁ : f₁ ≤ᵐ[μ] g₁) (h₂ : f₂ ≤ᵐ[μ] g₂) : f₁ + f₂ ≤ᵐ[μ] g₁ + g₂ := by
  filter_upwards [h₁, h₂] with ω hω₁ hω₂ using add_le_add hω₁ hω₂

/-
Intuitively, what `filter_upwards` is doing is simply exploiting the fact that
the intersection of two full measure sets (i.e. complements are null) is also
a set of full measure. Thus, it suffices to work in their intersection instead.

Now, try the above examples again using the `filter_upwards` tactic.
-/
end MeasureTheory

end Section13Sheet3
