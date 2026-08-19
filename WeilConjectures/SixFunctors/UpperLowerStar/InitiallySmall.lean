/-
Copyright (c) 2026 Orchestra Agent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Orchestra Agent
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.FinallySmall
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# The base-change Kan extensions, reduced to one smallness statement about schemes

`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension` asserts, with a
`sorry`, that left Kan extensions along the opposite of base change
`MorphismProperty.Over.pullback P ⊤ g` exist for an *arbitrary* `g : Z ⟶ Y`, and that they are
left exact. Its docstring justifies both by saying that the small sites are essentially small.
They are not: for `P = @Etale` the family `∐_{i : I} Y` gives pairwise non-isomorphic objects
of `Y.Etale` for pairwise non-equinumerous `I`, and the same family lives in the comma
categories indexing the pointwise left Kan extensions.

This file replaces that missing hypothesis by the correct one. Mathlib's
`CategoryTheory.InitiallySmall` is exactly the weakening of `EssentiallySmall` that colimit
theory needs, and `CategoryTheory.initiallySmall_of_small_weakly_initial_set` reduces it, for
a *cofiltered* category, to the existence of a `u`-small weakly initial set of objects. Base
change is representably flat (`AlgebraicGeometry.Etale.representablyFlat_overPullback`), so
the comma categories are cofiltered and that reduction applies.

The outcome is that both sorried Kan-extension statements for base change follow from the
single input

> for every `V : P.Over ⊤ Z` the category `StructuredArrow V (Over.pullback P ⊤ g)` — the
> category of `P`-neighbourhoods of the `Y`-scheme `V.left` — has a `u`-small weakly initial
> family of objects,

which is a statement about schemes with no category theory left in it. Nothing here proves
that input; it is the remaining mathematics.

## Main results

- `AlgebraicGeometry.initiallySmall_structuredArrow_overPullback`: the reduction to a
  `u`-small weakly initial family.
- `AlgebraicGeometry.hasColimitsOfShape_costructuredArrow_op_overPullback` and
  `AlgebraicGeometry.hasExactColimitsOfShape_costructuredArrow_op_overPullback`: the colimits
  computing the pointwise left Kan extension, and their exactness.
- `AlgebraicGeometry.hasPointwiseLeftKanExtension_op_overPullback_of_initiallySmall` and
  `AlgebraicGeometry.hasLeftKanExtension_op_overPullback_of_initiallySmall`: the conclusion of
  `CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback`, conditional on
  that input and free of `sorryAx`.
- `AlgebraicGeometry.Etale.initiallySmall_structuredArrow_overPullback`: for an *étale* `g` the
  input holds, because the comma categories then have initial objects. This is the check that
  the reduction is not vacuous — it reproves the already proved
  `AlgebraicGeometry.Etale.hasPointwiseLeftKanExtension_op_overPullback`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite MorphismProperty AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

variable (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- **The reduction.** For an arbitrary `g : Z ⟶ Y`, the category of `P`-neighbourhoods of a
`P`-scheme `V` over `Z`, viewed over `Y`, is `u`-initially small as soon as it has a `u`-small
weakly initial family of objects.

The hypothesis `RepresentablyFlat (MorphismProperty.Over.pullback P ⊤ g)` — which holds for
`P = @Etale` by `AlgebraicGeometry.Etale.representablyFlat_overPullback` — is what makes the
category cofiltered, and cofilteredness is what makes a weakly initial family enough.

This is the only step of the argument that mentions schemes; everything downstream is formal. -/
theorem initiallySmall_structuredArrow_overPullback
    [RepresentablyFlat (MorphismProperty.Over.pullback P ⊤ g)] (V : P.Over ⊤ Z)
    (s : Set (StructuredArrow V (MorphismProperty.Over.pullback P ⊤ g))) [Small.{u} s]
    (hs : ∀ i, ∃ j ∈ s, Nonempty (j ⟶ i)) :
    InitiallySmall.{u} (StructuredArrow V (MorphismProperty.Over.pullback P ⊤ g)) :=
  initiallySmall_of_small_weakly_initial_set s hs

variable (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]

/-- The colimits computing the pointwise left Kan extension along the opposite of base change
exist as soon as the comma categories are `u`-initially small. -/
theorem hasColimitsOfShape_costructuredArrow_op_overPullback (K : (P.Over ⊤ Z)ᵒᵖ)
    [InitiallySmall.{u} (StructuredArrow K.unop (MorphismProperty.Over.pullback P ⊤ g))] :
    HasColimitsOfShape
      (CostructuredArrow (MorphismProperty.Over.pullback P ⊤ g).op K) A :=
  Limits.hasColimitsOfShape_costructuredArrow_op_of_initiallySmall _ K A

/-- Those colimits are moreover exact, since base change is representably flat and `A` is
`AB5`. This is the input to left exactness of the left Kan extension. -/
theorem hasExactColimitsOfShape_costructuredArrow_op_overPullback
    [RepresentablyFlat (MorphismProperty.Over.pullback P ⊤ g)] (K : (P.Over ⊤ Z)ᵒᵖ)
    [InitiallySmall.{u} (StructuredArrow K.unop (MorphismProperty.Over.pullback P ⊤ g))] :
    haveI : HasColimitsOfShape
        (CostructuredArrow (MorphismProperty.Over.pullback P ⊤ g).op K) A :=
      hasColimitsOfShape_costructuredArrow_op_overPullback P g A K
    HasExactColimitsOfShape
      (CostructuredArrow (MorphismProperty.Over.pullback P ⊤ g).op K) A :=
  Limits.hasExactColimitsOfShape_costructuredArrow_op_of_initiallySmall _ K A

/-- All pointwise left Kan extensions along the opposite of base change exist, as soon as the
comma categories are `u`-initially small. -/
theorem hasPointwiseLeftKanExtension_op_overPullback_of_initiallySmall
    [∀ V : P.Over ⊤ Z,
      InitiallySmall.{u} (StructuredArrow V (MorphismProperty.Over.pullback P ⊤ g))]
    (F : (P.Over ⊤ Y)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback P ⊤ g).op.HasPointwiseLeftKanExtension F := fun K =>
  haveI : HasColimitsOfShape
      (CostructuredArrow (MorphismProperty.Over.pullback P ⊤ g).op K) A :=
    hasColimitsOfShape_costructuredArrow_op_overPullback P g A K
  HasColimitsOfShape.has_colimit _

/-- The conclusion of the sorried
`CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback`, conditional on the
comma categories being `u`-initially small, and free of `sorryAx`.

The proof deliberately goes through the explicit pointwise left Kan extension rather than
`inferInstance`: in any module importing
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`, instance search
discharges a `HasLeftKanExtension` goal from the sorried global instance, so `inferInstance`
would typecheck here and certify nothing. -/
theorem hasLeftKanExtension_op_overPullback_of_initiallySmall
    [∀ V : P.Over ⊤ Z,
      InitiallySmall.{u} (StructuredArrow V (MorphismProperty.Over.pullback P ⊤ g))]
    (F : (P.Over ⊤ Y)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback P ⊤ g).op.HasLeftKanExtension F :=
  haveI := hasPointwiseLeftKanExtension_op_overPullback_of_initiallySmall P g A F
  (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ F).hasLeftKanExtension

/-- The `@Etale` specialisation of
`AlgebraicGeometry.hasLeftKanExtension_op_overPullback_of_initiallySmall`, which is the exact
conclusion of the sorried instance
`CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback` at `P = @Etale`.

Base change along an arbitrary `g` is representably flat here by
`AlgebraicGeometry.Etale.representablyFlat_overPullback`, so the smallness hypothesis is the
only thing separating this from that instance. -/
theorem Etale.hasLeftKanExtension_op_overPullback_of_initiallySmall
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A]
    [∀ V : Z.Etale,
      InitiallySmall.{u} (StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g))]
    (F : Y.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension F :=
  _root_.AlgebraicGeometry.hasLeftKanExtension_op_overPullback_of_initiallySmall
    (P := @Etale) g A F

section Consistency

/-- For an **étale** `g` the comma categories have initial objects — base change is then right
adjoint to the localization functor `MorphismProperty.Over.map ⊤ ‹Etale g›` — so they are
`u`-initially small for a reason that has nothing to do with cardinality.

This is the sanity check that the reduction above is not vacuous: feeding this instance to
`AlgebraicGeometry.Etale.hasLeftKanExtension_op_overPullback_of_initiallySmall` reproves the
already proved `AlgebraicGeometry.Etale.hasPointwiseLeftKanExtension_op_overPullback`. It is
deliberately **not** an instance: the étale case already has a better route, and registering
it would put an unnecessary `Etale g` search in front of every comma category. -/
theorem Etale.initiallySmall_structuredArrow_overPullback {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [Etale g] (V : MorphismProperty.Over @Etale ⊤ Z) :
    InitiallySmall.{u} (StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)) :=
  haveI : HasInitial (StructuredArrow V (MorphismProperty.Over.pullback @Etale ⊤ g)) :=
    (mkInitialOfLeftAdjoint _
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ g ‹Etale g› _root_.trivial) V).hasInitial
  inferInstance

example {Z Y : Scheme.{u}} (g : Z ⟶ Y) [Etale g] (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (F : Y.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension F :=
  haveI := Etale.initiallySmall_structuredArrow_overPullback g
  Etale.hasLeftKanExtension_op_overPullback_of_initiallySmall g A F

end Consistency

end AlgebraicGeometry
