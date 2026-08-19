/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!

# Left Kan extensions for presheaves on the small sites (sorried)

Left Kan extensions along the opposites of base change and of the localization functors
exist for `A`-valued presheaves on the small sites of `P`-schemes, for a Grothendieck
abelian category `A` with `Hom`-types in the universe `u` of the base schemes: the
categories indexing the pointwise left Kan extensions are essentially small and `A` is
cocomplete.

Moreover the left Kan extension along the opposite of base change is left exact: the
indexing comma categories of the pointwise left Kan extensions are cofiltered — base
change preserves the finite limits of the étale slice — so the Kan extension is computed
by filtered colimits, which are exact in `A` by AB5.

## The smallness hypothesis

The smallness input is *not* essential smallness of the small sites themselves: those are
not essentially small, see the module docstring of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`. What is available is the
essentially small dense affine subsite of `Mathlib.AlgebraicGeometry.Sites.Affine`, and
the indexing comma categories have to be reduced to it. Accordingly the instances below
carry `[IsZariskiLocalAtSource P]` and an
`[EssentiallySmall.{u} (MorphismProperty.CostructuredArrow P ⊤ Scheme.Spec _)]` hypothesis
on the slice the colimit is indexed by; both hold for `P = @Etale` and the second fails
for `P = ⊤`, whose slice is all of `Over U` and admits colimits of unbounded size.

A cheaper route is available for `hasLeftKanExtension_op_overMap` when `f` is a
*monomorphism* — in particular for the open immersions along which the localization lower
shriek is used throughout `WeilConjectures.SixFunctors`: a factorization of the structure
morphism of `W : P.Over ⊤ U` through `f` is then unique, so the indexing comma category is
either empty or has a terminal object and no smallness is needed at all. Discharging the
instance that way would let its smallness hypothesis be dropped again.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Left Kan extensions along the opposite of base change by an *arbitrary* morphism
`g : W ⟶ U` exist for `A`-valued presheaves on the small sites of `P`-schemes: the
indexing comma categories reduce to the essentially small dense affine subsite of
`P.Over ⊤ U` (see the module docstring) and the Grothendieck abelian category `A` is
cocomplete. -/
instance hasLeftKanExtension_op_overPullback (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [IsZariskiLocalAtSource P]
    {W U : Scheme.{u}}
    [EssentiallySmall.{u} (MorphismProperty.CostructuredArrow P ⊤ Scheme.Spec U)]
    (g : W ⟶ U) (F : (P.Over ⊤ U)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback P ⊤ g).op.HasLeftKanExtension F :=
  sorry

/-- Left Kan extensions along the opposite of the localization functor of `h : P f` exist
for `A`-valued presheaves on the small sites of `P`-schemes: the indexing comma categories
reduce to the essentially small dense affine subsite of `P.Over ⊤ V` (see the module
docstring) and the Grothendieck abelian category `A` is cocomplete. For a monomorphism `f`
the smallness hypothesis is not needed, see the module docstring. -/
instance hasLeftKanExtension_op_overMap (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [IsZariskiLocalAtSource P]
    {V U : Scheme.{u}}
    [EssentiallySmall.{u} (MorphismProperty.CostructuredArrow P ⊤ Scheme.Spec V)]
    {f : V ⟶ U} (h : P f) (F : (P.Over ⊤ V)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasLeftKanExtension F :=
  sorry

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

/-- The left Kan extension along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` is left exact for a Grothendieck abelian coefficient category: the indexing
comma categories of the pointwise left Kan extensions are cofiltered (base change
preserves the finite limits of the étale slice), so the Kan extension is computed by
filtered colimits, which are exact in `A` by AB5. -/
instance Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian
    (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
      (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  sorry

end AlgebraicGeometry
