/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib

/-!

# Left Kan extensions for presheaves on the small sites (sorried)

Following the convention of the `SixFunctors` folder, the coefficient category `A` of the
sheaf categories is a Grothendieck abelian category with `Hom`-types in the universe `u`
of the base schemes; this covers the intended applications `A = Ab.{u}` and
`A = ModuleCat.{u} Λ`. The first two instances below are stated for the small sites
defined by a general morphism property `P`, under the assumptions `[P.IsMultiplicative]`,
`[P.IsStableUnderBaseChange]` and `[P.HasOfPostcompProperty P]`; all of them hold for
`P = @Etale`.

## Sorried instances

- `CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback`: left Kan
  extensions along the opposite of base change by an *arbitrary* morphism exist for
  `A`-valued presheaves on the small sites: the sites are essentially small and `A` is
  cocomplete. For `P = @Etale` and an étale morphism this is proved
  (`AlgebraicGeometry.Etale.hasPointwiseLeftKanExtension_op_overPullback` in
  `WeilConjectures.SixFunctors.UpperLowerStar.Etale`).
- `CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overMap`: left Kan
  extensions along the opposite of the localization functor of `h : P f` exist for
  `A`-valued presheaves on the small sites, for the same reason. For `P = @Etale` and an
  open immersion this is proved
  (`AlgebraicGeometry.hasPointwiseLeftKanExtension_of_etale_and_mono` in
  `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Etale`).
- `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`:
  the left Kan extension along the opposite of base change by an *arbitrary* morphism is
  left exact: the indexing comma categories of the pointwise left Kan extensions are
  cofiltered (base change preserves the finite limits of the étale slice), so the Kan
  extension is computed by filtered colimits, which are exact in `A` by AB5. For an étale
  morphism this is proved
  (`AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback` in
  `WeilConjectures.SixFunctors.UpperLowerStar.Etale`).

The instances are stated for any Grothendieck abelian `A` — their mathematical content
does not use concreteness of `A` — and with their binders written out explicitly (rather
than taken from a `variable` block), so that the hypotheses on `A` are part of the
statements even though the `sorry` bodies do not use them.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Left Kan extensions along the opposite of base change by an *arbitrary* morphism
`g : W ⟶ U` exist for `A`-valued presheaves on the small sites of `P`-schemes: the sites
are essentially small for the étale-like properties `P` of interest and the Grothendieck
abelian category `A` is cocomplete. For `P = @Etale` and an étale `g` this needs no
smallness argument, see `AlgebraicGeometry.Etale.hasPointwiseLeftKanExtension_op_overPullback`. -/
instance hasLeftKanExtension_op_overPullback (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {W U : Scheme.{u}} (g : W ⟶ U) (F : (P.Over ⊤ U)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback P ⊤ g).op.HasLeftKanExtension F :=
  sorry

/-- Left Kan extensions along the opposite of the localization functor of `h : P f` exist
for `A`-valued presheaves on the small sites of `P`-schemes: the sites are essentially
small for the étale-like properties `P` of interest and the Grothendieck abelian category
`A` is cocomplete. For `P = @Etale` and an open immersion this needs no smallness
argument, see `AlgebraicGeometry.hasPointwiseLeftKanExtension_of_etale_and_mono`. -/
instance hasLeftKanExtension_op_overMap (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {V U : Scheme.{u}} {f : V ⟶ U} (h : P f) (F : (P.Over ⊤ V)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasLeftKanExtension F :=
  sorry

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

/-- The left Kan extension along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` is left exact for a Grothendieck abelian coefficient category: the indexing
comma categories of the pointwise left Kan extensions are cofiltered (base change
preserves the finite limits of the étale slice), so the Kan extension is computed by
filtered colimits, which are exact in `A` by AB5. For an étale `g` this is proved as
`Etale.preservesFiniteLimits_op_lan_overPullback`. -/
instance Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian
    (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
      (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  sorry

end AlgebraicGeometry
