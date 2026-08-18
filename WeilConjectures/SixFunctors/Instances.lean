/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib

/-!

# Sorried instances for the six functor formalism

Following the convention of the `SixFunctors` folder, the coefficient category `A` of the
sheaf categories is a concrete Grothendieck abelian category with objects in `Type u'`,
`Hom`-types and underlying types in the universe `u` of the base schemes, and the
forgetful functor preserving limits and filtered colimits and reflecting isomorphisms;
this covers the intended applications `A = Ab.{u}` and `A = ModuleCat.{u} Λ`. In this
generality Mathlib provides sheafification on the small étale sites and the Grothendieck
abelian structure of the étale sheaf categories
(`Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`). This file collects the remaining
instances needed to construct the six functors which are mathematically correct but not
yet formalized; they are recorded here with `sorry`, so that the constructions of the
folder carry no hypotheses beyond the ones above.

The instances are stated for the small sites defined by a general morphism property `P`,
under the assumptions `[P.IsMultiplicative]`, `[P.IsStableUnderBaseChange]` and
`[P.HasOfPostcompProperty P]`; all of them hold for `P = @Etale`. Mathematically they
make the small site `P.Over ⊤ U` finitely complete and — for the étale-like properties of
interest, which are locally of finite presentation — essentially small, which is what the
statements below rest on.

## Sorried instances

- `CategoryTheory.GrothendieckTopology.isContinuous_overPullback`: base change along an
  *arbitrary* morphism is continuous for the small `Q`-topologies of `P`-schemes, for
  `Q ≤ P`. Since `Q ≤ P` is not a class, the inequality enters as a `Fact` instance;
  `CategoryTheory.MorphismProperty.instFactLERefl` (proved below) provides it for
  `Q = P`, so for the small étale sites the instance fires with no further input. For
  `g` satisfying `P` continuity is proved
  (`CategoryTheory.GrothendieckTopology.isContinuous_overPullback_of_le` in
  `WeilConjectures.SixFunctors.LowerShriek.Defs`); in general it follows as in the étale
  case (`AlgebraicGeometry.Etale.isContinuous_overPullback` in
  `WeilConjectures.SixFunctors.UpperLowerStar.Etale`, which is proved): base change
  preserves covers because covers are jointly surjective families of `Q`-morphisms and
  `Q` is stable under base change, and it preserves compatible families because it is
  representably flat, the small site being finitely complete.
- `CategoryTheory.GrothendieckTopology.hasSheafify_smallGrothendieckTopology`:
  sheafification for `A`-valued presheaves on the small `Q`-sites of `P`-schemes: the
  sites are essentially small and the Grothendieck abelian `A` is complete and cocomplete
  with exact filtered colimits, so the plus-construction applies and is left exact. For
  the small étale sites and *concrete* `A` this is proved in Mathlib.
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
does not use the concreteness of `A` — and with their binders written out explicitly
(rather than taken from a `variable` block), so that the hypotheses on `A` are part of
the statements even though the `sorry` bodies do not use them.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- The reflexivity `P ≤ P` of the order on morphism properties, as a `Fact`. This is what
lets the `Fact (Q ≤ P)`-guarded instances below fire for `Q = P`, in particular for the
small étale sites (`P = Q = @Etale`). -/
instance CategoryTheory.MorphismProperty.instFactLERefl {C : Type*} [Category C]
    (P : MorphismProperty C) : Fact (P ≤ P) :=
  ⟨le_rfl⟩

namespace CategoryTheory.GrothendieckTopology

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` is continuous for the small
`Q`-topologies of `P`-schemes, for `Q ≤ P` (assumed as a `Fact`, provided for `Q = P` by
`CategoryTheory.MorphismProperty.instFactLERefl`). For `g` satisfying `P` this is
`CategoryTheory.GrothendieckTopology.isContinuous_overPullback_of_le`; in general it is
proved as in the étale case (`AlgebraicGeometry.Etale.isContinuous_overPullback`): base
change preserves covers because covers are jointly surjective families of `Q`-morphisms
and `Q` is stable under base change, and it preserves compatible families because it is
representably flat, the small site being finitely complete. -/
instance isContinuous_overPullback (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    [Fact (Q ≤ P)] {W U : Scheme.{u}} (g : W ⟶ U) :
    (MorphismProperty.Over.pullback P ⊤ g).IsContinuous
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P)) :=
  sorry

/-- Sheafification for `A`-valued presheaves on the small `Q`-site of `P`-schemes over a
scheme `U`, for a Grothendieck abelian coefficient category `A` with `Hom`-types in the
universe `u` of the base schemes: the site is essentially small for the étale-like
properties `P` of interest and `A` is complete and cocomplete with exact filtered
colimits, so the plus-construction applies and is left exact. For the small étale sites
and *concrete* `A` this is proved in Mathlib
(`Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`). -/
instance hasSheafify_smallGrothendieckTopology (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    HasSheafify (U.smallGrothendieckTopology Q (Q := P)) A :=
  sorry

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
