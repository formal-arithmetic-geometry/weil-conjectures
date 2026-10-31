/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import all WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import all WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import all WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange

/-! # Proper/open interchange and its tensor square on arbitrary étale bases

Source: Stacks Project, more-etale.tex, Tag 0F7B, torsion-ring case (b), in a Cartesian
square with open horizontal arrows. The tensor equation is the additional mate calculation
using sites-cohomology.tex, Tags 0GL1 and 0B56, with the canonical comparisons of Tag 0E48.
(blueprint: lem-sf-etale-proper-open-tensor-square).

The exchange is the existing `openImmersionLowerShriekLowerStarExchange`, whose component
formula fixes exactly the beta/unit/counit normalization in the node. Pullbacks in the tensor
formula use their canonical left-derived presentations; exactness identifies them with the
termwise inverse images used to define that exchange.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Proper/open interchange is an isomorphism and commutes with the counit-defined
projection maps on arbitrary unbounded constant-coefficient module derived categories.

Source: Stacks Project, more-etale.tex, Tag 0F7B(b), Cartesian open specialization;
additional tensor identity: sites-cohomology.tex, Tags 0GL1 and 0B56, with Tag 0E48.
(blueprint: lem-sf-etale-proper-open-tensor-square).

Here `Gamma = openImmersionLowerShriekLowerStarExchange` is the mate of the inverse of
`mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`. Its component is the unit for
`p`, followed by `R_p(beta)`, followed by `R_p(J_k(counit_r))`. The inverse open projection
isomorphisms are the node's delta maps. The last factor on the left explicitly transports
`P_k P_p N` to `P_r P_i N` by the canonical square comparison, under `M` tensor and `R_p J_k`.

Proof:
1. Exact extension/restriction and its termwise derived adjunction have invertible open
   unit, since restriction of extension by zero is the original sheaf. Thus both open
   extensions are fully faithful. Their derived stalks vanish outside their opens by the
   extension-by-zero stalk formula and exactness of stalks.
2. A finite ring is torsion. At a geometric point outside `W`, the pullback of `U` is
   empty. Arbitrary open base change gives zero pullback of `J_k M`; unbounded proper
   base change over torsion rings then gives zero stalk of `R_p J_k M` at that point.
3. The open counit `J_i P_i (R_p J_k M) -> R_p J_k M` is an isomorphism: inside `W` use
   the open unit and the triangle identity, and outside `W` both stalks vanish. Apply the
   stalk/cohomology test to its cone. Hence `R_p J_k M` is in the essential image of `J_i`.
4. Apply the fully-faithful mate-image criterion to `P_r`, `P_p`, `J_i`, `J_k`, and the
   specified beta. The mate component formula is precisely Gamma; units, beta and counits
   are natural, so it is a natural isomorphism.
5. Ordinary open projection exchange gives the tensor-action square for beta. Its tensor
   and pullback-composition comparisons are the canonical monoidal derived comparisons;
   this step needs neither properness nor any restriction on the complexes.
6. Apply tensor-square mate transfer. Its mate is Gamma and its counit-transpose projections
   are `rightDerivedLowerStarProjectionMap`. The two composites have the same transpose,
   namely `K(c) beta P_p(delta_i)`, where `c = (counit_r tensor 1) mu_r`. The adjunction Hom
   bijection is injective, giving the stated equality. No projection map is inverted. -/
theorem etaleProperOpenTensorSquare
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} {r : U ⟶ W} {k : U ⟶ V} {i : W ⟶ Z} {p : V ⟶ Z}
    [IsProper p] [IsOpenImmersion i] [IsOpenImmersion k]
    (sq : IsPullback r k i p) :
    IsIso (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq) ∧
      ∀ (M : DerivedCategoryModule A U) (N : DerivedCategoryModule A Z),
        ((-⊗ᴸ-(Z)[ModuleCat.{u + 1} A]).map
            ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq).app M)).app N ≫
          ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app
            (D((k)_!open[ModuleCat.{u + 1} A]).obj M)).app N ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (((derivedOpenImmersionLowerShriekProjectionIso
              (ModuleCat.{u + 1} A) k).inv.app M).app
              (L((p)^*[ModuleCat.{u + 1} A]).obj N)) ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (D((k)_!open[ModuleCat.{u + 1} A]).map
              (((-⊗ᴸ-(U)[ModuleCat.{u + 1} A]).obj M).map
                ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).hom.app N))) =
        ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) i).inv.app
            (R((r)_*[ModuleCat.{u + 1} A]).obj M)).app N ≫
          D((i)_!open[ModuleCat.{u + 1} A]).map
            (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) r).app M).app
              (L((i)^*[ModuleCat.{u + 1} A]).obj N)) ≫
          (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq).app
            (((-⊗ᴸ-(U)[ModuleCat.{u + 1} A]).obj M).obj
              (L((r)^*[ModuleCat.{u + 1} A]).obj
                (L((i)^*[ModuleCat.{u + 1} A]).obj N))) := by
  refine ⟨isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring A
    isAddTorsion_of_finite sq, ?_⟩
  intro M N
  exact (mixed_projection (ModuleCat.{u + 1} A) sq M N).symm

end AlgebraicGeometry.Etale
