/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Compactification.NagataDensityNormalizationSheaves
public import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Compactification.NagataDensityNormalizationSetup
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Proper direct image through the schematic closure

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-nagata-density-normalization/det-nagata-density-normalization-pushforward.md`.
(blueprint: det-nagata-density-normalization-pushforward).

The comparison is a specified natural transformation, formed from the closed derived
adjunction unit, the normalized open-extension base change, and derived composition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical direct-image comparison through the schematic closure.
Source: blueprint density-normalization pushforward, Steps 1--3
(blueprint: det-nagata-density-normalization-pushforward).
The parameter beta is normalized in the theorem by its inverse adjunction transpose.
Apply Rp_* to the derived closed unit on j_! and then this base-change
isomorphism. Finish with the composition comparison characterized by right-derived
units. Exactness of closed pushforward identifies this with the degreewise sheaf map
of nagataDensityNormalizationSheaves followed by Ri_* = D(i_*) and composition. -/
def nagataDensityNormalizationPushforwardMap {X S : Scheme.{u}} {f : X ⟶ S}
    (c : Compactification f) [IsNoetherian c.Z]
    (β : openImmersionLowerShriek Λ c.i ⋙ upperStar Λ c.i.imageι ≅
      openImmersionLowerShriek Λ c.i.toImage) :
    (openImmersionLowerShriek Λ c.i).mapDerivedCategory ⋙
        moduleObjectDerivedPushforward Λ c.g ⟶
      (openImmersionLowerShriek Λ c.i.toImage).mapDerivedCategory ⋙
        moduleObjectDerivedPushforward Λ (c.i.imageι ≫ c.g) :=
  let J := (openImmersionLowerShriek Λ c.i).mapDerivedCategory
  let JZ := (openImmersionLowerShriek Λ c.i.toImage).mapDerivedCategory
  let I := (upperStar Λ c.i.imageι).mapDerivedCategory
  let R := moduleObjectDerivedPushforward Λ c.i.imageι
  let P := moduleObjectDerivedPushforward Λ c.g
  let a := (upperStarLowerStarAdjunction Λ c.i.imageι).mapDerivedCategoryRightDerivedAdjunction
  let b : J ⋙ I ≅ JZ :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso β
  let t : J ⟶ JZ ⋙ R :=
    (Functor.rightUnitor J).inv ≫ Functor.whiskerLeft J a.unit ≫
      (Functor.associator J I R).inv ≫ Functor.whiskerRight b.hom R
  letI := (upperStarLowerStarAdjunction Λ c.i.imageι).preservesKInjectiveComplexes
  Functor.whiskerRight t P ≫ (Functor.associator JZ R P).hom ≫
    Functor.whiskerLeft JZ
      (Functor.rightDerivedFunctorCompIso' (lowerStar Λ c.i.imageι) (lowerStar Λ c.g)
        (lowerStarComp Λ c.i.imageι c.g)).hom

/-- For every unbounded derived object, proper direct image of extension by zero agrees
canonically with proper direct image through the schematic closure.
Source: blueprint main-20261015, density-normalization pushforward, entire statement
(blueprint: det-nagata-density-normalization-pushforward).

Proof: (1) nagataDensityNormalizationSetup gives the closed image and its complementary
open V. Noetherian opens, including V intersected with any affine open, are quasi-compact
(lem-weil-pbc-noetherian-open-subscheme-noetherian). Apply the sheaf-exactness clause of
condensed_open_closed_recollement: i^* and i_* are exact for these same coefficients.
The exact right-derived comparison of def-sfb-right-derived-exact gives Ri_* = D(i_*)
on the whole unbounded category; no bounded-below derived recollement is applied here.
(2) upperStarLowerStarAdjunction and Adjunction.preservesKInjectiveComplexes show that
i_* takes K-injectives to K-injectives. The right-derived units and lowerStarComp give
a unique composition comparison R(p i)_* -> Rp_* Ri_*. At a K-injective I all three
units are invertible, since i_* I is K-injective, so this comparison is invertible.
K-injective representatives give invertibility everywhere, without a boundedness or
cohomological-dimension assumption. This is rightDerivedFunctorCompIso'.
(3) nagataDensityNormalizationSheaves identifies j_! with i_* j_Z,! via the closed unit
and its normalized base change. Under the exact comparison in (1), the derived closed
unit used in the map above is that very degreewise unit. Apply Rp_* to this isomorphism
and compose with (2). All factors are isomorphisms, so the specified component is an
isomorphism in D(S_proet, Lambda_S), naturally in K. -/
theorem nagataDensityNormalizationPushforward {X S : Scheme.{u}} (f : X ⟶ S)
    (c : Compactification f) [IsNoetherian c.Z] :
    ∃ β : openImmersionLowerShriek Λ c.i ⋙ upperStar Λ c.i.imageι ≅
        openImmersionLowerShriek Λ c.i.toImage,
      (∀ M, β.inv.app M =
        ((openImmersionLowerShriekUpperStarAdjunction Λ c.i.toImage).homEquiv M
          ((upperStar Λ c.i.imageι).obj ((openImmersionLowerShriek Λ c.i).obj M))).symm
            ((openImmersionLowerShriekUpperStarAdjunction Λ c.i).unit.app M ≫
              (nagataClosurePullbackComparison Λ c).hom.app
                ((openImmersionLowerShriek Λ c.i).obj M))) ∧
      ∀ K : DerivedCategory
          (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj Λ X)),
        IsIso ((nagataDensityNormalizationPushforwardMap Λ c β).app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
