/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.IntegralTwistBaseChange
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.IntrinsicCoefficientTwists

import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.IntegralLineTensorComparison
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic

/-!
# Integral twisting and completed derived scalar extension

Source: blueprint `sec-smooth-purity/sk-prop-sf-existence/prop-weil-twist-preserves.md`,
proof, final integral/common-stage sentence
(blueprint: lem-weil-integral-twist-derived-scalar).

The ordinary and completed comparisons below use the published functors. The equality
with their K-flat counits specifies descent of the displayed chain map. The equation
with the published completion map specifies its conjugation. Membership of the two
endpoints makes the natural isomorphism an isomorphism in the full integral categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]

/-- Twisting commutes with completed integral scalar extension by the specified chain map.
Source: blueprint `prop-weil-twist-preserves`, final integral/common-stage sentence
(blueprint: lem-weil-integral-twist-derived-scalar).

Proof:
1. Use `integral_twist_base_change` and `pur_twist_sheaf_locally_free` to identify
   the base change of each signed line with the target line. Tensor powers reduce
   by balancing; dual bases reduce to dual bases. Thus each signed line and its
   dual are locally the coefficient ring, and all finite reductions have rank one.
2. Tensor with a line and its dual gives inverse additive equivalences by
   `SheafOfModules.tensorClosed`. They are exact, so the lines are flat and tensor
   preserves cohomology and each vanishing interval.
3. The given flat-term K-flat representative stays K-flat with flat terms after
   twisting. Associativity identifies its tensor with an acyclic complex with the
   twist of an acyclic tensor. Closedness justifies rebracketing the total sums;
   the line is in degree zero, so there is no additional differential sign.
4. The balanced map sends (x tensor y) tensor b to (x tensor b) tensor (y tensor 1).
   Its inverse sends (x tensor b) tensor (y tensor c) to (x tensor y) tensor bc.
   The bilinear universal property and sheafification extend these formulas and
   prove that the composites are identities. Compose with `twistLineScalarIso`.
   Both formulas commute with differentials, giving the chain isomorphism below.
5. Site derived-tensor descent and derived change of rings identify the two sides
   on K-flat representatives. Change of rings preserves K-flat flat-term models.
   The pure-tensor formula commutes with every chain map; localization extends
   naturality to derived arrows and makes the comparison independent of P.
6. `integralLineTensorComparison` identifies ordinary tensor by a line with the
   completed reduction tower. Its reduction maps are precisely the balanced maps
   above, so its first Roos map is the required completeness map. Thus twists of
   complete objects are complete.
7. Exact tensor with the finite rank-one reductions preserves the common support
   interval. On each constructible stratum refine the local trivializing covers;
   tensor with the finite free rank-one line preserves the finite constant model.
   Hence twists preserve `sfIntegralConstructible`, with the same uniform interval.
8. Apply `finiteFreeCompletedScalarComparison` to C and C(m). Conjugate the ordinary
   comparison by its specified completion maps chi. Naturality and invertibility
   follow factor by factor. `sfIntegralScalarExtension_constructible` and step 7
   put both endpoints in the full integral category, whose inclusion is fully faithful.
-/
theorem integral_twist_derived_scalar (m : ℤ) :
    ∃ (α : (sfIntegralConstructible l E S).ι ⋙
        (integralSheafTwist l E S m).mapDerivedCategory ⋙
        completedDerivedScalarExtension l E F ι S ≅
      (sfIntegralConstructible l E S).ι ⋙ completedDerivedScalarExtension l E F ι S ⋙
        (integralSheafTwist l F S m).mapDerivedCategory)
      (β : (sfIntegralConstructible l E S).ι ⋙
        (integralSheafTwist l E S m).mapDerivedCategory ⋙
        integralScalarExtensionOfUniverses l E F ι S ≅
      (sfIntegralConstructible l E S).ι ⋙ integralScalarExtensionOfUniverses l E F ι S ⋙
        (integralSheafTwist l F S m).mapDerivedCategory),
      (∀ (C : sfIntegralConstructibleCategory l E S)
        (P : (integralOperationsGoodComplex l E S).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ C.obj),
        ∃ a : (completedOrdinaryScalarComplex l E F ι S).obj
            (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj) ≅
          ((integralSheafTwist l F S m).mapHomologicalComplex (.up ℤ)).obj
            ((completedOrdinaryScalarComplex l E F ι S).obj P.obj),
          (∀ (i : ℤ) (U : S.ProEtᵒᵖ)
            (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U)
            (x : (P.obj.X i).val.obj U) (y : (integralTwistLine l E S m).val.obj U),
            (a.hom.f i).val.app U
                (completedScalarTensorSection l E F ι S _ U b
                  (SheafOfModules.siteSheafTensorTmul
                    (A := completedIntegralCommRingSheafUnrestricted l E S) _ _ U x y)) =
              SheafOfModules.siteSheafTensorTmul
                (A := completedIntegralCommRingSheafUnrestricted l F S) _ _ U
                (completedScalarTensorSection l E F ι S (P.obj.X i) U b x)
                ((twistScalarMaps l E S F ι m).val.app U y)) ∧
          (completedDerivedScalarExtension l E F ι S).map
              ((integralSheafTwist l E S m).mapDerivedCategory.map e.inv) ≫
            (completedDerivedScalarExtension l E F ι S).map
              ((integralSheafTwist l E S m).mapDerivedCategoryFactors.hom.app P.obj) ≫
            completedScalarCounit l E F ι S
              (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
            DerivedCategory.Q.map a.hom =
          α.hom.app C ≫ (integralSheafTwist l F S m).mapDerivedCategory.map
              ((completedDerivedScalarExtension l E F ι S).map e.inv) ≫
            (integralSheafTwist l F S m).mapDerivedCategory.map
              (completedScalarCounit l E F ι S P.obj) ≫
            (integralSheafTwist l F S m).mapDerivedCategoryFactors.hom.app
              ((completedOrdinaryScalarComplex l E F ι S).obj P.obj)) ∧
      (∀ C : sfIntegralConstructibleCategory l E S,
        (completedScalarComparison l E F ι S).app
            ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj) ≫ β.hom.app C =
          α.hom.app C ≫ (integralSheafTwist l F S m).mapDerivedCategory.map
            ((completedScalarComparison l E F ι S).app C.obj)) ∧
      ∀ C : sfIntegralConstructibleCategory l E S,
        sfIntegralConstructible l E S
            ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj) ∧
          sfIntegralConstructible l F S
            ((integralScalarExtensionOfUniverses l E F ι S).obj
              ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj)) ∧
          sfIntegralConstructible l F S
            ((integralScalarExtensionOfUniverses l E F ι S).obj C.obj) ∧
          sfIntegralConstructible l F S
            ((integralSheafTwist l F S m).mapDerivedCategory.obj
              ((integralScalarExtensionOfUniverses l E F ι S).obj C.obj)) := by
  sorry

end WeilConjectures
