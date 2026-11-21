/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-!
# Underived sheaf monoidal square for scalar/site comparison

## References

* [Stacks, Tag 03EK]
* [Stacks, Tag 03EL]
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

namespace WeilConjectures.FiniteFreeCoefficients.Sites

attribute [local instance] Sheaf.monoidalCategory
-- Use the site's direct monoidal sheafification instance, as in ScalarExtensionMonoidal.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

/-- The existing sheafified scalar balancing tensorator (`composeAndSheafifyOplaxMonoidal`),
specialized to the etale site. -/
-- This is definitionally the project's ordinary scalar tensorator; the local instance
-- avoids importing derived exceptional-coefficient constructions for an underived square.
local instance etaleScalarOplax {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

-- The etale scalar tensorator is the project instance
-- `AlgebraicGeometry.Etale.ExceptionalCoefficients.ordinaryOplax` (the sheafified scalar
-- balancing map), the same construction as the pro-etale instance
-- `AlgebraicGeometry.ProEtale.oplaxMonoidal_sheafExtendScalars`.

/-- The ordinary scalar/site comparison square commutes on module sheaves. -/
theorem normalized_stage_site_sheaf_tensor_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.sheafExtendScalars φ X).map
          (Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X) M N) ≫
        Functor.OplaxMonoidal.δ (ProEtale.sheafExtendScalars φ X)
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj M)
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj N) ≫
        ((ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).inv.app M ⊗ₘ
          (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).inv.app N) =
      (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).inv.app (M ⊗ N) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).map
          (Functor.OplaxMonoidal.δ (ProEtale.etaleSheafExtendScalars φ X) M N) ≫
        Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
          ((ProEtale.etaleSheafExtendScalars φ X).obj M)
          ((ProEtale.etaleSheafExtendScalars φ X).obj N) := by
  let := ProEtale.laxMonoidal_sheafComposeRestrictScalars φ X
  let : (sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1} φ)).LaxMonoidal :=
    sheafComposeLaxMonoidal _ _
  have hβ : NatTrans.IsMonoidal
      (ProEtale.comparisonLowerStarCompSheafComposeRestrictScalarsIso φ X).hom := by
    exact Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
      X.toProEt X.smallEtaleTopology (Scheme.ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} φ)
  let := hβ
  let : (ProEtale.etaleSheafExtendScalarsAdjunction φ X).IsMonoidal :=
    isMonoidal_sheafAdjunction _ (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  have h := conjugateEquiv_symm_app_tensor_comp_δ
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X))
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
      (ProEtale.sheafExtendScalarsAdjunction φ X))
    (ProEtale.comparisonLowerStarCompSheafComposeRestrictScalarsIso φ X).hom M N
  simpa only [ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso,
    conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv,
    Functor.OplaxMonoidal.comp_δ, Category.assoc] using h.symm

end WeilConjectures.FiniteFreeCoefficients.Sites
