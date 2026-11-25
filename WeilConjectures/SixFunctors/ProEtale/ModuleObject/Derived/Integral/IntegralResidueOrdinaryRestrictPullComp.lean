/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.ComapUpperStarIsoComposition

/-! # Composition of restriction and derived pullback

## References

- Bhatt--Scholze, *The pro-étale topology for schemes*, Remark 6.8.15.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralResidueOrdinaryRestrictPullComp
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Ordinary scalar restriction commutes with pullback composition. -/
theorem integralResidue_ordinaryRestrictPull_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Z)) :
    (upperStarComp (integralCoeff ℓ E) f g).hom.app
        ((Mod.comap (coefficientMap (integralReductionMap ℓ E) Z)).obj N) ≫
      (f)^*⟦integralCoeff ℓ E⟧.map
        ((comapUpperStarIso (integralReductionMap ℓ E) g).inv.app N) ≫
      (comapUpperStarIso (integralReductionMap ℓ E) f).inv.app
        ((g)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧.obj N) =
    (comapUpperStarIso (integralReductionMap ℓ E) (f ≫ g)).inv.app N ≫
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).map
        ((upperStarComp
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom.app N) := by
  rw [← cancel_mono ((comapUpperStarIso (integralReductionMap ℓ E) f).hom.app
    ((g)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧.obj N))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← cancel_mono ((f)^*⟦integralCoeff ℓ E⟧.map
    ((comapUpperStarIso (integralReductionMap ℓ E) g).hom.app N))]
  simp only [Functor.comp_obj, Category.comp_id, Category.assoc, cancelIso]
  exact comapUpperStarIso_comp (a := integralReductionMap ℓ E) f g N

end AlgebraicGeometry.ProEtale.CondensedRing
