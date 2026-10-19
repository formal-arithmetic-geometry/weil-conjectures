/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition
import Sheaf.AlgebraicGeometry.HigherDirectImageOverCoherence
import Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity
import Sheaf.AlgebraicGeometry.SmallEtaleAffineColimitDetection

public import Sheaf.AlgebraicGeometry.BaseChangeSourceImageSheafCoherence

/-! # Descent of base-change source images

Source: Stacks Project Tag 09Z1 and the limit step of Tag 0F07.
(blueprint: lem-sbc-source-image-limit-descent)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
namespace BaseChangeSourceImageLimitDescent
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} [IsAffine S]
variable (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)

set_option backward.isDefEq.respectTransparency true in
omit [IsAffine S] in
/-- Apply the compatibility square to geometric stalks. -/
theorem source_square {U V : Over T} (φ : U ⟶ V) :
    baseChangeStalkMap Λ p g q F x V ≫ baseChangeTargetStalkMap Λ p g q F x φ =
      (X.uliftPointSmallEtale x).sheafFiber.map
        ((sourceIso Λ p g q F V).hom ≫
          ((p)^*[ModuleCat.{u + 1} Λ]).map (higherDirectImageOverMap Λ g F q φ) ≫
          (sourceIso Λ p g q F U).inv) ≫ baseChangeStalkMap Λ p g q F x U := by
  simp only [baseChangeStalkMap, baseChangeTargetStalkMap, ← Functor.map_comp]
  congr 1
  exact source_square_sheaf Λ p (V.hom ≫ g) q
    (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
    (IsPullback.of_hasPullback (V.hom ≫ g) p) φ.left (U.hom ≫ g)
    (by rw [← Category.assoc, Over.w]) (IsPullback.of_hasPullback (U.hom ≫ g) p)
    _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj F)
    ((upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom (Over.w φ).symm).inv.app F)


end BaseChangeSourceImageLimitDescent
end AlgebraicGeometry.Etale
