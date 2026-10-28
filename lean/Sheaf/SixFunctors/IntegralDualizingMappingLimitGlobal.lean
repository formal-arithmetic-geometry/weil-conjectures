/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
import Sheaf.SixFunctors.IntegralDualizingMappingTowerLimit
import Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComparison
import Sheaf.SixFunctors.IntegralDualizingCoefficientHomTowerLimit

/-! The global mapping-complex comparison for the prescribed dualizing limit.

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/--
The mapping-complex comparison obtained by applying the finite adjunctions to the
coherent Roos presentation and passing to the derived inverse limit.  The proof
uses the common Tor bounds, compact-support reduction, scalar adjunction, the
finite counit compatibility, and the coefficient tower trace and currying maps.
The resulting tower map is an isomorphism, and completeness of the DVR identifies
its limit with the coefficient derived dual.

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph
(blueprint: lem-coef-integral-dualizing-mapping-limit-global).
-/
theorem integralDualizing_mapping_limit_global
    (T : NormalizedDVRTower l E X D hl)
    (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
        (e m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h))
    (M : sfIntegralConstructibleCategory l E X)
    (hM : IntegralDualizingLimitPresentation l E D hl X T M.obj) :
    Nonempty (integralDualizingGlobalHom l E X M.obj ≅
      (integralDualizingCompactSections l E D hl X).op ⋙
        coefficientDerivedDual (integralDualizingCoefficients l E)) := by
  obtain ⟨a⟩ := integralDualizing_mapping_tower_limit D l hl E X T M hM
  obtain ⟨b⟩ := integralDualizing_mapping_tower_finite_comparison D l hl E X T e he
  obtain ⟨c⟩ := integralDualizing_coefficient_hom_tower_limit l E
  exact ⟨a ≪≫ Functor.isoWhiskerRight b
    (CoefTower.totalLimit (integralDualizingCoefficients l E)) ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (integralDualizingCompactSections l E D hl X).op c⟩

end WeilConjectures
