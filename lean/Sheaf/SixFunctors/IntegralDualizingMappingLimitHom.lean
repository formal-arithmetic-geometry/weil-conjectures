/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
import Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAt

/-! The degree-zero mapping adjunction for the prescribed dualizing limit.

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
The degree-zero Hom equivalence induced by the same finite mapping tower as the
global comparison.  Derived sections and the coefficient-point equivalence turn
the tower isomorphism into the displayed bijection for every constructible object.

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph
(blueprint: lem-coef-integral-dualizing-mapping-limit-hom).
-/
theorem integralDualizing_mapping_limit_hom
    (T : NormalizedDVRTower l E X D hl)
    (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
        (e m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h))
    (M : sfIntegralConstructibleCategory l E X)
    (hM : IntegralDualizingLimitPresentation l E D hl X T M.obj) :
    ∀ K : sfIntegralConstructibleCategory l E X,
      Nonempty ((K.obj ⟶ M.obj) ≃
        ((integralDualizingLimit l E (Spec (.of D.k))).obj
          ((integralDualizingCompactTower l E D hl X).obj K.obj) ⟶
            (DerivedCategory.singleFunctor (scalarReductionSource l E (Spec (.of D.k))) 0).obj
              (SheafOfModules.unit
                (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))) := by
  intro K
  simpa only [] using
    (integralDualizing_mapping_limit_hom_at D l hl E X T e he M hM K)

end WeilConjectures
