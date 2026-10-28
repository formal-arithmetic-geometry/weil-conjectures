/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
import Sheaf.SixFunctors.IntegralDualizingGlobalHomologyAtZero
import Sheaf.SixFunctors.IntegralDualizingCoefficientHomologyAtZero

/-! The degree-zero extraction from the global integral dualizing comparison.

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph.
The global mapping comparison supplies an isomorphism of derived global-Hom functors;
this node isolates the remaining passage from its component at a constructible object
to the displayed Hom equivalence at the coefficient point.
(blueprint: lem-coef-integral-dualizing-mapping-limit-hom-at-degree-zero)
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
The degree-zero component of a global integral dualizing comparison gives the
coefficient-point Hom equivalence for one constructible source and target.
The tower, finite identifications, and Roos presentation are encapsulated in the
supplied global comparison; this statement records only the degree-zero extraction.

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph,
where the global RHom comparison is converted to the displayed degree-zero Hom
bijection by derived sections and the coefficient-point equivalence.
(blueprint: lem-coef-integral-dualizing-mapping-limit-hom-at-degree-zero)
-/
theorem integralDualizing_mapping_limit_hom_at_degree_zero
    (M : sfIntegralConstructibleCategory l E X)
    (K : sfIntegralConstructibleCategory l E X)
    (η : integralDualizingGlobalHom l E X M.obj ≅
      (integralDualizingCompactSections l E D hl X).op ⋙
        coefficientDerivedDual (integralDualizingCoefficients l E)) :
    Nonempty ((K.obj ⟶ M.obj) ≃
      ((integralDualizingLimit l E (Spec (.of D.k))).obj
        ((integralDualizingCompactTower l E D hl X).obj K.obj) ⟶
          (DerivedCategory.singleFunctor (scalarReductionSource l E (Spec (.of D.k))) 0).obj
            (SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))) := by
  obtain ⟨a⟩ := integralDualizing_global_homology_at_zero l E X M K
  obtain ⟨b⟩ := integralDualizing_coefficient_homology_at_zero D l hl E X K
  let h := (DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) 0).mapIso
      (η.app (Opposite.op K))
  exact ⟨a.symm.toEquiv.trans (h.toLinearEquiv.toEquiv.trans b)⟩

end WeilConjectures
