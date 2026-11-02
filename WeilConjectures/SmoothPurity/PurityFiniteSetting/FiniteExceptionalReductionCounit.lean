/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Live finite exceptional comparison interface

The declarations below realize the live blueprint route, without the withdrawn
four-clause exceptional q-identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
variable (P : PurityFiniteSetting.{u}) (n m : ℕ) (h : m ≤ n)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
/-- Finite reduction preserves the specified finite exceptional adjunction counit.
Source: blueprint finite reduction of purity, Step 4
(blueprint: lem-route-finite-reduction-exceptional-finite-model-counit).
Proof: the exceptional comparison is the right mate of inverse q. Its counit
identity followed by q cancels q inverse. The proof uses the generic mate counit
identity and the inverse cancellation of the specified q. -/
theorem finiteExceptionalReduction_counit
    (L : (FiniteExceptional.domain P.coefficients.l P.extension Y n).FullSubcategory) :
    let c := @HasCompactification.compactification X Y f
        (hasCompactification_of_finiteType_over_field P.field.k X Y f)
    (FiniteExceptional.q P.coefficients.l P.extension P.field
      P.coefficients.different f c h).hom.app
        ((FiniteExceptional.G P.coefficients.l P.extension P.field
          P.coefficients.different f c n).obj L) ≫
      (FiniteExceptional.F P.coefficients.l P.extension P.field
        P.coefficients.different f c m).map
          ((FiniteExceptional.b P.coefficients.l P.extension P.field
            P.coefficients.different f c h).app L) ≫
      (FiniteExceptional.adjunction P.coefficients.l P.extension P.field
        P.coefficients.different f c m).counit.app
          ((FiniteExceptional.Q P.coefficients.l P.extension Y h).obj L) =
      (FiniteExceptional.Q P.coefficients.l P.extension Y h).map
        ((FiniteExceptional.adjunction P.coefficients.l P.extension P.field
          P.coefficients.different f c n).counit.app L) := by
  let c := @HasCompactification.compactification X Y f
    (hasCompactification_of_finiteType_over_field P.field.k X Y f)
  have hc := mateEquiv_counit
    (FiniteExceptional.adjunction P.coefficients.l P.extension P.field
      P.coefficients.different f c n)
    (FiniteExceptional.adjunction P.coefficients.l P.extension P.field
      P.coefficients.different f c m)
    (FiniteExceptional.q P.coefficients.l P.extension P.field
      P.coefficients.different f c h).inv L
  simpa only [FiniteExceptional.b, Iso.app_hom] using
    (Iso.eq_inv_comp ((FiniteExceptional.q P.coefficients.l P.extension P.field
      P.coefficients.different f c h).app
        ((FiniteExceptional.G P.coefficients.l P.extension P.field
          P.coefficients.different f c n).obj L))).mp hc

end WeilConjectures.PurityFiniteSetting
