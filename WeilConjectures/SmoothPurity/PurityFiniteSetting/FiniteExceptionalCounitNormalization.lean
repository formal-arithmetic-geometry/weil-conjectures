/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData

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
/-- The included finite exceptional counit is the specified intrinsic counit.
Source: blueprint finite reduction of purity, Step 4
(blueprint: lem-route-finite-reduction-exceptional-finite-model-counit-normalization).
Proof: finite-Tor constructibility makes the inverse intrinsic realization bounded
below. Apply AdjunctionNormalized to the published exceptional counit and its
etale-origin witness. Evaluation of fixedHom is the identity by right-adjoint
uniqueness. Naturality of homEquiv along the intrinsic equivalence counit and the
triangle identity identify the transpose with the identity. Transposing back gives
the included finite counit. The bounded-below branch of smoothExceptionalCounit is
exactly this composite. This is one coefficient level, with no reduction equation;
the argument applies to equal indices, zero objects, and empty schemes. -/
theorem finiteExceptionalCounit_normalization
    (L : (FiniteExceptional.domain P.coefficients.l P.extension Y n).FullSubcategory) :
    (FiniteExceptional.domain P.coefficients.l P.extension Y n).ι.map
      ((FiniteExceptional.adjunction P.coefficients.l P.extension P.field
        P.coefficients.different f (@HasCompactification.compactification X Y f
        (hasCompactification_of_finiteType_over_field P.field.k X Y f)) n).counit.app L) =
      (P.finiteReductionSetting (n + 1) (Nat.succ_pos n)).smoothExceptionalCounit
        f L.obj := by sorry

end WeilConjectures.PurityFiniteSetting
