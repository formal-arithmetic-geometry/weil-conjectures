/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptional
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteReductionExceptionalQIdentification

/-! # The finite exceptional mate in purity coordinates

Source: blueprint finite reduction of purity, Step 2, and
lem-coef-finite-exceptional, the counit identity.
(blueprint: lem-pur-finite-reduction-exceptional-model-counit).

Positive coefficient exponents are written as n+1 to use the existing finite
exceptional adjunction. Its specified mate supplies the comparison isomorphism;
the remaining statement identifies its transpose in the purity realization.
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
/-- In the purity realization, the specified finite exceptional mate transposes to
scalar extension of the specified exceptional counit. This statement concerns the
normalization of an already constructed isomorphism, rather than its invertibility.

Source: current blueprint thm-pur-finite-reduction-of-purity.proof.md, Step 2,
exceptional coefficient compatibility; lem-coef-finite-exceptional.proof.md,
last paragraph, counit identity
(blueprint: lem-pur-finite-reduction-exceptional-model-counit).

Proof: apply the third clause of finiteReductionExceptionalQIdentification to the
full-subcategory object represented by K and hK. Unfold the scalar-adjunct
compact-support comparison and the finite model isomorphism hom; their morphisms
are definitionally the ones displayed here. The bridge theorem includes equal
indices, zero objects and empty schemes without a flatness hypothesis. -/
theorem finiteReductionExceptionalFiniteModel_counit
    (K : Scheme.proEtaleDerivedCategory Y (P.finiteReductionSetting (n + 1)
      (Nat.succ_pos n)).Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y K) :
    let N := P.finiteReductionSetting (n + 1) (Nat.succ_pos n)
    let M := P.finiteReductionSetting (m + 1) (Nat.succ_pos m)
    let red := N.finiteReduction (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h)
    let adj := N.finiteReductionAdjunction (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h)
    let c := @HasCompactification.compactification X Y f
      (hasCompactification_of_finiteType_over_field P.field.k X Y f)
    ((adj Y).homEquiv _ _).symm
        ((N.smoothCompactSupport f).map
            ((adj X).unit.app ((N.compositionExceptional f).obj K)) ≫
          (Scheme.sfCompactSupportRestriction c
            (N.finiteReductionRingHom (m + 1) (Nat.succ_pos m)
              (Nat.succ_le_succ h))).hom.app
            ((red X).obj ((N.compositionExceptional f).obj K))) ≫
      (M.smoothCompactSupport f).map
        (P.finiteReductionExceptionalFiniteModel n m h f K hK).hom ≫
      M.smoothExceptionalCounit f ((red Y).obj K) =
    (red Y).map (N.smoothExceptionalCounit f K) := by
  let L : (FiniteExceptional.domain P.coefficients.l P.extension Y n).FullSubcategory :=
    ⟨K, hK⟩
  have hc := (finiteReductionExceptionalQIdentification P.field P.coefficients
    P.extension m n h f).2.2.1 L
  exact hc

end WeilConjectures.PurityFiniteSetting
