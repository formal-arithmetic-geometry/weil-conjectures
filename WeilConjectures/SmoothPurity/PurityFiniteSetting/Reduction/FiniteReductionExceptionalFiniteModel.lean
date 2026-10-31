/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptional

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
/-- The existing finite exceptional coefficient isomorphism, with the full inclusion
forgetting only the finite-Tor membership proof. No endpoint isomorphism is chosen.
Source: lem-coef-finite-exceptional, canonical b and its invertibility
(blueprint: lem-pur-finite-reduction-exceptional-model-counit). -/
def finiteReductionExceptionalFiniteModel
    (K : Scheme.proEtaleDerivedCategory Y (P.finiteReductionSetting (n + 1)
      (Nat.succ_pos n)).Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y K) :
    let N := P.finiteReductionSetting (n + 1) (Nat.succ_pos n)
    let M := P.finiteReductionSetting (m + 1) (Nat.succ_pos m)
    (N.finiteReduction (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) X).obj
        ((N.compositionExceptional f).obj K) ≅
      (M.compositionExceptional f).obj
        ((N.finiteReduction (m + 1) (Nat.succ_pos m) (Nat.succ_le_succ h) Y).obj K) := by
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  let c := HasCompactification.compactification f
  let L : (FiniteExceptional.domain P.coefficients.l P.extension Y n).FullSubcategory := ⟨K, hK⟩
  have hb := (FiniteExceptional.finite_exceptional P.coefficients.l P.extension
    P.field P.coefficients.different f c).2.1 h
  let e := (FiniteExceptional.domain P.coefficients.l P.extension X m).ι.mapIso
    ((asIso (FiniteExceptional.b P.coefficients.l P.extension
      P.field P.coefficients.different f c h)).app L)
  exact e

/-- In the purity realization, the specified finite exceptional mate transposes to
scalar extension of the specified exceptional counit. This statement concerns the
normalization of an already constructed isomorphism, rather than its invertibility.

Source: current blueprint thm-pur-finite-reduction-of-purity.proof.md, Step 2,
exceptional coefficient compatibility; lem-coef-finite-exceptional.proof.md,
last paragraph, counit identity
(blueprint: lem-pur-finite-reduction-exceptional-model-counit).

Proof: use the final counit equation of FiniteExceptional.finite_exceptional for
n -> m and the full-subcategory object represented by K. Apply the full inclusion.
Its scalar restrictions have unchanged underlying morphisms, so the right side
becomes scalar extension of the original counit. The normalization in
FiniteExceptional.adjunction_existsUnique identifies each finite counit with the
published bounded-etale-origin counit: expand its fixedHom chain, use the intrinsic
realization unit/counit identities, and cancel fixedExceptionalIso by right-adjoint
uniqueness. The finite-Tor predicate makes K bounded constructible, hence its inverse
realization bounded below; thus smoothExceptionalCounit uses its nonzero branch.
For q, expand FiniteExceptional.supportMap. The finiteImageIso factors transport
the coefficient-ring open adjunction to sfIntrinsicOpenAdjunction. Both open
restriction comparisons preserve that adjunction unit; their equality follows by
left-adjoint uniqueness. The proper restriction comparisons agree on K-injective
representatives by their prescribed derived direct-image normalization. Pasting
these two squares identifies the transported q with the scalar adjunct displayed
below. Substitute these identifications in the included finite counit equation.
This gives the claimed equality. The argument includes m=n and the zero object;
all unit, counit and section normalizations also apply on empty schemes. No
flatness or finite projective dimension of the quotient is used. -/
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
  sorry

end WeilConjectures.PurityFiniteSetting
