/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernClasses
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.Modules.LocalSectionOfEpi
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.AlgebraicGeometry.Modules.HomSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientGeometry
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleQuotientEpi
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleSymmetricAlgebraIso
public import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjSectionCompatibility
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
public import WeilConjectures.AlgebraicGeometry.KummerAdditivity
import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ClosedSupportedCupVanishing
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality

/-!
# The Chern polynomial of a bundle filtered by line quotients

Source: Stacks Project, Tags 0FI5 and 0FI7, `proposition-chern-class` and
`lemma-splitting-principle`; blueprint localized-top-Chern Step 4 (L4)
(blueprint: lem-pur-chern-flag-formula).

The polynomial identity is stated coefficient by coefficient in H^(2i)(S,A(i)).
`ordinaryFiniteFlagProductCoefficient` expands the product of the factors 1+x_j u
by the usual coefficient recurrence. Its multiplication is the existing full-support
cup product with the actual Kummer class of the quotient line. Thus no new cohomology
ring or arbitrary multiplication is assumed. `ordinaryFiniteFlagTopProduct` is the
ordered cup product of all the roots, with empty product the coefficient unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary etale Kummer class of the specified invertible module; its exact
comparison inverse image is x=c_(1,A)(M) on the small pro-etale site. The exponent
ell^level works at every positive coefficient level, with no divisibility condition.
Source: Stacks Tags 0FI5, 03PL; lem-pur-kummer-additivity
(blueprint: lem-pur-chern-flag-formula). -/
def ordinaryFiniteFlagRoot (P : PurityFiniteSetting.{u}) {S : Scheme.{u}}
    (a : S ⟶ Spec (.of P.field.k)) (M : S.Modules) (hM : M.IsInvertible) :
    Etale.ordinaryFiniteUnit P.Coefficient S ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧ :=
  letI := hM
  Etale.kummerFirstChern P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates
    S (P.diagonalExponent_isUnit a) (Scheme.Pic.ofIsInvertible M)

/-- The coefficient of u^i in the product of 1+x_j u, in the homogeneous group
H^(2i)(S,A(i)). Append the last factor: b'_0=1 and b'_(i+1)=b_(i+1)+b_i cup x_last.
For zero factors the coefficient sequence is (1,0,0,...). Cup multiplication uses
ordinaryFiniteHyperplaneStep, which applies exact comparison to the given etale root.
Source: Stacks Tag 0FI5, iterated line-subbundle formula
(blueprint: lem-pur-chern-flag-formula). -/
def ordinaryFiniteFlagProductCoefficient (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    (r : ℕ) → (Fin r →
      (Etale.ordinaryFiniteUnit P.Coefficient S ⟶
        (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧)) →
      (i : ℕ) → ordinaryFiniteCohomology P S i
  | 0, _, 0 => P.ordinaryFiniteCohomologyOne S
  | 0, _, _ + 1 => 0
  | _ + 1, _, 0 => P.ordinaryFiniteCohomologyOne S
  | r + 1, x, i + 1 =>
      P.ordinaryFiniteFlagProductCoefficient S r (fun j => x j.castSucc) (i + 1) +
        P.ordinaryFiniteHyperplaneStep S (x (Fin.last r)) i
          (P.ordinaryFiniteFlagProductCoefficient S r (fun j => x j.castSucc) i)

/-- The cup product x_0 cup ... cup x_(r-1), beginning with the coefficient unit.
Each new root is multiplied on the right, with the ordered shifted Tate comparison
already used in the ordinary Chern construction. In rank zero this is 1 in H^0(S,A).
Source: Stacks Tag 0FI5, top coefficient of the product of linear factors
(blueprint: lem-pur-chern-flag-formula). -/
def ordinaryFiniteFlagTopProduct (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :
    (r : ℕ) → (Fin r →
      (Etale.ordinaryFiniteUnit P.Coefficient S ⟶
        (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧)) →
      ordinaryFiniteCohomology P S r
  | 0, _ => P.ordinaryFiniteCohomologyOne S
  | r + 1, x => P.ordinaryFiniteHyperplaneStep S (x (Fin.last r)) r
      (P.ordinaryFiniteFlagTopProduct S r (fun j => x j.castSucc))

end WeilConjectures.PurityFiniteSetting
