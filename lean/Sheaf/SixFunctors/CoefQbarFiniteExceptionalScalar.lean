/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore

/-! Scalar compatibility for finite exceptional comparison data.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-formula-scalar)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Scalar compatibility for normalized finite exceptional comparisons.
Source: thm-coef-qbar-verdier, retained proof step 9.
(blueprint: lem-coef-qbar-finite-exceptional-formula-scalar)

Proof: apply the scalar mate identity for rational exceptional identifications to the
specified finite duality extensions. Substitute the normalized BX and BY duality squares
and the published pullback scalar square; naturality and inverse cancellation yield the
 displayed inclusion-transition equation, including identity extensions. -/
theorem finite_exceptional_formula_scalar
    (BX : Duality D l hl Ω X) (BY : Duality D l hl Ω Y)
    (c : Compactification f)
    (S : ConstructibleExceptionalCoefficients.System l (AuxiliaryClosure.{u} l) D hl (f := f))
    (t : FiniteExceptionalFormulaCore D l hl Ω X f BX BY c S) :
    ∀ (E L : Index l Ω) (h : E ≤ L) (M : Stage l Ω Y E),
      (inclusion L).map ((finiteRightScalar D l hl Ω X f c S E L h).hom.app M) ≫
        (t.comparison L).hom.app ((transition l Ω Y E L h).obj M) =
      (inclusionTransition l Ω X E L h).hom.app
          ((finiteRight D l hl Ω X f c S E).obj M) ≫
        (t.comparison E).hom.app M ≫
        (specifiedExceptionalFormulaCore D l hl Ω X f BX BY).map
          ((inclusionTransition l Ω Y E L h).inv.app M) := by sorry

end WeilConjectures.CoefQbarVerdier
