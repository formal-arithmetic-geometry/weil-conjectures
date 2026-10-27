/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.DerivedPullbackTensorHom
/-! Rational unit coherence for the specified Hom comparison.
(blueprint: lem-zl-specified-hom-scalar-evaluation). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
/-- The identity scalar comparison satisfies the Hom unit equation after rationalization.
Source: blueprint common-stage paragraph (blueprint: lem-zl-specified-hom-scalar-evaluation).
Proof: localize the integral unit equation and identify each normalized component. -/
theorem specifiedHomScalarRational_unit (X : Scheme.{u})
    (P : (constructibleRationalHomPairs l E X).FullSubcategory) :
    ((rationalHomScalarComparison l E E (AlgHom.id ℚ_[l] E) X P).hom ≫
      (rationalDerivedInternalHom l E X).map
        (ObjectProperty.homMk
          (X := rationalHomScalarPair l E E (AlgHom.id ℚ_[l] E) X P) (Y := P)
          (Prod.mkHom
            (((sfRationalScalarUnit l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))).inv.app P.obj.1.unop).op)
            ((sfRationalScalarUnit l E X 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app P.obj.2))) =
      (sfRationalScalarUnit l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
          ((rationalDerivedInternalHom l E X).obj P)) := by
  sorry
end WeilConjectures
