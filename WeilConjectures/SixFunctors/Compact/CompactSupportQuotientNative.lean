/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleData

/-! # Native constant-coefficient types for integral quotient reductions

We present the integral quotient reductions, their restrictions and comparisons with canonical
constant-coefficient source and target types.

## References

* [Stacks, Tags 03DA, 03DI, 06YY]
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing integral reduction with its canonical constant-coefficient codomain. -/
def compactSupportQuotientNativeLevel (W : Scheme.{u}) (n : ℕ) :
    DerivedCategory (scalarReductionSource.{u, u} l E W) ⥤
      proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1)) :=
  scalarReductionDerivedExtension.{u, u} l E W n

/-- Quotient restriction with its canonical constant-coefficient source and target. -/
def compactSupportQuotientNativeRestriction (W : Scheme.{u})
    (m n : ℕ) (h : n ≤ m) :
    proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1)) ⥤
      proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (m + 1)) :=
  compactSupportCoefficientRestriction W (compactSupportLevelQuotient l E m n h)

/-- The original identity comparison in canonical quotient restriction types. -/
def compactSupportQuotientNativeResId (W : Scheme.{u}) (n : ℕ) :
    compactSupportQuotientNativeRestriction l E W n n le_rfl ≅ 𝟭 _ :=
  compactSupportQuotientResId l E W n

/-- The original composition comparison in canonical quotient restriction types. -/
def compactSupportQuotientNativeResComp (W : Scheme.{u})
    (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m) :
    compactSupportQuotientNativeRestriction l E W m n hmn ⋙
        compactSupportQuotientNativeRestriction l E W r m hrm ≅
      compactSupportQuotientNativeRestriction l E W r n (hmn.trans hrm) :=
  compactSupportQuotientResComp l E W r m n hrm hmn

/-- The original compact-support comparison in canonical quotient restriction types. -/
def compactSupportQuotientNativeComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (m n : ℕ) (h : n ≤ m) :
    compactSupportQuotientNativeRestriction l E X m n h ⋙
        sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (m + 1)) c ≅
      sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c ⋙
        compactSupportQuotientNativeRestriction l E Y m n h :=
  compactSupportCoefficientComparison c (compactSupportLevelQuotient l E m n h)

/-- The published normalized quotient arrow in the native constant-ring presentation. -/
def compactSupportQuotientNativeMap (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) :
    (compactSupportQuotientNativeLevel l E W m).obj K ⟶
      (compactSupportQuotientNativeRestriction l E W m n h).obj
          ((compactSupportQuotientNativeLevel l E W n).obj K) :=
  compactSupportReductionMap l E W m n h K

end WeilConjectures
