/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportQuotientNative

/-! # Original presentation of the input quotient laws

Source: the current blueprint finite-level coefficient comparison
(blueprint: lem-coef-compact-support-quotient-raw-input).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.scalarReductionDerivedExtension WeilConjectures.compactSupportReductionMap
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The input laws in the original scalar-reduction presentation.
Source: the specified quotient unit and coefficient comparisons
(blueprint: lem-coef-compact-support-quotient-raw-input).
Proof: the native wrappers have exactly the original functors and arrows as values. -/
theorem compactSupportQuotient_raw_input
    (X : Scheme.{u}) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hi :
    (∀ n : ℕ, compactSupportQuotientNativeMap l E X n n le_rfl K ≫
      (compactSupportQuotientNativeResId l E X n).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportQuotientNativeMap l E X r m hrm K ≫
          (compactSupportQuotientNativeRestriction l E X r m hrm).map
              (compactSupportQuotientNativeMap l E X m n hmn K) ≫
          (compactSupportQuotientNativeResComp l E X r m n hrm hmn).hom.app
            ((compactSupportQuotientNativeLevel l E X n).obj K) =
        compactSupportQuotientNativeMap l E X r n (hmn.trans hrm) K)) :
    (∀ n : ℕ, compactSupportReductionMap l E X n n le_rfl K ≫
      (compactSupportQuotientResId l E X n).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportReductionMap l E X r m hrm K ≫
          (proEtaleCoefficientRestrictScalars X
            (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory.map
              (compactSupportReductionMap l E X m n hmn K) ≫
          (compactSupportQuotientResComp l E X r m n hrm hmn).hom.app
            ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) =
    compactSupportReductionMap l E X r n (hmn.trans hrm) K) := by
  sorry

end WeilConjectures
