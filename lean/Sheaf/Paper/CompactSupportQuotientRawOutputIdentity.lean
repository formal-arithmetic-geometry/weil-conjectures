/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportQuotientNative
import Sheaf.Paper.CompactSupportQuotientOutputIdentity
import all Sheaf.Paper.CompactSupportCoefficientPresentation

/-! # Original presentation of the output quotient identity

Source: the current blueprint finite-level coefficient comparison
(blueprint: lem-coef-compact-support-quotient-raw-output-identity).
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

/-- The transported identity with exactly the original compact-support expressions.
Source: identity coefficient normalization and functoriality
(blueprint: lem-coef-compact-support-quotient-raw-output-identity).
Proof: rewrite the intrinsic functor to its identical ambient presentation, and
apply the proved output identity. Every quotient wrapper retains its actual value. -/
theorem compactSupportQuotient_raw_output_identity
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hid :
    (∀ n : ℕ, compactSupportQuotientNativeMap l E X n n le_rfl K ≫
      (compactSupportQuotientNativeResId l E X n).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K) = 𝟙 _)) :
    (∀ n : ℕ, ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
        (compactSupportReductionMap l E X n n le_rfl K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E n n le_rfl)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) ≫
      (compactSupportQuotientResId l E Y n).hom.app
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) = 𝟙 _) := by
  sorry

end WeilConjectures
