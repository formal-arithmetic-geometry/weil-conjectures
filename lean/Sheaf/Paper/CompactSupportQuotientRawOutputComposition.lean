/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportQuotientNative
import Sheaf.Paper.CompactSupportQuotientOutputTransport
import all Sheaf.Paper.CompactSupportCoefficientPresentation

/-! # Original presentation of the output quotient cocycle

Source: the current blueprint finite-level coefficient comparison
(blueprint: lem-coef-compact-support-quotient-raw-output-composition).
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

/-- The transported composition with exactly the original compact-support expressions.
Source: the normalized coefficient square and naturality
(blueprint: lem-coef-compact-support-quotient-raw-output-composition).
Proof: obtain the transported composition from the proved pair of output laws.
Rewrite each intrinsic functor to the identical ambient presentation and specialize
that composition to the three levels. No quotient map or equality cast changes. -/
theorem compactSupportQuotient_raw_output_composition
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
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
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (r + 1))).map
        (compactSupportReductionMap l E X r m hrm K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E r m hrm)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X m).obj K)) ≫
          (proEtaleCoefficientRestrictScalars Y
            (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory.map
              (((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
        (compactSupportReductionMap l E X m n hmn K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n hmn)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))) ≫
          (compactSupportQuotientResComp l E Y r m n hrm hmn).hom.app
            ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
              ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) =
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (r + 1))).map
        (compactSupportReductionMap l E X r n (hmn.trans hrm) K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E r n (hmn.trans hrm))).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))) := by
  sorry

end WeilConjectures
