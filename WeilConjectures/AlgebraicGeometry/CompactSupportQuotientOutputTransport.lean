/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportQuotientCocycleData
public import WeilConjectures.AlgebraicGeometry.CompactSupportQuotientNative
import WeilConjectures.AlgebraicGeometry.CompactSupportQuotientOutputIdentity
import WeilConjectures.AlgebraicGeometry.CompactSupportQuotientOutputComposition

/-! # Compact-support images of the input quotient laws

Source: the current blueprint, lem-coef-integral-compact-support.proof.md,
finite-level coefficient comparison; Stacks Tag 03DA
(blueprint: lem-coef-compact-support-quotient-output-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
-- Keep distinct quotient levels from unfolding their valuation-theoretic ideal data.
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.scalarReductionDerivedExtension

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Compact support transports the given quotient identity and cocycle.
Source: blueprint quotient-cocycle naturality argument, Step 6
(blueprint: lem-coef-compact-support-quotient-output-transport).
Proof: apply the abstract naturality calculations to the input equations. For identity
coefficients use the normalized identity square with its actual quotient cast. For
composition use the specified compact-support restriction composition theorem with
the two actual quotient maps. Its invertibility hypothesis holds in every stalk by
mapping the unit l in the base field along the scheme structure morphism. -/
theorem compactSupportQuotient_output_transport
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hid : (∀ n : ℕ, compactSupportQuotientNativeMap l E X n n le_rfl K ≫
      (compactSupportQuotientNativeResId l E X n).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K) = 𝟙 _))
    (hcomp : (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportQuotientNativeMap l E X r m hrm K ≫
          (compactSupportQuotientNativeRestriction l E X r m hrm).map
              (compactSupportQuotientNativeMap l E X m n hmn K) ≫
          (compactSupportQuotientNativeResComp l E X r m n hrm hmn).hom.app
            ((compactSupportQuotientNativeLevel l E X n).obj K) =
        compactSupportQuotientNativeMap l E X r n (hmn.trans hrm) K)) :
    (∀ n : ℕ, ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
        (compactSupportQuotientNativeMap l E X n n le_rfl K) ≫
      (compactSupportQuotientNativeComparison l E c n n le_rfl).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K)) ≫
      (compactSupportQuotientNativeResId l E Y n).hom.app
        ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
          ((compactSupportQuotientNativeLevel l E X n).obj K)) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (r + 1)) c).map
        (compactSupportQuotientNativeMap l E X r m hrm K) ≫
      (compactSupportQuotientNativeComparison l E c r m hrm).hom.app
        ((compactSupportQuotientNativeLevel l E X m).obj K)) ≫
          (compactSupportQuotientNativeRestriction l E Y r m hrm).map
              (((sfAmbientCompactSupportCandidate
                (Padic.coefficientExtensionRing l E (m + 1)) c).map
        (compactSupportQuotientNativeMap l E X m n hmn K) ≫
      (compactSupportQuotientNativeComparison l E c m n hmn).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K))) ≫
          (compactSupportQuotientNativeResComp l E Y r m n hrm hmn).hom.app
            ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
              ((compactSupportQuotientNativeLevel l E X n).obj K)) =
        ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (r + 1)) c).map
        (compactSupportQuotientNativeMap l E X r n (hmn.trans hrm) K) ≫
      (compactSupportQuotientNativeComparison l E c r n (hmn.trans hrm)).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K))) := by
  exact ⟨compactSupportQuotient_output_identity l E c K hid,
    compactSupportQuotient_output_composition l E k _hl c K hcomp⟩

end WeilConjectures
