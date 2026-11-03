/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeTowerLimitData
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-! # Integral criterion in the smooth-purity native coefficient presentation

The two continuous integer-ring presentations use the same spectral topology. Equality
of their ring objects identifies the native completion and first-residue condition.
No completed-section constructibility predicate enters this comparison.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.NativeTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The canonical uniformizer-completion condition and constructible first reduction.
The witness is determined by heterogeneous equality with the given native object. -/
def CriterionCondition (K : Integral l E T) : Prop :=
  ∃ K' : DerivedCategory (AdicCompletion.Modules l E T),
    HEq K K' ∧ IsDerivedComplete l E T K' ∧
      constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) T
        ((AdicCompletion.derivedReduction l E T 0).obj K')

private theorem criterionWithPoint [IsNoetherian T]
    (A : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hA : Mon.mk (DerivedNakayama.integerRing l E) = A) [IsCommMonObj A.X]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj A.X T))) :
    constantModelBoundedConstructible A.X T K ↔
      ∃ K' : DerivedCategory (AdicCompletion.Modules l E T),
        HEq K K' ∧ IsDerivedComplete l E T K' ∧
          constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) T
            ((AdicCompletion.derivedReduction l E T 0).obj K') := by
  cases hA
  constructor
  · intro hK
    exact ⟨K, HEq.rfl, ((condensed_integral_criterion l E T K).out 0 1).mp hK⟩
  · rintro ⟨K', h, hK⟩
    cases eq_of_heq h
    exact ((condensed_integral_criterion l E T K).out 1 0).mp hK

/-- The Noetherian integral criterion, stated for the actual smooth-purity condensed
integer ring. Bounded constructibility has no completeness condition in its definition.
Source: current blueprint integral criterion, (1) iff (2)
(blueprint: lem-sp-native-tower-integral-criterion).

Proof: the spectral absolute value and spectral norm give equal metrics after using
norm(-x)=norm(x), hence equal induced topologies on O_E. Their continuous-function
ring sheaves and ring-object structures are therefore equal. After this equality,
heterogeneous equality of derived objects is ordinary equality. Apply the existing
condensed integral criterion in both directions. -/
theorem criterion [IsNoetherian T] (K : Integral l E T) :
    constantModelBoundedConstructible (spIntegralCondensed l E) T K ↔
      CriterionCondition l E T K := by
  exact criterionWithPoint l E T (sfbCondensedIntegers l E) (integralPointMon_eq l E) K

end AlgebraicGeometry.ProEtale.NativeTower
