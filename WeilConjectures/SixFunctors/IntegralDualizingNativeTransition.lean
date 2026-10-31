/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportNativeSystemTransition
public import WeilConjectures.SixFunctors.FiniteDualizingData
import all WeilConjectures.AlgebraicGeometry.CompactSupportFiniteAction

/-! # The native support transition in normalized quotient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})

/-- The specified finite restriction and the native coefficient restriction agree.
Source: Stacks 03DA, 0941 (blueprint: lem-coef-system-native-transition). -/
def integralDualizingNativeRestriction {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E W h ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory :=
  by
    letI := proEtaleCoefficientRestrictScalars_preservesFiniteLimits W
      (compactSupportLevelQuotient l E m n h)
    letI := proEtaleCoefficientRestrictScalars_preservesFiniteColimits W
      (compactSupportLevelQuotient l E m n h)
    exact Functor.mapDerivedCategoryNatIso
      (eqToIso (compactSupportModuleRes_eq l E W h))

/-- The uniquely specified sequence transition is the native horizontal transition.
Source: Stacks 0941; finite counit compatibility, proof step 4.
(blueprint: lem-coef-system-native-transition).
Proof: the two ordinary maps have the same horizontal restriction on every section.
Their exact localizations and composition comparisons are therefore equal. -/
theorem integralDualizingNativeTransition_eq {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceDerivedTransition l E W h ≫
      Functor.whiskerLeft (coefficientSequenceDerivedEvaluation l E W n)
        (integralDualizingNativeRestriction l E W h).hom =
      compactSupportCoefficientTransition l E W h := by
  exact derivedTransition_direct l E W h


end WeilConjectures
