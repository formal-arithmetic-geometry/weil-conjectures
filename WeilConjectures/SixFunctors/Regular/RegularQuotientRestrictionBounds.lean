/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.CondensedFiniteQuotientRestrictionConstructible
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.CondensedRegularQuotientHomologySequence
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.CondensedRegularQuotientTorRestriction
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedScalarExtensionTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteUniverseConstructibleKernels

/-! # Uniform constructibility and Tor bounds for finite quotient restriction

Source: Tags 06YY, 07A6, 0A70, 0BZE, 0BZH and 08FZ; Zheng Lemma 5.22 and Proposition 5.26.
(blueprint: lem-sf-regular-quotient-restriction-bounds). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem reductionBounds_of_finiteTor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) T)))
    (hL : _root_.DerivedCategory.finiteTorAmplitude _ L)
    (hcons : ∀ m : ℕ,
      boundedConstructible (condensedRingObj (IntegralQuotient.finite l E m) T)
        ((IntegralQuotient.scalar l E T m).obj L)) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ m : ℕ,
      boundedConstructible (condensedRingObj (IntegralQuotient.finite l E m) T)
          ((IntegralQuotient.scalar l E T m).obj L) ∧
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((IntegralQuotient.scalar l E T m).obj L) ∧
        _root_.DerivedCategory.torAmplitudeIn
          (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj (IntegralQuotient.finite l E m) T)) a b
          ((IntegralQuotient.scalar l E T m).obj L) := by
  obtain ⟨a, b, hab⟩ := hL
  refine ⟨min a b, b, min_le_right _ _, fun m ↦ ?_⟩
  have htor := CondensedRing.torAmplitudeIn_scalarExtension
    (IntegralQuotient.reduction l E m) T
      (hab.mono (min_le_left a b) (le_refl b))
  exact ⟨hcons m, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn htor,
    htor⟩

/-- Restriction of a finite-Tor constructible quotient complex has constructible finite
reductions with one cohomological and Tor interval, independent of the reduction level.
Source: Zheng, Lemma 5.22 and Proposition 5.26; Stacks Project, Tags 06YY, 07A6 and 08FZ.
(blueprint: lem-sf-regular-quotient-restriction-bounds).

Proof: choose a bounded flat representative in a Tor interval [a,b] for K. Each flat
module over the fixed quotient B=A/(pi^(n+1)) has flat dimension at most one over A:
tensor the length-one free resolution of B with it, or use the change-of-rings Tor
spectral sequence and B-flatness. The bounded representative therefore has A-Tor
amplitude [a-1,b]. Derived tensor with any quotient A/(pi^(m+1)) retains this same
interval over the target quotient, by derived tensor associativity. Tensoring with
the unit gives the same cohomological bound, for every m at once. To check
constructibility, use a finite locally closed stratification trivializing the bounded
constructible finite-Tor B-complex locally by bounded finite projective B-complexes.
Resolve each finite projective term over A using the regular principal resolution,
and tensor this finite model with A/(pi^(m+1)). Its cohomology is finite over the
finite target ring, and the local constant models give constructible cohomology on
each of the same strata. The normalized scalar-extension counit identifies these
computations with the prescribed scalarReductionDerivedExtension, and exact scalar
restriction identifies their input with scalarReductionDerivedRestriction. Isomorphism
invariance transfers both predicates to those functors. Enlarge the two finite bounds
if necessary to obtain ordered a,b common to cohomology and Tor. Positivity of n+1
and m+1 includes level zero; zero complexes and empty strata satisfy the same bounds.
This statement does not assert derived completeness or any adjunction. -/
theorem scalarReductionDerivedRestriction_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionTarget.{u, u} l E T n))
    (hK : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ m : ℕ,
      intrinsicFiniteTorsionConstructible l E (m + 1) (Nat.succ_pos m) T
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ∧
        proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ⊆ Set.Icc a b ∧
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (m + 1))
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) a b := by
  sorry

/-- Restriction of a finite-Tor constructible quotient complex has constructible finite
reductions with one cohomological and Tor interval, independent of the reduction level.
Source: Zheng, Lemma 5.22 and Proposition 5.26; Stacks Project, Tags 06YY, 07A6 and 08FZ.
(blueprint: lem-sf-regular-quotient-restriction-bounds).

Proof: choose a bounded flat representative in a Tor interval [a,b] for K. Each flat
module over the fixed quotient B=A/(pi^(n+1)) has flat dimension at most one over A:
tensor the length-one free resolution of B with it, or use the change-of-rings Tor
spectral sequence and B-flatness. The bounded representative therefore has A-Tor
amplitude [a-1,b]. Derived tensor with any quotient A/(pi^(m+1)) retains this same
interval over the target quotient, by derived tensor associativity. Tensoring with
the unit gives the same cohomological bound, for every m at once. To check
constructibility, use a finite locally closed stratification trivializing the bounded
constructible finite-Tor B-complex locally by bounded finite projective B-complexes.
Resolve each finite projective term over A using the regular principal resolution,
and tensor this finite model with A/(pi^(m+1)). Its cohomology is finite over the
finite target ring, and the local constant models give constructible cohomology on
each of the same strata. The normalized scalar-extension counit identifies these
computations with the prescribed scalarReductionDerivedExtension, and exact scalar
restriction identifies their input with scalarReductionDerivedRestriction. Isomorphism
invariance transfers both predicates to those functors. Enlarge the two finite bounds
if necessary to obtain ordered a,b common to cohomology and Tor. Positivity of n+1
and m+1 includes level zero; zero complexes and empty strata satisfy the same bounds.
This statement does not assert derived completeness or any adjunction. -/
theorem scalarReductionDerivedRestriction_bounds_legacy
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionTarget.{u, u} l E T n))
    (hK : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ m : ℕ,
      intrinsicFiniteTorsionConstructible l E (m + 1) (Nat.succ_pos m) T
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ∧
        proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ⊆ Set.Icc a b ∧
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (m + 1))
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) a b := by
  sorry

end WeilConjectures
