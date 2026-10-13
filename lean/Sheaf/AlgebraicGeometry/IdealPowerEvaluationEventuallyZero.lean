/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk

/-! # IdealPowerEvaluationEventuallyZero

Source: Stacks Project, Properties, Lemma 01PQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A homomorphism from an ideal power that evaluates to zero on the complement
vanishes after restriction to a sufficiently high power.

Proof: Choose a finite affine cover of the quasi-compact scheme. On one affine member
write the ideal as a finitely generated ideal J = (f_1,...,f_t) and F as the sheaf of M.
The affine tilde/Gamma adjunction identifies the homomorphism with a linear map
J^n -> M. On D(f_i), evaluation at one is phi(f_i^n)/f_i^n, by linearity and naturality.
Its vanishing means f_i^k phi(f_i^n) = 0 for some k. Take one k for all generators.
Then phi kills every f_i^(n+k). Any monomial of degree t*(n+k-1)+1 contains one of
these powers, so phi vanishes on a sufficiently high power of J. For J = 0 use a
positive power directly, and enlarge all exponents to be at least n. Take the maximum
of the exponents from the finite affine cover. The specified r is the power inclusion
by its equality over the structure sheaf and monicity of the power inclusions.
The resulting restricted homomorphism vanishes on the cover, hence vanishes globally
by sheaf uniqueness. The case n = 0 uses the same calculation with f_i^0 = 1.

Source: Stacks Project, Properties, Lemma 01PQ and its reduction to Lemma 01PM.
(blueprint: lem-weil-pbc-ideal-power-evaluation-eventually-zero). -/
theorem ideal_power_evaluation_eventually_zero
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2) :
    ∀ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ F),
      φ.app U (one n) = 0 →
      ∃ (m : ℕ) (h : n ≤ m), r n m h ≫ φ = 0 := by sorry

end AlgebraicGeometry.Scheme
