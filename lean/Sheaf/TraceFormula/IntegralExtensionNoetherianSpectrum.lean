module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.NoetherianSpace

/-!
# Noetherian spectrum of a finite fraction-field integral closure

Source: W. Heinzer, *Minimal primes of ideals and integral ring extensions*, Theorem 2,
Proc. Amer. Math. Soc. 40 (1973), 370--372, printed pp. 371--372,
specialized to the integral closure in a finite fraction-field extension
(blueprint: lem-trf-integral-extension-noetherian-spectrum).
-/

@[expose] public section

universe u v

open TopologicalSpace

/-- Let `A` be a Noetherian domain, let `L` be a finite field extension of its fraction
field, and let `B` be the integral closure of `A` in `L`.  Then `Spec B` is a Noetherian
space.  The algebra structure from `A` to `L` is required to factor through the canonical
fraction field by the scalar-tower assumption.

Source: Heinzer, Theorem 2, printed pp. 371--372
(blueprint: lem-trf-integral-extension-noetherian-spectrum).

Proof outline recorded for the postponed proof.  Induct on prime ideals of the
Noetherian domain `A`.  For a prime `p`, reduce to `R = A ⧸ p` and consider an
integral subring `C` of a finite extension of `Frac R`.  For a nonzero prime `Q`
of the integral closure `D`, a least-degree monic equation for a nonzero element
of `Q` has nonzero constant term, so `Q ∩ R` gives a strictly larger prime of
`A`.  The finite-residue-field-degree theorem and induction make `Spec (D ⧸ Q)`
Noetherian, hence each `V(Q)` is Noetherian.  Minimal-prime decompositions of
principal ideals then make every proper closed subset of `Spec D` Noetherian,
and therefore `Spec D` itself is Noetherian.  The integral inclusion `C ⊆ D`
gives a continuous surjection on spectra, so the descending-chain condition
 descends to `Spec C`.  Applying this at `p = 0`, `C = D = integralClosure A L`,
proves the stated result; the scalar-tower instance expresses the composite
`A → FractionRing A → L`, and `L = FractionRing A` is included.
-/
theorem integralExtension_noetherianSpectrum
    (A : Type u) (L : Type v) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] :
    NoetherianSpace (PrimeSpectrum (integralClosure A L)) := by
  sorry

end
