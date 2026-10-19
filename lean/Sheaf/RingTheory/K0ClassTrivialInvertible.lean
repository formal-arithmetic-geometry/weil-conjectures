module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Sheaf.RingTheory.FiniteProjectiveK0
import Sheaf.RingTheory.K0DeterminantMap

/-!
# Triviality from a multiple of the ring class in `K₀`

Source: Stacks Project, `literature/stacks-project/more-algebra.tex`, Lemma 0AFX and
Tag 0AFZ (blueprint: lem-trf-k0-class-trivial-invertible).

This stage-2 statement is delivered by group Q64.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module.FiniteProjectiveK0

/-- A finite projective module that is locally free of rank one and has class a multiple
of the ring class is isomorphic to the ring. Source: Stacks Project, Lemma 0AFX and
Tag 0AFZ (blueprint: lem-trf-k0-class-trivial-invertible). The proof applies the
 determinant homomorphism from `lem-trf-k0-determinant-map` to the stated K₀ equality;
that homomorphism sends the class of a rank-one module to its Picard class and the
class of the ring to the identity, so equality of Picard classes gives the displayed
linear equivalence. -/
theorem class_trivial_invertible
    (S : Type u) [CommRing S]
    (L : Type v) [AddCommGroup L] [Module S L]
    [Module.Finite S L] [Module.Projective S L]
    (hlocal : ∀ q : PrimeSpectrum S,
      Module.Free (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl L) ∧
      Module.rank (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl L) = 1)
    (n : ℤ)
    (hclass : FiniteProjectiveK0.mk S L = n • FiniteProjectiveK0.mk S S) :
    Nonempty (L ≃ₗ[S] S) := by
  sorry

end Module.FiniteProjectiveK0

end
