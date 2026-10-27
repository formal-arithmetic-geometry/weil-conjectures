module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.HenselianFactorizationCriterion
import WeilConjectures.RingTheory.EtaleSectionLiftingOfGabberRoots

/-! # Étale sections modulo the radical of a henselian ideal

Source: Stacks Project, More on Algebra, Tags 09XJ and 09XI, (1) implies (2)
(blueprint: lem-sfb-henselian-pair-radical-etale-section).
-/

@[expose] public section

universe u

namespace Algebra

/-- Every section of an étale algebra modulo the radical of a henselian ideal lifts.
Source: Stacks Project, More on Algebra, Tag 09XJ with `J = I.radical`, and Tag 09XI,
(1) implies (2) (blueprint: lem-sfb-henselian-pair-radical-etale-section).

Proof:
1. If `A` is the zero ring, its unital algebra `B` is zero too, and its unique map to
   `A` is the required lift. Otherwise `A` is nonzero.
2. Put `J = I.radical`. For every finite `A`-algebra `C`, the kernel of
   `C/IC → C/JC` is a nil ideal. A representative is a finite sum of terms `aᵢcᵢ`
   with `aᵢ ∈ J`. Choose positive `nᵢ` with `aᵢ^nᵢ ∈ I`. Expanding the power
   `1 + ∑ᵢ (nᵢ - 1)` puts every term in `IC`; the empty sum is zero.
   By lem-weil-pbc-lift-idempotents-locally-nilpotent, this quotient map gives a
   bijection on idempotents. Compose it with the henselian bijection for `C → C/IC`.
   The finite-algebra idempotent characterization in def-weil-pbc-henselian-terminology
   shows that `(A,J)` is henselian.
3. Apply lem-weil-pbc-henselian-factorization-criterion to `(A,J)`. It gives the
   Jacobson condition and coprime monic factorization lifting. For a Gabber polynomial
   `f = X^n(X-1) + ∑ᵢ aᵢX^i`, `n ≥ 1`, `aᵢ ∈ J`, the reduction has coprime
   factors `X^n` and `X-1`, since `X^n - (X-1)(1+X+⋯+X^(n-1)) = 1`.
   Lift these factors to monic `g,h` with `f = gh` and `h mod J = X-1`.
   Since `A/J` is nonzero, the monic `h` has degree one, so `h = X-α` with
   `α-1 ∈ J`. Evaluation gives `f(α) = 0`, verifying Gabber's root condition.
4. The affine criterion converts the given scheme étaleness to étaleness of the
   `A`-algebra `B`. Apply lem-weil-pbc-gabber-root-criterion-etale-section-lifting
   to `J` and `σbar`, using the Jacobson and root conditions from step 3. It gives
   `σ` whose reduction along `A → A/J` is exactly `σbar`. -/
theorem exists_etale_section_lift_mod_radical_of_henselianRing
    (A B : Type u) [CommRing A] [CommRing B] (I : Ideal A) [HenselianRing A I]
    [Algebra A B]
    [AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (σbar : B →ₐ[A] A ⧸ I.radical) :
    ∃ σ : B →ₐ[A] A, (Ideal.Quotient.mkₐ A I.radical).comp σ = σbar := by
  sorry

end Algebra
