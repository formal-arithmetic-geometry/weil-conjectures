/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Sheaf.Algebra.Module.DegreeZeroFractions

/-!
# Detection of homogeneous degree on a Proj basic open

Source: Stacks Project, Tags 01MN and 01M7.
-/

@[expose] public section

universe v
open CategoryTheory Opposite LocalizedModule
namespace AlgebraicGeometry.Proj

/-- An ordinary fraction whose values at all homogeneous primes have degree k itself has
an equal-degree numerator and denominator for the shifted grading.
Source: Stacks Project, Tag 01MN, homogeneous localization of a graded module,
and Tag 01M7, Lemma 27.8.4 (injectivity on a basic open).
(blueprint: lem-sc-proj-twist-degree-detection)

Proof: represent z by a/f^r and decompose a into its finitely many homogeneous
components. This gives components of degrees i-r*b. At a homogeneous prime p away from f,
localize first at just the homogeneous elements outside p. This localization is Z-graded.
It injects into A_p: for an ordinary denominator outside p, some homogeneous component
is outside p and becomes a unit. The grading map sends that denominator to a Laurent
polynomial with a unit coefficient. McCoy's criterion makes this polynomial regular.
The grading map is multiplicative and injective (evaluation at 1 is a left inverse),
so the denominator acts injectively on the graded localization. Further localization
at all ordinary denominators outside p is consequently injective. The degree-k fraction
supplied by hz is already in this graded localization. Equality there and independence
of homogeneous components force every component of z of degree different from k to vanish.
For such a numerator component a_i, consider I = {x in A | some power of f kills x*a_i}.
If a_i/f^r is nonzero, I is proper, homogeneous, and disjoint from powers of f. Choose
an ordinary prime containing I and avoiding f, then take its homogeneous core; the core
is prime, still contains I, and avoids f. It is relevant because f has positive degree.
Vanishing of the component at this point supplies a homogeneous denominator outside the
core killing a_i after multiplication by a power of f. That denominator belongs to I,
a contradiction. Thus only the degree-k component survives globally. Increase r if
necessary until k+r*b is nonnegative, multiplying the numerator by the same power of f.
The resulting numerator and f^r have degree difference k and exhibit membership. If all
components vanish, use the zero numerator; if f is nilpotent, A_f is the zero module. -/
theorem twist_degree_detection
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (k : ℤ) (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b)
    (z : LocalizedModule.Away f A)
    (hz : ∀ p : basicOpen 𝒜 f,
      IsLocalization.map (M := Submonoid.powers f)
      (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
      (Submonoid.powers_le.mpr p.2) z ∈
        HomogeneousLocalization.degreePart 𝒜
          p.1.asHomogeneousIdeal.toIdeal.primeCompl k) :
    z ∈ degreeZeroFractions (fun n : ℕ ↦ (𝒜 n : Set A))
      (fun n : ℕ ↦ {y : A | if 0 ≤ k + n then y ∈ 𝒜 (k + n).toNat else y = 0})
      (Submonoid.powers f) := by sorry

end AlgebraicGeometry.Proj
