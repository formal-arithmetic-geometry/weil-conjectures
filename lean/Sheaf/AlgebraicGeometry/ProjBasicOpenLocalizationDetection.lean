/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Detection of localized elements at homogeneous primes

Source: Stacks Project, Tag 01M7, basic-open localization argument.
-/

@[expose] public section

universe v
namespace AlgebraicGeometry.Proj

/-- Homogeneous primes of a positive-degree basic open detect equality in A_f.
Source: Stacks Project, Lemma 27.8.4, Tag 01M7, localization injectivity argument.
(blueprint: lem-sc-proj-basic-open-localization-detection)

Proof: first localize at the homogeneous elements outside a homogeneous prime p.
This localization B has a Z-grading and injects into the ordinary localization A_p.
To see injectivity, write an ordinary denominator s outside p as a finite sum of
homogeneous components. Some component is outside p, hence is a unit in B. The grading
map sends s to a Laurent polynomial over B with a unit coefficient. McCoy's polynomial
zero-divisor criterion says that this Laurent polynomial is regular: an annihilator
would annihilate every coefficient, including the unit. The grading map is injective
(evaluation at 1 is a left inverse), so s is regular in B. Thus further localization
at ordinary denominators outside p is injective, and vanishing in A_p implies that
each homogeneous component already vanishes in B.

Now write z-w over a common power of f. For a homogeneous component u of its numerator,
the ideal ann(u) is homogeneous: the homogeneous components of a*u have distinct
degrees, so a*u=0 implies that each component of a annihilates u. If no power of f
kills u, ann(u) is disjoint from the powers of f. The prime-existence theorem gives
a prime containing ann(u) and avoiding f. Its homogeneous core is prime, still contains
ann(u), and avoids f; it is relevant since f has positive degree. At this core, the
hypothesis and the preceding injectivity argument force u to vanish in B. Hence some
homogeneous denominator outside the core annihilates u, contradicting containment of
ann(u). A power of f therefore kills every component. A common power kills their sum,
proving z=w. If f is nilpotent, A_f is zero. -/
theorem basicOpen_localization_detection
    {A σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) (b : ℕ)
    (hb : 0 < b) (hf : f ∈ 𝒜 b) (z w : LocalizedModule.Away f A)
    (h : ∀ p : basicOpen 𝒜 f,
      IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2) z =
      IsLocalization.map (M := Submonoid.powers f)
        (T := p.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (Localization.AtPrime p.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
        (Submonoid.powers_le.mpr p.2) w) : z = w := by sorry

end AlgebraicGeometry.Proj
