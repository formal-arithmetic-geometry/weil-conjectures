module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Testing primaryness on homogeneous factors

Source: Altman--Kleiman, A Term of Commutative Algebra, Proposition 20.24,
printed p. 122 (PDF p. 130), specialized to the regular module and a proper homogeneous ideal.
(blueprint: lem-sfb-homogeneous-primary-test)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal.IsHomogeneous

/-- A proper homogeneous ideal of a Noetherian nonnegatively graded commutative ring is primary
if its primaryness can be tested on homogeneous factors.
Source: Altman--Kleiman, A Term of Commutative Algebra, Proposition 20.24, printed p. 122,
specialized to the regular module and a proper homogeneous ideal.
(blueprint: lem-sfb-homogeneous-primary-test)

Proof: (1) Given uv in J with u outside J, let t be the least degree of a component u_t
outside J. Subtract from u the sum q of its components of degree below t. Then q belongs
to J, w = u - q has no components below t, w_t = u_t, and vw belongs to J.
(2) If every nonzero component v_j has a power v_j^{e_j} in J with e_j positive, take
N = 1 + sum_j (e_j - 1). Every term in the expansion of v^N has a factor v_j^{e_j},
so v^N belongs to J. For v = 0 take N = 1.
(3) Otherwise let s be the least degree whose component c = v_s has no positive power
in J. The sum a of the components below s has a positive power a^k in J by the same
finite expansion argument, including the empty sum case. Set z = v - a.
(4) In the expansion of z^k w = (v - a)^k w, the term with no v factor is in J since
a^k is in J, and all other terms are multiples of vw. Hence z^k w belongs to J.
(5) Its component of degree k*s + t is c^k u_t: all degrees from z are at least s
and all degrees from w are at least t, so equality forces all these least degrees.
Homogeneity of J puts this product in J, even when it vanishes.
(6) Apply the homogeneous-factor hypothesis to u_t and c^k, using commutativity.
It gives (c^k)^h = c^{k*h} in J for positive h, contradicting the choice of s.
Thus (2) applies to every v, proving primaryness. These are the six elementary
steps of the node's proof; no additional proof dependencies are required.
-/
theorem isPrimary_of_homogeneous_factors {R : Type u} [CommRing R]
    [IsNoetherianRing R] (𝒜 : ℕ → AddSubgroup R) [GradedRing 𝒜]
    {J : Ideal R} (hJ : J.IsHomogeneous 𝒜) (hJ_ne_top : J ≠ ⊤)
    (homogeneous_primary : ∀ {a b : R},
      SetLike.IsHomogeneousElem 𝒜 a → SetLike.IsHomogeneousElem 𝒜 b →
      a * b ∈ J → a ∉ J → ∃ h : ℕ, 1 ≤ h ∧ b ^ h ∈ J) :
    J.IsPrimary := by
  sorry

end Ideal.IsHomogeneous
