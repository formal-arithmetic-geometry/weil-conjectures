module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# The homogeneous core of a primary ideal

Source: Altman--Kleiman, A Term of Commutative Algebra, Exercise 20.26 and
Proposition 20.24, printed p.122; solution to Exercise 20.26, printed p.229,
specialized to the module R over itself. (blueprint: lem-sfb-primary-homogeneous-core)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal.IsPrimary

/-- The homogeneous core of a primary ideal in a Noetherian, nonnegatively graded
commutative ring is proper, homogeneous, primary, and contained in the original ideal.
Source: Altman--Kleiman, Exercise 20.26 and Proposition 20.24, printed p.122,
and the solution to Exercise 20.26, printed p.229, specialized to M = R.
(blueprint: lem-sfb-primary-homogeneous-core)

Proof: Put H = Q*. Componentwise addition and negation preserve membership in H.
The degree-d component of sr is the finite sum of products s_j r_i with i+j=d;
each belongs to Q when every r_i belongs to Q. Thus H is an ideal. Components of
an element of H again lie in H, so it is homogeneous. Summing the components shows
H is contained in Q, hence proper. For a homogeneous element, membership in H is
equivalent to membership in Q. If homogeneous a,b satisfy ab in H and a outside H,
then ab is in Q and a is outside Q. Primaryness of Q gives b^h in Q for some h >= 1.
The element b^h is homogeneous, including when b is zero or has degree zero, so it
belongs to H. Apply [lem-sfb-homogeneous-primary-test] to this proper homogeneous
ideal H in the given Noetherian ring to obtain primaryness for arbitrary factors.
-/
theorem homogeneousCore_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type v} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {Q : Ideal R} (hQ : Q.IsPrimary) :
    (Q.homogeneousCore 𝒜).toIdeal ≠ ⊤ ∧
      (Q.homogeneousCore 𝒜).toIdeal.IsHomogeneous 𝒜 ∧
      (Q.homogeneousCore 𝒜).toIdeal.IsPrimary ∧
      (Q.homogeneousCore 𝒜).toIdeal ≤ Q := by
  sorry

end Ideal.IsPrimary
