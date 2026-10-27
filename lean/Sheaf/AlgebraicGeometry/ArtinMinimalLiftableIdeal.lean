module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestQuotient
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.HopkinsLevitzki

/-! # The smallest ideal allowing a deformation to lift

Source: Stacks Project, Formal Deformation Theory, Tag 06SZ,
lemma-largest-closed-where-lift (blueprint: lem-sfb-artin-minimal-liftable-ideal).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k] [Algebra R k]
  [Algebra.FiniteType R k]

/-- An ideal contained in the kernel is liftable if x is the restriction, up to
isomorphism, of an object over the literal quotient B/L.
Source: Stacks, Tag 06SZ (blueprint: lem-sfb-artin-minimal-liftable-ideal). -/
def IsLiftableIdeal (F : CofibredGroupoids.{u, v, w} R k)
    {B A : TestCategory R k} (f : B ⟶ A) (x : fibre F A) (L : Ideal (ring B)) : Prop :=
  ∃ hL : L ≤ RingHom.ker (map f).toRingHom,
    ∃ y : fibre F (testQuotient f L hL),
      Nonempty ((push F (testQuotientTo f L hL)).obj y ≅ x)

/-- A socle extension has a least ideal whose quotient admits a lift of x.
Source: Stacks, Tag 06SZ (blueprint: lem-sfb-artin-minimal-liftable-ideal).
Proof: the kernel I is liftable because B/I is canonically isomorphic to A.
Liftability is upward closed by covariant transport and its composition isomorphisms.
Since the maximal ideal kills I, its ideals are k-subspaces. For liftable J and K,
use Submodule.exists_isCompl to complement J+K inside I, and enlarge J to J' so that
J'+K=I and J' intersect K=J intersect K. The map from B/(J' intersect K) to
(B/J') times over A (B/K) is an isomorphism: its kernel is J' intersect K, and
surjectivity follows by writing b-c=j+t with j in J' and t in K. Apply the
essential-surjectivity part of (RS) to the two lifts with their specified
identifications over A. This makes J intersect K liftable. By
isArtinianRing_iff_isFiniteLength the ideals of B have a finite strict-chain bound,
so the nonempty set of liftable ideals has a minimal member M. For every liftable L,
M intersect L is liftable; minimality forces M intersect L=M, proving M is least.
The source's displayed A/(J intersect K) is a typo for B/(J intersect K). -/
theorem exists_isLeast_liftableIdeal (F : CofibredGroupoids.{u, v, w} R k)
    (hF : IsPredeformation F) (hRS : IsRimSchlessinger F)
    {B A : TestCategory R k} (f : B ⟶ A) (hf : Function.Surjective (map f))
    (hI : ∀ b ∈ IsLocalRing.maximalIdeal (ring B),
      ∀ t ∈ RingHom.ker (map f).toRingHom, b * t = 0) (x : fibre F A) :
    ∃ L : Ideal (ring B), IsLeast {J : Ideal (ring B) | IsLiftableIdeal F f x J} L := sorry

end AlgebraicGeometry.ArtinDeformation
