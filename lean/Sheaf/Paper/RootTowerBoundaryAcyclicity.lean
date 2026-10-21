module
public import Sheaf.Paper.RootBoundaryScalarComparison

import Sheaf.Paper.RootCoordinateSupportedVanishing
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Sheaf.Paper.IntegralLisseClosedBaseChange
import Sheaf.Paper.CondensedSurjectiveClosedEquivalence
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.Paper.ProfiniteConstantDerivedFunctions

/-!
# Relative boundary acyclicity of the compatible root tower

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
agent-formulated tame-boundary root-tower calculation.
(blueprint: lem-sfb-root-tower-boundary-acyclicity).

The coefficient ring contains all norm-continuous functions, even for incomplete Omega.
The conclusion is a normalized isomorphism in the ordinary unbounded derived category,
with entire-scheme diagrams for profinite families and canonical scalar-restriction arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RootBoundary
/-- Boundary restriction of one profinite term of the punctured compatible-root tower.
Source: direct-image proof paragraph (3), agent-formulated all-continuous calculation
(blueprint: lem-sfb-root-tower-boundary-acyclicity).

Proof: (1) Apply lem-sfb-root-coordinate-supported-vanishing one coordinate at a time.
The closed-support triangle of det-lem-formal-closed-support-adjunction identifies the
puncture unit as an isomorphism. Normalized derived composition pushes that actual unit
to U and restricts it to S, giving openUnit, not an unspecified isomorphism.
(2) The finite monic root algebras are finite free by lem-weil-pbc-monic-quotient-free;
lem-weil-pbc-finite-algebra-is-integral and passage to the filtered colimit make q_P
integral. The parameter test projection is integral too. In its closed fibre every root
is nilpotent. The zero-root copy of S[P] maps surjectively and closed into that fibre;
there is no assertion that the two schemes are equal or that the nil exponent is uniform.
(3) Apply lem-sfb-integral-lisse-closed-base-change to the full projection and S.
The actual pullback along the surjective closed immersion is an equivalence by
new-lem-weil-pbc-condensed-surjective-closed-equivalence. Its unit is invertible and its
inverse is exact. Normalized derived composition then gives exactly boundaryExchange.
(4) Pull the supplied boundary identification to S[P], using
lem-weil-pbc-profinite-point-pullback. The normalized comparison of
lem-sfb-profinite-constant-derived-functions identifies derived parameter evaluation
with an isomorphism. Compose inverse openUnit, fullRestriction and inverse evaluation.
This gives NormalizedComparison in the derived category itself. Its defining equation
makes H^0 the actual restriction of full-tower sections. At the one-point parameter,
evaluation is the identity and the triangle identities identify the full source with
i^*N, so the comparison is the inverse of the puncture unit under that identification.
(5) Naturality of units, exchange mates and evaluation gives the module and parameter
squares. Apply those same diagrams on entire pro-etale base changes U[Q] to obtain
family-level equivariance, with the supplied module action and before point evaluation.
For the coefficient clause, use the actual ordinary tensor unit x maps to 1 tensor x.
The target model unit and the directional internal-Hom restriction land in the common
restricted Omega-model. The scalar-extended boundary identification and the scalar
restriction diagrams for exchange and parameter evaluation identify both legs of the
full-source cospan with its common boundary arrow. The biproduct universal property
combines those two equalities into ScalarCompatibility. Right-derived
restriction comparisons retain their canonical direction; no scalar/direct-image
comparison is inverted. Cancellation of the invertible puncture units gives compatibility
of the normalized comparisons themselves.
(6) If r = 0, the tower and puncture are U, the stratum is U, and the unit is the identity.
For the empty parameter the free module and both derived objects are zero. Rank zero
and the empty stratum also give zero. A finite parameter gives the finite product of
the one-point models. No cohomology/limit interchange or finite-subextension descent
for incomplete Omega is used. -/
theorem rootTower_boundary_acyclicity
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra E Ω] [IsAlgClosure E Ω]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) [LocallyOfFiniteType y] [QuasiCompact y]
    [IsSeparated y] (hY : IsRegularScheme Y)
    (A : Type u) [CommRing A] (b : Spec (.of A) ⟶ Y) [Etale b]
    (r : ℕ) (s : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv (∏ i, s i)}))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({s i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (R : Type u) [CommRing R]
    (a : A →+* R) [WeaklyEtale (Spec.map (CommRingCat.ofHom a))] :
    Assertion E p (fun i ↦ a (s i)) E ∧ Assertion Ω p (fun i ↦ a (s i)) E ∧
      ScalarCompatibility p (fun i ↦ a (s i)) E Ω := by
  sorry
end AlgebraicGeometry.ProEtale.RootBoundary
