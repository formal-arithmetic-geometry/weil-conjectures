/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusPointTransport

/-! # Coefficient compatibility of rational Frobenius point transport

Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151;
the explicit completed-coefficient normalization argument is agent-written.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Rational Frobenius transport commutes with every finite coefficient extension.
Source: Deligne, Weil II, (1.1.3) and (1.1.7), pp. 150--151; proof step 3 of
`lem-weil-frobenius-point-transport-natural` and the normalized rational equation
of `lem-weil-point-automorphism-transport-scalar-extension`.
(blueprint: lem-weil-frobenius-point-transport-rational-scalar).

Proof: identify the finite and completed sectionwise sigma maps with restriction
along the geometric Frobenius by their equality on every section. Exact localization
preserves this identification. Identify the completed comparison with the fixed
Roos-resolution comparison by its normalization on every flat-term K-flat model;
its naturality identifies the conjugates on all representatives. Thus after the
canonical coefficient unlift the integral Frobenius component is the component
`pointTransport` for this automorphism. Apply the third, rationalized equation of
`point_automorphism_transport_scalar_extension`. The normalization of the rational
fibre functor identifies its component with the scalar extension of the integral
one. The normalization of the rational pullback comparison identifies its inverse
with the rationalized integral inverse. The sections comparison is the specified
`pointRationalFibreScalarIso`, by its normalized sections formula. Conjugate the
raw equation by these three normalization isomorphisms and cancel inverse pairs.
Faithfulness of coefficient size lift gives the displayed equation. Identity
extensions and zero objects are included: the unit comparisons and zero maps give
the same cancellation, without any injectivity or nonzero-object assumption. -/
theorem frobeniusPointTransportRational_scalar
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    ∀ (E' L : Type u) [Field E'] [Algebra ℚ_[l] E']
      [FiniteDimensional ℚ_[l] E'] [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] (ι : E' →ₐ[ℚ_[l]] L)
      (K : sfRationalConstructibleCategory l E' (Spec (.of D.k))),
      letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
        fun x => frobeniusPointPrimeInvertible D l hl x
      (pointRationalFibreScalarIso D l hl E' L ι).inv.app K ≫
          frobeniusPointTransportRational D l hl L
            ((sfRationalScalarExtension l E' (Spec (.of D.k)) 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) ≫
          (pointRationalFibre D l hl L).map
            (eqToHom ((fun N ↦ (rationalDerivedPullback_existsUnique l L
              (frobeniusPointIso D).hom).exists.choose_spec.2.1 N)
              ((sfRationalScalarExtension l E' (Spec (.of D.k)) 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K)).symm) ≫
          (pointRationalFibre D l hl L).map
            ((rationalPullbackScalarComparison l E' L ι
              (frobeniusPointIso D).hom).inv.app K) ≫
          (pointRationalFibreScalarIso D l hl E' L ι).hom.app
            ((rationalDerivedPullback l E' (frobeniusPointIso D).hom).obj K) =
        (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
          (frobeniusPointTransportRational D l hl E' K) ≫
          (DerivedCategory.pointFdScalarExtension ι.toRingHom).map
            ((pointRationalFibre D l hl E').map
              (eqToHom ((fun N ↦ (rationalDerivedPullback_existsUnique l E'
              (frobeniusPointIso D).hom).exists.choose_spec.2.1 N) K).symm)) := by
  sorry

end WeilConjectures
