/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.DerivedPullbackTensorHom

/-! Coefficient passage for the explicit Frobenius point transport. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Frobenius transport respects extension of coefficient fields and the common-stage
realization over an algebraic closure. The equality arguments insert the canonical object
formulas; by proof irrelevance the result does not depend on the proofs supplied.

Source: Deligne, *La conjecture de Weil II*, (1.1.3) and (1.1.7), pp. 150--151;
the explicit coefficient normalization is the argument of steps 3--4 of
`lem-weil-frobenius-point-transport-natural`.
(blueprint: lem-weil-frobenius-point-coefficient-passage).

Proof: first identify the restriction transformation at the point with sigma on complexes.
Its section formula is the restriction along the Frobenius arrow, and the uniqueness
assertions for the finite and integral sigma maps identify their degree components.
Restriction of scalars along the inverse ULift equivalence identifies the completed
sections functor with `pointCompletedSections`; localization of this identification and
of the chain transformation identifies integral Frobenius transport with
`pointTransport` of `lem-weil-point-automorphism-transport-scalar-extension`.
The comparison kappa is the same specified comparison, since the prime-unit inputs are
propositions. Apply that lemma's integral and rational scalar equations. Conjugate by
`pointIntegralRationalNormalization` and `pointRationalNormalization`. Their definitions
are the coefficient-down comparison and the counit of coefficient-size descent;
naturality of the counit cancels size descent, and the pure-tensor normalization of
`pointFibreRationalDownIso` identifies the remaining arrow with rationalization of the
integral sigma-kappa composite. The normalizations of `pointRationalFibreScalarIso` and
`rationalPullbackScalarComparison` identify the two outer comparisons. Cancel the
normalization isomorphisms and use faithfulness of the module carrier lift to obtain the
finite-extension equation, with the supplied rational object equality inserted.

For algebraically closed coefficients, take all finite subfields simultaneously.
Integral naturality is the localization of sigma followed by the natural kappa comparison;
the scalar equation just obtained supplies the coefficient compatibility hypothesis of
`lem-weil-point-transformation-coefficient-descent`. Apply that lemma to this family.
The preceding rational normalization identifies its rational components with the explicit
Frobenius components. Its common-stage normalization therefore identifies the component
at (E,K) with the image of this explicit rational arrow in the point-category cocone,
which is `frobeniusPointTransportQbar`. Naturality of the descended transformation gives
the first equation after inserting the supplied fibre and pullback object equalities.
These arguments also cover zero objects, identity coefficient extensions and arbitrary
morphisms represented only after a common finite extension; no completeness hypothesis
on the ambient integral section modules is used. -/
theorem frobeniusPointTransport_coefficient_passage
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (hR : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (N : sfRationalConstructibleCategory l E (Spec (.of D.k))),
      letI := frobeniusPointPrimeInvertible D l hl
      (rationalDerivedPullback l E (frobeniusPointIso D).hom).obj N =
        frobeniusPointRationalPullbackObj D l hl E N)
    (hQ : ∀ (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
      (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))),
      letI := frobeniusPointPrimeInvertible D l hl
      (commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj A =
        frobeniusPointQbarPullbackObj D l hl Ω A)
    (hF : ∀ (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
      (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))),
      (pointQbarFibre D l hl Ω).obj A = pointQbarFibreObj D l hl Ω A) :
    (∀ (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
      [IsAlgClosure ℚ_[l] Ω]
      (A B : generalAlgebraicallyClosedConstructibleCategory l Ω
        (Spec (.of D.k)))
      (u : A ⟶ B),
      letI : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
        fun x => frobeniusPointPrimeInvertible D l hl x
      (eqToHom (hF Ω A).symm ≫
          (pointQbarFibre D l hl Ω).map u ≫
          eqToHom (hF Ω B)) ≫
          frobeniusPointTransportQbar D l hl Ω B =
        frobeniusPointTransportQbar D l hl Ω A ≫
          (eqToHom (congrArg (pointQbarFibreObj D l hl Ω)
              (hQ Ω A).symm) ≫
            eqToHom (hF Ω
              ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj A)).symm ≫
            (pointQbarFibre D l hl Ω).map
              ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).map u) ≫
            eqToHom (hF Ω
              ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj B)) ≫
            eqToHom (congrArg (pointQbarFibreObj D l hl Ω)
              (hQ Ω B)))) ∧
    (∀ (E' L : Type u) [Field E'] [Algebra ℚ_[l] E']
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
            (eqToHom (hR L
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
              (eqToHom (hR E' K).symm))) := by sorry

end WeilConjectures
