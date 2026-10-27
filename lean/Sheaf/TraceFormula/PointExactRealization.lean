/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-! # Exact realization at the finite-coefficient point

Source: Stacks Project, Tag 015F and its left-derived dual; Tags 0982 and 098H;
blueprint finite point evaluation and compact Frobenius transport
(blueprint: lem-trf-point-exact-realization).

The coefficient exponent is n + 1. The ordinary pullback uses the published intrinsic
realization of the canonical constant-scalar pullback. The comparisons below are the
canonical exact-functor localization comparisons on all unbounded complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The rth power in the existing automorphism group of the geometric point.
Source: Deligne, Weil II (1.1.7); blueprint point Frobenius
(blueprint: lem-trf-point-exact-realization). -/
def trfPointFrobeniusPower (r : ℕ) : Aut (Spec (.of D.k)) :=
  @HPow.hPow (Aut (Spec (.of D.k))) ℕ (Aut (Spec (.of D.k))) inferInstance
    (frobeniusPointIso D) r

/-- Ordinary pullback along the rth power of the specified point Frobenius, with
its canonical constant coefficient action, in the existing intrinsic realization.
Source: Stacks Tag 015F; blueprint finite point transport
(blueprint: lem-trf-point-exact-realization). -/
abbrev trfPointOrdinaryPullback (n r : ℕ) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1))
    ((trfPointFrobeniusPower D r).hom)

/-- The canonical exact-functor comparison for the specified total derived pullback.
Its domain is every unbounded complex, including all K-flat representatives.
Source: Stacks Tag 015F and its left-derived dual
(blueprint: lem-trf-point-exact-realization). -/
def trfPointPullbackExactComparison (n r : ℕ) :
    DerivedCategory.Q ⋙ finiteDerivedPullback l E n (trfPointFrobeniusPower D r).hom ≅
      (trfPointOrdinaryPullback D l E n r).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  (trfPointOrdinaryPullback D l E n r).mapDerivedCategoryFactors

/-- The canonical exact evaluation comparison, using final-object sections with the
constant-section scalar map, on every unbounded complex.
Source: Stacks Tag 015F; blueprint finite point evaluation
(blueprint: lem-trf-point-exact-realization). -/
def trfPointEvaluationExactComparison (n : ℕ) :
    DerivedCategory.Q ⋙
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ≅
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors

/-- Exact realization of ordinary finite-coefficient point pullback and evaluation.
The explicit comparisons above are natural isomorphisms on all unbounded complexes;
the displayed derived-functor properties identify them with total derived comparisons.

Source: Stacks Tag 015F and its left-derived dual; Tags 0982 and 098H; blueprint
finite point evaluation (blueprint: lem-trf-point-exact-realization).

Proof plan:
1. The coefficient ring is finite by def-weil-l-adic-coefficient-extension. Apply
   prop-weil-pbc-proetale-constant-exact using precisely the coefficient isomorphism
   of prop-weil-pbc-proetale-constant-ring-map. This gives exact additive pullback.
   By lem-weil-point-proetale-sections-exact final-object evaluation is exact;
   restriction through the constant-section map preserves kernels and cokernels.
2. Apply lem-weil-pbc-exact-functor-derived-factorization to these two exact functors.
   Their termwise functors preserve quasi-isomorphisms on arbitrary complexes.
3. Apply lem-weil-pbc-exact-functor-derived-functor. The recorded finite pullback is
   exactly the induced functor of the ordinary pullback. Its canonical comparison
   on a K-flat resolution q : P -> K carries the representative H(P) to H(K) by
   localization of H(q), an isomorphism by step 2. The same comparison works for
   every K, without a K-flatness hypothesis. Evaluation uses its analogous factor.
4. Frobenius and its powers are scheme isomorphisms by def-weil-frobenius-detailed.
   The distinct primes make l invertible on s. Apply the finite clause of
   lem-weil-isomorphism-derived-pullback to obtain bounded constructibility.
5. Clause 1 of def-weil-finite-coefficient-point defines the restricted fibre functor
   as this very derived evaluation. Clause 1 of lem-weil-point-sections-finiteness
   gives bounded finite cohomology, and its full inclusion gives the stated equality.
-/
theorem trfPointExactRealization (hl : l ≠ D.p) (n r : ℕ) (_hr : 1 ≤ r) :
    (trfPointOrdinaryPullback D l E n r).Additive ∧
    PreservesFiniteLimits (trfPointOrdinaryPullback D l E n r) ∧
    PreservesFiniteColimits (trfPointOrdinaryPullback D l E n r) ∧
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).Additive ∧
    PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) ∧
    PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) ∧
    (∀ (K L : CochainComplex
        (proEtaleRingModules (Spec (.of D.k))
          (proEtaleConstantRing (Spec (.of D.k)) (Padic.coefficientExtensionRing l E (n + 1))))
        ℤ) (f : K ⟶ L), QuasiIso f →
      QuasiIso (((trfPointOrdinaryPullback D l E n r).mapHomologicalComplex (.up ℤ)).map f) ∧
      QuasiIso (((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).map f)) ∧
    (finiteDerivedPullback l E n (trfPointFrobeniusPower D r).hom).IsLeftDerivedFunctor
      (trfPointPullbackExactComparison D l E n r).hom
      (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
    ((pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory).IsRightDerivedFunctor
      (trfPointEvaluationExactComparison D l E n).inv
      (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
    (∀ K : proEtaleDerivedCategory (Spec (.of D.k))
        (Padic.coefficientExtensionRing l E (n + 1)),
      intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)) K →
        intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))
          ((finiteDerivedPullback l E n (trfPointFrobeniusPower D r).hom).obj K)) ∧
    (pointFiniteFibre D l hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) ⋙
      (DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))).ι =
      (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).ι ⋙
        (pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory) := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · intro K L f hf
    have : QuasiIso f := hf
    exact ⟨inferInstance, inferInstance⟩
  · exact ((trfPointOrdinaryPullback D l E n r).exactFunctor_derivedFunctor
      (finiteDerivedPullback l E n (trfPointFrobeniusPower D r).hom)
      (trfPointPullbackExactComparison D l E n r)).2.1
  · exact ((pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).exactFunctor_derivedFunctor
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
      (trfPointEvaluationExactComparison D l E n)).1
  · let : ∀ x : Spec (.of D.k), Invertible (l : (Spec (.of D.k)).residueField x) :=
      fun x ↦ (frobeniusPointPrimeResidueUnit D l hl x).invertible
    obtain ⟨h, _⟩ := isomorphismFiniteDerivedPullback_termwise l E
      (trfPointFrobeniusPower D r).hom n
    exact fun K hK ↦ (h K hK).1
  · rfl

end WeilConjectures
