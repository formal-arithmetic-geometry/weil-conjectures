/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.Paper.ZlFiniteAdicDirectImage
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.Paper.ProperCoincidenceFrobenius
import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso
import Mathlib.FieldTheory.Finite.GaloisField
public import Sheaf.Paper.ProperSectionsSemilinearGerms
public import Mathlib.Algebra.DirectSum.Module
import Sheaf.SixFunctors.FrobeniusCohomologyTransport

/-! # Evaluation of finite Weil sections and Frobenius return

Source: Stacks Project, Tag 03QP(1); Deligne, Weil II, (1.1.3), (1.1.7)--(1.1.13);
blueprint main-20261015, lem-a1-finite-boundary-weights, geometric-stalk correction
(blueprint: lem-a1-finite-weil-sections-decomposition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (Z₀ : Over (Spec (.of D.k₀))) [IsFinite Z₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The finite set of geometric lifts of a closed point in the geometric fibre.
Source: Stacks 03QP(1), with the geometric-stalk correction
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
abbrev A1FinitePointLifts (x : {x : Z₀.left // x ∈ closedPoints Z₀.left}) :=
  {z : Spec (.of D.k) ⟶ (D.geometricFiber Z₀).left //
    z ≫ (D.geometricFiber Z₀).hom = 𝟙 _ ∧
    (z ≫ pullback.fst Z₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).base
        (IsLocalRing.closedPoint D.k) = x.val}

/-- Degree-zero compact geometric cohomology, with its actual action on Weil morphisms.
Source: Stacks 03QP(1); Deligne (1.1.14)
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
abbrev a1FiniteCohomologyFunctor :=
  sfWeilForget D c.l c.different Z₀ E.val ⋙
    frobeniusCohomologyRationalFunctor D c.l c.different E.val Z₀
      (Compactification.ofIsProper Z₀.hom) true ⋙
    DerivedCategory.coefficientFdCohomology E.val 0

/-- The actual geometric stalk functor, including its action on Weil morphisms.
Source: Deligne (1.1.10); the recorded local point complex
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
abbrev a1FiniteStalkFunctor (z : Spec (.of D.k) ⟶ (D.geometricFiber Z₀).left) :=
  letI := frobeniusPointPrimeInvertible D c.l c.different
  letI := sfWeilPrimeInvertible D c.l c.different Z₀
  sfWeilForget D c.l c.different Z₀ E.val ⋙
    rationalDerivedPullback c.l E.val z ⋙ pointRationalFibre D c.l c.different E.val ⋙
    DerivedCategory.coefficientFdCohomology E.val 0

/-- Canonical stalk evaluation: H⁰ of the recorded compact rational counit germ.
There is no choice of a linear map here. The identity compactification comparison
is already part of rationalGerm.
Source: Stacks 03QP(1); Deligne (1.1.14)
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
def a1FiniteEvaluation (K : sfWeilComplex D c.l c.different Z₀ E.val)
    (x : {x : Z₀.left // x ∈ closedPoints Z₀.left}) (z : A1FinitePointLifts D Z₀ x) :
    (a1FiniteCohomologyFunctor D c Z₀ E).obj K ⟶
      (a1FiniteStalkFunctor D c Z₀ E z.val).obj K :=
  letI : Fact (c.l ≠ D.p) := ⟨c.different⟩
  (DerivedCategory.coefficientFdCohomology E.val 0).map
    (ProperSemilinearGerms.rationalGerm D Z₀ c.l E.val z.val z.property.1 K.carrier)

/-- The specified compact geometric Frobenius on H⁰, not an arbitrary endomorphism.
Source: Deligne (1.1.14), global geometric Frobenius
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
abbrev a1FiniteFrobenius (K : sfWeilComplex D c.l c.different Z₀ E.val) :=
  (globalGeometricFrobeniusOnCohomology D c E Z₀
    (Compactification.ofIsProper Z₀.hom) K 0).2.hom

/-- Finite geometric sections decompose by their canonical stalk evaluations.
Source: Stacks 03QP(1); Deligne, Weil II (1.1.3), (1.1.7)--(1.1.14);
blueprint main-20261015, corrected first evaluation display
(blueprint: lem-a1-finite-weil-sections-decomposition).

Proof: finite base change makes the geometric structure map finite and proper.
Use lem-pod-proper-coincidence-frobenius with its identity compactification and
lem-zl-finite-adic-direct-image to obtain the canonical germ isomorphism, natural
in underlying sheaf maps. Closed-point residue fields are finite separable extensions;
the finite-field Galois theorem counts their lifts and makes the moving-point map
one cycle of length d. Regroup the finite geometric-stalk sum by closed points.
The point-fibre convention gives finite-dimensional stalks and thus finite-dimensional
sections. Expand the r-th global Frobenius iterate as the iterated Weil map followed
by iterated compact transport, using naturality and integral pullback composition.
Apply lem-a1-proper-sections-semilinear-germs to this composite: for r=1 its stalk
blocks are isomorphisms from Tz to z. For r=d the moving point returns to z and
its germ coefficient is exactly localFrobeniusCohomology, with its specified point
transport and return comparison. This proves the return formula. The inverse block
permutation gives invertibility of the specified global Frobenius. Scalar extension
from the common finite coefficient field gives the algebraically closed convention.
The empty scheme gives the unique map between zero spaces.
-/
theorem a1FiniteWeilSectionsDecompositionRational
    (K : sfWeilComplex D c.l c.different Z₀ E.val)
    (hK : sfRationalHeartProperty c.l E.val (D.geometricFiber Z₀).left K.carrier) :
    Finite {x : Z₀.left // x ∈ closedPoints Z₀.left} ∧
    (∀ x : {x : Z₀.left // x ∈ closedPoints Z₀.left},
      Nat.card (A1FinitePointLifts D Z₀ x) = localClosedPointDegree D Z₀ x ∧
        1 ≤ localClosedPointDegree D Z₀ x) ∧
    FiniteDimensional E ((a1FiniteCohomologyFunctor D c Z₀ E).obj K) ∧
    Function.Bijective (a1FiniteFrobenius D c Z₀ E K) ∧
    (∃ e : (a1FiniteCohomologyFunctor D c Z₀ E).obj K →ₗ[E]
        DirectSum {x : Z₀.left // x ∈ closedPoints Z₀.left} (fun x ↦
          DirectSum (A1FinitePointLifts D Z₀ x) (fun z ↦
            (a1FiniteStalkFunctor D c Z₀ E z.val).obj K)),
      Function.Bijective e ∧
      ∀ v x z, (e v x) z = a1FiniteEvaluation D c Z₀ E K x z v) ∧
    (∀ x : {x : Z₀.left // x ∈ closedPoints Z₀.left},
      ∃ T : Equiv.Perm (A1FinitePointLifts D Z₀ x),
        (∀ z, (T z).val = ProperSemilinearGerms.movingPoint D Z₀ z.val 0) ∧
        (∀ z w, ∃ n : Fin (localClosedPointDegree D Z₀ x), (T^[n.val]) z = w) ∧
        (∀ z, ∃ b : ((a1FiniteStalkFunctor D c Z₀ E (T z).val).obj K) ≃ₗ[E]
            ((a1FiniteStalkFunctor D c Z₀ E z.val).obj K),
          (a1FiniteEvaluation D c Z₀ E K x z).hom.comp
              (a1FiniteFrobenius D c Z₀ E K) =
            b.toLinearMap.comp (a1FiniteEvaluation D c Z₀ E K x (T z)).hom)) ∧
    (∀ (x : {x : Z₀.left // x ∈ closedPoints Z₀.left})
        (z : A1FinitePointLifts D Z₀ x),
      ∃ h : z.val ≫ localPositivePower (D.geometricFrobenius Z₀).hom
            (localClosedPointDegree D Z₀ x - 1) =
          localPositivePower (frobeniusPointIso D).hom
            (localClosedPointDegree D Z₀ x - 1) ≫ z.val,
        (a1FiniteEvaluation D c Z₀ E K x z).hom.comp
            (a1FiniteFrobenius D c Z₀ E K ^ localClosedPointDegree D Z₀ x) =
          (localFrobeniusCohomology c.l E.val D c.different Z₀ K z.val
            (localClosedPointDegree D Z₀ x - 1) h 0).hom.comp
              (a1FiniteEvaluation D c Z₀ E K x z).hom) ∧
    (∀ (L : sfWeilComplex D c.l c.different Z₀ E.val),
      sfRationalHeartProperty c.l E.val (D.geometricFiber Z₀).left L.carrier →
      ∀ (f : K ⟶ L) (x : {x : Z₀.left // x ∈ closedPoints Z₀.left})
        (z : A1FinitePointLifts D Z₀ x),
      (a1FiniteCohomologyFunctor D c Z₀ E).map f ≫ a1FiniteEvaluation D c Z₀ E L x z =
        a1FiniteEvaluation D c Z₀ E K x z ≫ (a1FiniteStalkFunctor D c Z₀ E z.val).map f) := by
  sorry

/-- Scalar extension from the specified common finite coefficient field to Qbar.
Source: Deligne (1.1.3), common-stage coefficients
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
abbrev a1FiniteExtend := ModuleCat.extendScalars (R := E.val) (S := c.Qbar) E.val.subtype

/-- Compact H⁰ with algebraically closed coefficients, extended from its common stage.
Source: Deligne (1.1.3), (1.1.14)
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
abbrev a1FiniteQbarCohomologyFunctor :=
  a1FiniteCohomologyFunctor D c Z₀ E ⋙ a1FiniteExtend D c E

/-- Geometric stalks with algebraically closed coefficients at the same common stage.
Source: Deligne (1.1.3), (1.1.10)
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
abbrev a1FiniteQbarStalkFunctor
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Z₀).left) :=
  a1FiniteStalkFunctor D c Z₀ E z ⋙ a1FiniteExtend D c E

/-- The scalar extension of the canonical counit evaluation, with no chosen map.
Source: Stacks 03QP(1); Deligne (1.1.3)
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
def a1FiniteQbarEvaluation (K : sfWeilComplex D c.l c.different Z₀ E.val)
    (x : {x : Z₀.left // x ∈ closedPoints Z₀.left}) (z : A1FinitePointLifts D Z₀ x) :=
  (a1FiniteExtend D c E).map (a1FiniteEvaluation D c Z₀ E K x z)

/-- The specified global geometric Frobenius extended from the common field stage.
Source: Deligne (1.1.3), (1.1.14)
(blueprint: lem-a1-finite-weil-sections-decomposition). -/
abbrev a1FiniteQbarFrobenius (K : sfWeilComplex D c.l c.different Z₀ E.val) :=
  ((a1FiniteExtend D c E).map (globalGeometricFrobeniusOnCohomology D c E Z₀
    (Compactification.ofIsProper Z₀.hom) K 0).2).hom

/-- The finite geometric-stalk decomposition with Qbar coefficients, using a common
finite field of definition for the constructible Weil sheaf and every morphism.
The evaluation is fixed by its actual germ components; T is the geometric moving-point
cycle, and the return coefficient is scalar extension of the recorded local operator.
Source: Stacks 03QP(1); Deligne, Weil II (1.1.3), (1.1.7)--(1.1.14);
blueprint main-20261015, corrected first evaluation display
(blueprint: lem-a1-finite-weil-sections-decomposition).

Proof: apply the preceding rational assertion at the chosen common field stage.
Scalar extension preserves finite-dimensionality, isomorphisms and finite direct sums,
including the empty sum. Extend each canonical germ, the specified global operator,
the invertible cyclic block maps and the specified local operator. Functoriality
preserves both the one-step and return identities. Given a Weil-sheaf morphism,
choose a common finite field stage for its source, target and arrow, as in the recorded
common-stage category. The rational naturality square extends to exactly the square
below. The coefficient-transition comparisons in the recorded cohomology and stalk
functors identify these constructions after enlarging the common field; hence they
interpret the Qbar objects and maps independently of the presentation.
-/
theorem a1FiniteWeilSectionsDecomposition
    (K : sfWeilComplex D c.l c.different Z₀ E.val)
    (hK : sfRationalHeartProperty c.l E.val (D.geometricFiber Z₀).left K.carrier) :
    Finite {x : Z₀.left // x ∈ closedPoints Z₀.left} ∧
    (∀ x : {x : Z₀.left // x ∈ closedPoints Z₀.left},
      Nat.card (A1FinitePointLifts D Z₀ x) = localClosedPointDegree D Z₀ x ∧
        1 ≤ localClosedPointDegree D Z₀ x) ∧
    FiniteDimensional c.Qbar ((a1FiniteQbarCohomologyFunctor D c Z₀ E).obj K) ∧
    Function.Bijective (a1FiniteQbarFrobenius D c Z₀ E K) ∧
    (∃ e : (a1FiniteQbarCohomologyFunctor D c Z₀ E).obj K →ₗ[c.Qbar]
        DirectSum {x : Z₀.left // x ∈ closedPoints Z₀.left} (fun x ↦
          DirectSum (A1FinitePointLifts D Z₀ x) (fun z ↦
            (a1FiniteQbarStalkFunctor D c Z₀ E z.val).obj K)),
      Function.Bijective e ∧
      ∀ v x z, (e v x) z = a1FiniteQbarEvaluation D c Z₀ E K x z v) ∧
    (∀ x : {x : Z₀.left // x ∈ closedPoints Z₀.left},
      ∃ T : Equiv.Perm (A1FinitePointLifts D Z₀ x),
        (∀ z, (T z).val = ProperSemilinearGerms.movingPoint D Z₀ z.val 0) ∧
        (∀ z w, ∃ n : Fin (localClosedPointDegree D Z₀ x), (T^[n.val]) z = w) ∧
        (∀ z, ∃ b : ((a1FiniteQbarStalkFunctor D c Z₀ E (T z).val).obj K) ≃ₗ[c.Qbar]
            ((a1FiniteQbarStalkFunctor D c Z₀ E z.val).obj K),
          (a1FiniteQbarEvaluation D c Z₀ E K x z).hom.comp
              (a1FiniteQbarFrobenius D c Z₀ E K) =
            b.toLinearMap.comp (a1FiniteQbarEvaluation D c Z₀ E K x (T z)).hom)) ∧
    (∀ (x : {x : Z₀.left // x ∈ closedPoints Z₀.left})
        (z : A1FinitePointLifts D Z₀ x),
      ∃ h : z.val ≫ localPositivePower (D.geometricFrobenius Z₀).hom
            (localClosedPointDegree D Z₀ x - 1) =
          localPositivePower (frobeniusPointIso D).hom
            (localClosedPointDegree D Z₀ x - 1) ≫ z.val,
        (a1FiniteQbarEvaluation D c Z₀ E K x z).hom.comp
            (a1FiniteQbarFrobenius D c Z₀ E K ^ localClosedPointDegree D Z₀ x) =
          ((a1FiniteExtend D c E).map
            (localFrobeniusCohomology c.l E.val D c.different Z₀ K z.val
              (localClosedPointDegree D Z₀ x - 1) h 0)).hom.comp
              (a1FiniteQbarEvaluation D c Z₀ E K x z).hom) ∧
    (∀ (L : sfWeilComplex D c.l c.different Z₀ E.val),
      sfRationalHeartProperty c.l E.val (D.geometricFiber Z₀).left L.carrier →
      ∀ (f : K ⟶ L) (x : {x : Z₀.left // x ∈ closedPoints Z₀.left})
        (z : A1FinitePointLifts D Z₀ x),
      (a1FiniteQbarCohomologyFunctor D c Z₀ E).map f ≫ a1FiniteQbarEvaluation D c Z₀ E L x z =
        a1FiniteQbarEvaluation D c Z₀ E K x z ≫
          (a1FiniteQbarStalkFunctor D c Z₀ E z.val).map f) := by
  sorry

end WeilConjectures
