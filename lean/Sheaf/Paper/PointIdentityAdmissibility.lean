/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.Paper.ExceptionalAdjointAdmissibility
public import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.FiniteCoefficientPoint

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.SfCommonStageWeilCohomology
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek

/-!
# Admissibility of the identity of the geometric point

Source: Weil blueprint, main-20261015, `sk-thm-sf-global-duality/lem-sf-point.proof.md`,
identity-adjunction sentence (blueprint: lem-sf-point-identity-admissibility).

The auxiliary structures package the identity identifications and their equations for
this statement. All functors and coefficient maps are the published canonical ones.
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Identity identifications for the actual ambient compact-support adjunctions, including
all refinements. The two component equations say that the transported unit and counit
are identities. Source: blueprint `lem-sf-point.proof.md`, identity-adjunction sentence
(blueprint: lem-sf-point-identity-admissibility). -/
structure PointIdentityAdjunctionModel (s : Scheme.{u}) (A : Type u) [CommRing A]
    [Finite A] where
  /-- The actual ambient adjunction family at the identity compactification. -/
  datum : SfAmbientExceptionalRightAdjointDatum A (𝟙 s) (Compactification.ofIsProper (𝟙 s))
  /-- Identification of each compact-support candidate with the identity. -/
  leftIso : ∀ d : Compactification (𝟙 s), sfAmbientCompactSupportCandidate A d ≅ 𝟭 _
  /-- Identification of each ambient right adjoint with the identity. -/
  rightIso : ∀ d : Compactification (𝟙 s), datum.rightAdjoint d ≅ 𝟭 _
  /-- Under the identifications the unit is the identity. -/
  unit_identity : ∀ (d : Compactification (𝟙 s)) (K : proEtaleDerivedCategory s A),
    (datum.adjunction d).unit.app K ≫
        (datum.rightAdjoint d).map ((leftIso d).hom.app K) ≫ (rightIso d).hom.app K = 𝟙 K
  /-- Under the identifications the counit is the identity. -/
  counit_identity : ∀ (d : Compactification (𝟙 s)) (K : proEtaleDerivedCategory s A),
    (datum.adjunction d).counit.app K =
      (sfAmbientCompactSupportCandidate A d).map ((rightIso d).hom.app K) ≫
        (leftIso d).hom.app K
  /-- Every left refinement comparison becomes the identity. -/
  left_refinement : ∀ {d e : Compactification (𝟙 s)} (r : d ⟶ e),
    (datum.theta r).hom ≫ (leftIso e).hom = (leftIso d).hom
  /-- Every right refinement comparison becomes the identity. -/
  right_refinement : ∀ {d e : Compactification (𝟙 s)} (r : d ⟶ e),
    (datum.rho r).hom ≫ (rightIso d).hom = (rightIso e).hom

/-- The component equation identifying the canonical right-adjoint coefficient mate
with the identity of the actual derived coefficient-change functor. This is a predicate,
not a replacement coefficient comparison. Source: blueprint `lem-sf-point.proof.md`,
identity-adjunction sentence (blueprint: lem-sf-point-identity-admissibility). -/
noncomputable def PointIdentityCoefficientComparison
    {s : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (MA : PointIdentityAdjunctionModel s A)
    (MB : PointIdentityAdjunctionModel s B) : Prop :=
  ∀ K : proEtaleDerivedCategory s A,
    (exceptionalCoefficientExtension φ s).map
        ((MA.rightIso (Compactification.ofIsProper (𝟙 s))).inv.app K) ≫
      (exceptionalFiniteRightCoefficientMap φ (Compactification.ofIsProper (𝟙 s))
        MA.datum MB.datum).app K ≫
      (MB.rightIso (Compactification.ofIsProper (𝟙 s))).hom.app
        ((exceptionalCoefficientExtension φ s).obj K) =
      𝟙 ((exceptionalCoefficientExtension φ s).obj K)

/-- Positive coefficient stages are finite, using the recorded finiteness theorem.
The index `n` denotes exponent `n+1`, including the first finite stage.
Source: blueprint finite coefficient convention
(blueprint: lem-sf-point-identity-admissibility). -/
noncomputable instance pointIdentityFiniteCoefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)

/-- One point identity system, with precisely the three zero bounds and the identity
normalization of all finite reductions, including equal exponents.
Source: blueprint `lem-sf-point.proof.md`, identity-adjunction sentence
(blueprint: lem-sf-point-identity-admissibility). -/
structure PointIdentityFiniteSystem (s : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] where
  /-- Actual adjunctions and normalized identity identifications at each positive stage. -/
  model : ∀ n : ℕ, PointIdentityAdjunctionModel s (Padic.coefficientExtensionRing l E (n + 1))
  /-- FullCD with bound zero, on all module sheaves and every site base change. -/
  fullCD_zero : ∀ n : ℕ,
    sfFullCohomologicalDimension (𝟙 s) (Padic.coefficientExtensionRing l E (n + 1)) 0
  /-- Constructible intervals and finite Tor amplitude are preserved with zero shifts. -/
  preserves_zero : ∀ n : ℕ,
    ExceptionalAdjointPreserves l E (n + 1) (Nat.le_add_left 1 n)
      ((model n).datum.rightAdjoint (Compactification.ofIsProper (𝟙 s))) 0 0
  /-- The actual quotient-map mate becomes the identity, including nonflat reductions. -/
  reduction_identity : ∀ (m n : ℕ) (h : m ≤ n),
    PointIdentityCoefficientComparison
      (Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal l E (n + 1))
        (T := Padic.coefficientExtensionIdeal l E (m + 1))
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))) (model n) (model m)

/-- The point identity is admissible at every coefficient stage, with coherent identity
adjunctions and coefficient comparisons and bounds `cCD = cMinus = cPlus = 0`.
Source: blueprint main-20261015, `sk-thm-sf-global-duality/lem-sf-point.proof.md`,
identity-adjunction sentence (blueprint: lem-sf-point-identity-admissibility).

Proof: (1) Identity direct image is exact and identity extension by zero is identity;
the K-injective derived direct image is therefore naturally identity. (2) Its positive
cohomology on a degree-zero sheaf vanishes, also after each arbitrary pro-etale base
change, proving FullCD with bound zero. (3) In any identity compactification the open
immersion is a section of a separated proper map, hence is closed as well. (4) Gluing
on the two clopen pieces identifies extension by zero with exact direct image, so its
derived direct image is the same functor. (5) Derived direct-image composition gives
beta_d : F_d ≅ id and theta_r = beta_d followed by beta_e inverse, coherently under
identity and composition of refinements. (6) Transport the identity adjunction along
beta_d, obtaining unit beta_d inverse and counit beta_d; choose right comparisons to
be identities. These give exactly the refinement unit and counit equations; uniqueness
of right adjoints identifies any other chosen model canonically. (7) Identity preserves
constructible intervals with zero shifts and every finite Tor-amplitude test. (8) On
K-flat representatives the identity support coefficient comparison is identity, so
its right mate is identity, including nonflat finite reductions and identity scalar
extensions. All three bounds are zero independently of the field and exponent. The
finite-system definition then gives integral, rational and algebraically closed
admissibility. The identity also preserves the derived-complete subcategory and acts
identically on rationalized and common-finite-stage objects and morphisms. -/
theorem point_identity_admissibility
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    ∃ M : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
        [FiniteDimensional (Padic l) E], PointIdentityFiniteSystem (Spec (.of D.k)) l E,
      (∀ (E L : Type u) [Field E] [Algebra (Padic l) E]
        [FiniteDimensional (Padic l) E] [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (n : ℕ),
        PointIdentityCoefficientComparison (integralScalarQuotientMap l E L ι n)
          ((M E).model n) ((M L).model n)) ∧
      ∃ hS : ∀ x : Spec (.of D.k), IsUnit (l : (Spec (.of D.k)).presheaf.stalk x),
        (∀ (E : Type u) [Field E] [Algebra (Padic l) E]
          [FiniteDimensional (Padic l) E],
          (∀ n : ℕ, IsExceptionalAdjointAdmissibleAtFiniteStage l E (n + 1)
            (Nat.le_add_left 1 n) (Spec (.of D.k)) (Spec (.of D.k)) (Spec (.of D.k)) hS
            (𝟙 _) (Compactification.ofIsProper (𝟙 _))) ∧
          IsExceptionalAdjointAdmissibleAtIntegral l E
            (Spec (.of D.k)) (Spec (.of D.k)) (Spec (.of D.k)) hS
            (𝟙 _) (Compactification.ofIsProper (𝟙 _)) ∧
          IsExceptionalAdjointAdmissibleAtRational l E
            (Spec (.of D.k)) (Spec (.of D.k)) (Spec (.of D.k)) hS
            (𝟙 _) (Compactification.ofIsProper (𝟙 _))) ∧
        IsExceptionalAdjointAdmissibleAtAlgebraicallyClosed l Ω
          (Spec (.of D.k)) (Spec (.of D.k)) (Spec (.of D.k)) hS
          (𝟙 _) (Compactification.ofIsProper (𝟙 _)) := by
  sorry

end WeilConjectures
