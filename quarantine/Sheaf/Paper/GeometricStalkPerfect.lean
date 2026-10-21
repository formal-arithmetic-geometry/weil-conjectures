/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Field.ULift
public import Mathlib.CategoryTheory.Adjunction.Additive

import Sheaf.Paper.DerivedComplete
import Sheaf.Paper.IntegralDerivedReduction
import Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.RingTheory.RlimPerfectComplete

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.AlgebraicGeometry.GeometricStalkToposPoint
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.CategoryTheory.DerivedCategory.FiniteTorAmplitudePerfect
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfRationalizationKaroubi
/-!
# Perfect geometric stalks

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-trace-perfectness`, order 1825
(blueprint: fix-lem-finite-tor-perfect).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- Finite-coefficient pro-etale stalks have bounded finite-free models.
Source: blueprint order 1825 (blueprint: fix-lem-finite-tor-perfect).
Proof: exactness of the stalk identifies stalk cohomology with stalks of cohomology,
which are finite and bounded by constructibility. Apply the ringed-point derived tensor
comparison to a constant sheaf of an arbitrary coefficient module N. Its stalk is N,
so the finite Tor interval of M is also a Tor interval of its stalk. Apply the local
Artinian finite-Tor perfectness criterion to this bounded finite-cohomology complex.
Its perfect model has finite projective terms; localness makes these finite free. -/
theorem finiteTorConstructible_proEtale_stalk_finiteFree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
    (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))))) ℤ)
    (hK : WeilConjectures.finiteTorConstructible l E n hn Y (DerivedCategory.Q.obj K)) :
    ∃ (P : CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        (P.X i) ∧ Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
          (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (finiteCoefficientModuleStalkFunctor y (Padic.coefficientExtensionRing l E n))
           (ComplexShape.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P) := by
  sorry

/-- The small-etale finite-coefficient assertion, with the actual derived-tensor
Tor predicate on etale module sheaves.
Source: blueprint order 1825 (blueprint: fix-lem-finite-tor-perfect).
Proof: exact geometric stalks preserve cohomology. Constructibility gives finite
cohomology, and boundedness gives finite support. The geometric ringed-topos point
commutes with derived tensor; apply it to every constant coefficient module N.
The given finite Tor interval therefore works for the stalk. The local Artinian
finite-Tor perfectness criterion supplies a bounded finite-projective model,
whose terms are finite free since the coefficient ring is local. -/
theorem finiteTorConstructible_etale_stalk_finiteFree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) (_hn : 1 ≤ n)
    (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))) ℤ)
    (hK : AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleFiniteTor
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) Y (DerivedCategory.Q.obj K)) :
    ∃ (P : CochainComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) ℤ)
      (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        (P.X i) ∧ Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
          (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj
        ((((pointSmallEtale y).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E n)))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P) := by
  sorry

end AlgebraicGeometry.Scheme

namespace WeilConjectures

variable {Y : AlgebraicGeometry.Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- The geometric stalk of an integral representative, followed by field scalar extension.
For the rational stage take ι to be the identity; for a common-stage object (E,K),
take the inclusion of its finite field E into the fixed algebraic closure.
The use of representatives does not impose an extra hypothesis: raw scalar localization
has exactly the integral objects, and the common-stage category has these pairs as objects.
Source: blueprint order 1825 and the rationalization/common-stage definitions
(blueprint: fix-lem-finite-tor-perfect). -/
noncomputable def fieldGeometricStalkComplex
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (y : Spec (.of Ω) ⟶ Y)
    (F : Type u) [Field F] (ι : E →+* F)
    (K : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ) :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} F)) ℤ :=
  let φ : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      ULift.{u + 1, u} F :=
    (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).symm.toRingHom.comp
      (ι.comp ((Padic.coefficientExtensionIntegers l E).subtype.comp
        (ULift.ringEquiv : ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l E) ≃+* _).toRingHom))
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).left_adjoint_additive
  ((integralCoefficientModuleStalkFunctor l E y ⋙
    ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K

/-- A rational-coefficient geometric stalk has a bounded finite-dimensional model
and is perfect. The integral representative has only the recorded derived-complete
constructibility condition; no finite-Tor hypothesis is added at field coefficients.
Source: blueprint order 1825 (blueprint: fix-lem-finite-tor-perfect).
Proof: take all finite reductions of one flat-term K-flat resolution of K.
Exact stalks and derived tensor comparison give coherent quotient identifications
between their stalks (`def-weil-integral-derived-reduction`,
`lem-pur-kflat-change-of-rings`). Evaluation at strict localization commutes with
products (`lem-cbc-proetale-classical-stalk`), so the derived-completeness triangle
identifies the integral stalk with the derived limit of this tower, using exact
products of modules (`lem-weil-derived-limit-products-core`). The coefficient DVR
is complete: compatible lifts modulo uniformizer powers form a Cauchy sequence
in E, and the closed valuation balls give its prescribed residues and uniqueness
(`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-l-adic-extension-complete`).
The first reduction is over the residue field; choose bases of its finitely many
nonzero cohomology groups and lift them to cycles. Their finite sum gives a
quasi-isomorphism from a bounded finite-dimensional complex, hence a perfect model.
Apply `lem-weil-pbc-rlim-perfect-complete` to obtain a bounded finite-projective
O_E model of the integral stalk. The constant-to-completed map fixes its O_E action.
Localization O_E → E is flat, so termwise scalar extension preserves the derived
isomorphism; finite projective terms become finite-dimensional E-vector spaces.
This bounded model is perfect over E (`def-weil-rationalization-karoubi`). -/
theorem rationalConstructible_stalk_perfect
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (scalarReductionSource.{u, u} l E Y) ℤ)
    (hK : sfIntegralConstructible l E Y (DerivedCategory.Q.obj K)) :
    (∃ (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, FiniteDimensional (ULift.{u + 1, u} E) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj (fieldGeometricStalkComplex l E y E (RingHom.id E) K) ≅
        DerivedCategory.Q.obj P)) ∧
      DerivedCategory.IsPerfect
        (DerivedCategory.Q.obj (fieldGeometricStalkComplex l E y E (RingHom.id E) K)) := by
  sorry

/-- The geometric stalk of the common-stage object represented by (E,K) has a bounded
finite-dimensional model over the fixed algebraic closure and is perfect.
Source: blueprint order 1825 (blueprint: fix-lem-finite-tor-perfect).
Proof: every common-stage object is a pair with a finite field of definition, with
no idempotent completion. Apply the rational-stage assertion to its integral
representative. Extend the bounded finite-dimensional model along E → Qlbar.
Tensor over a field is exact, preserves the cohomology isomorphism, and sends each
finite-dimensional term to a vector space of the same finite dimension. The same
finite degree interval therefore gives the required perfect model. -/
theorem commonStageConstructible_stalk_perfect
    (l : ℕ) [Fact l.Prime] (F : Type u) [Field F] [Algebra ℚ_[l] F]
    [IsAlgClosure ℚ_[l] F] (E : Padic.FiniteCoefficientFields l F)
    (y : Spec (.of Ω) ⟶ Y)
    (K : CochainComplex (scalarReductionSource.{u, u} l E.val Y) ℤ)
    (hK : sfIntegralConstructible l E.val Y (DerivedCategory.Q.obj K)) :
    (∃ (P : CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} F)) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i : ℤ, FiniteDimensional (ULift.{u + 1, u} F) (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj (fieldGeometricStalkComplex l E.val y F E.val.subtype K) ≅
        DerivedCategory.Q.obj P)) ∧
      DerivedCategory.IsPerfect
        (DerivedCategory.Q.obj (fieldGeometricStalkComplex l E.val y F E.val.subtype K)) := by
  sorry

end WeilConjectures
