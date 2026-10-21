/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.FdCoefficientComparisonSystem
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.Paper.PbcCommonStageCones
import Mathlib.CategoryTheory.Equivalence

/-! # Exact linear common-stage comparison descent

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence; extracted comparison subclaim
(blueprint: lem-fd-common-stage-comparison-descent).

The functors and transformations below are the existing literal-pair constructions.
The beta maps are the inverses of the scalar comparisons denoted by j in the source.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe d u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- Coherent exact finite equivalences give the specified exact linear pair equivalence.
Source: trace-definition final sentence, common-stage comparison subclaim
(blueprint: lem-fd-common-stage-comparison-descent).

Proof: (1) Use coherent-pair descent with beta = inverse j. (2) Expand the two
associators in transport and use the scalar cocycle and naturality of j to obtain
tr(mapAt u) = mapAt(tr u). (3) At each stage conjugation and full faithfulness
of J give a Hom bijection; its inverse commutes with transport by injectivity.
Both therefore descend to inverse Hom-colimit maps. (4) Essential surjectivity
at the field label of a target pair gives essential surjectivity on pairs; use
Functor.asEquivalence. (5) Enlarge a representative field to contain the scalar;
finite-stage linearity proves Omega-linearity, also for the inverse Hom maps.
(6) Descend the finite shift comparisons using scalar-shift compatibility.
(7) Every distinguished source triangle comes from a finite stage, where J is
exact. (8) To reflect triangles, choose an exact finite inverse for a finite
model of the target triangle and lift its isomorphism through the Hom bijections.
This also makes the inverse equivalence exact. No idempotent is adjoined. -/
theorem fdCommonStageComparisonDescent
    (_D : FiniteFieldDatum.{d}) (_hl : l ≠ _D.p)
    (J : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (pbcScalarSystem l Ω T dT.out iT.out))
    [∀ E, (J.Φ E).CommShift ℤ]
    (hadd : ∀ E, (J.Φ E).Additive)
    (hequiv : ∀ E, (J.Φ E).IsEquivalence)
    (hlinear : ∀ E, (J.Φ E).Linear E.val)
    (hexact : ∀ E, (J.Φ E).IsTriangulated)
    (hshift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      NatTrans.CommShift (J.β h).hom ℤ) :
    ∃ e : generalAlgebraicallyClosedConstructibleCategory l Ω T ≌ pbcQbarCategory l Ω T,
      e.functor = J.functor ∧ e.functor.Additive ∧ e.functor.Linear Ω ∧
      e.inverse.Additive ∧ e.inverse.Linear Ω ∧
      ∃ (s : e.functor.CommShift ℤ) (r : e.inverse.CommShift ℤ),
        (fun [hs : e.functor.CommShift ℤ] [hr : e.inverse.CommShift ℤ] ↦
          e.functor.IsTriangulated ∧ e.inverse.IsTriangulated ∧
          (∀ E (n : ℤ) (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
            HEq ((e.functor.commShiftIso n).hom.app ⟨E, K⟩)
              (((pbcScalarSystem l Ω T dT.out iT.out).ι E).map
                  (((J.Φ E).commShiftIso n).hom.app K) ≫
                (((pbcScalarSystem l Ω T dT.out iT.out).ι E).commShiftIso n).hom.app
                  ((J.Φ E).obj K))) ∧
          (∀ A : Triangle (generalAlgebraicallyClosedConstructibleCategory l Ω T),
            e.functor.mapTriangle.obj A ∈ distTriang (pbcQbarCategory l Ω T) ↔
              A ∈ distTriang (generalAlgebraicallyClosedConstructibleCategory l Ω T)))
          (hs := s) (hr := r) := by
  sorry

/-- Common-stage conjugation is bijective, commutes with transport, and induces
inverse maps on the actual quotient Homs. Source: trace-definition final sentence,
common-stage comparison subclaim (blueprint: lem-fd-common-stage-comparison-descent).

Proof: steps 2--3 of the node: conjugation is invertible and J is fully faithful.
Expand transport at both endpoints and substitute the scalar cocycle. Naturality
of j cancels the middle comparisons. The inverse transport equation follows by
injectivity at the larger stage. Eventual equality is thus respected in both
directions, giving inverse maps on quotient Homs. The representative formula is
exactly the defining map formula of the existing descended functor. -/
theorem fdCommonStageHomDescent
    (J : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (pbcScalarSystem l Ω T dT.out iT.out))
    (hequiv : ∀ E, (J.Φ E).IsEquivalence) :
    (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
      (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M),
      Function.Bijective (J.mapAt (hi := hA) (hj := hB) (x := A.obj) (y := B.obj))) ∧
    (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω T)
      (M N : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
      (h : M ≤ N) (f : A.toStage hA ⟶ B.toStage hB),
      (pbcScalarSystem l Ω T dT.out iT.out).tr h (J.mapAt f) =
        J.mapAt ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).tr h f)) ∧
    (∀ A B : generalAlgebraicallyClosedConstructibleCategory l Ω T,
      ∃ e : (A ⟶ B) ≃ (J.functor.obj A ⟶ J.functor.obj B),
        (∀ f, e f = J.functor.map f) ∧
        (∀ (M : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ M) (hB : B.stage ≤ M)
          (f : A.toStage hA ⟶ B.toStage hB),
          e (StageSystem.PairCategory.mkHom M hA hB f) =
            StageSystem.PairCategory.mkHom
              (X := J.functor.obj A) (Y := J.functor.obj B) M hA hB (J.mapAt f))) ∧
    (∀ E, Nonempty ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T).ι E ⋙
      J.functor ≅ J.Φ E ⋙ (pbcScalarSystem l Ω T dT.out iT.out).ι E)) := by
  sorry

/-- All equations of compatible finite transformations descend, including identities
and composition. Applying this also to composite families gives the stipulated scheme,
shift and scalar equations with their actual associators.
Source: trace-definition final sentence, common-stage comparison subclaim, step 12
(blueprint: lem-fd-common-stage-comparison-descent).

Proof: the component of descNatTrans at (E,K) is inclusion of the finite component.
Equal components therefore give equal transformations by extensionality. The identity
and composite formulas follow from functoriality of each inclusion. Whiskering uses
functorCompIso, whose components are identities, so the same calculation applies to
identity/composition of pullbacks and to the descended shift/scalar comparisons. -/
theorem fdCommonStageComparisonEquations
    (F G H : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (pbcScalarSystem l Ω T dT.out iT.out))
    (τ τ' : StageSystem.Morphism.Hom F G) (η : StageSystem.Morphism.Hom G H) :
    ((∀ E, τ.τ E = τ'.τ E) →
      StageSystem.Morphism.descNatTrans τ = StageSystem.Morphism.descNatTrans τ') ∧
    StageSystem.Morphism.descNatTrans (StageSystem.Morphism.Hom.id F) = 𝟙 F.functor ∧
    StageSystem.Morphism.descNatTrans (τ.comp η) =
      StageSystem.Morphism.descNatTrans τ ≫ StageSystem.Morphism.descNatTrans η := by
  sorry

/-- The finite part of the recorded coefficient datum, before the pair-equivalence fields.
This is input data, with the same normalized integral lifts, not an existence assertion.
Source: trace-definition final sentence, finite data preceding common-stage descent
(blueprint: lem-fd-common-stage-comparison-descent). -/
structure FdFiniteCoefficientComparison (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] where
  stage : ∀ E, FdRationalStageComparison l Ω T E
  family : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (pbcScalarSystem l Ω T dT.out iT.out)
  finite_functor : ∀ E, HEq (family.Φ E) (stage E).rational.functor
  [finite_shift : ∀ E, (family.Φ E).CommShift ℤ]
  finite_shift_normalization : ∀ E (n : ℤ),
    HEq ((family.Φ E).commShiftIso n) ((stage E).rational.functor.commShiftIso n)
  scalar_shift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (family.β h).hom ℤ
  ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    FdOrdinaryScalarTransport l Ω T h
  integral_scalar : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
        integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
          pbcAmbientScalarExtension l Ω T h ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T ⋙
        (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)
  integral_scalar_lift : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    ∃ c : (stage E).integral.functor ⋙
        pbcIntegralScalarExtension l Ω T dT.out iT.out h ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T ⋙
        (stage L).integral.functor,
      (∀ K, HEq (c.hom.app K).hom ((integral_scalar h).hom.app K)) ∧
      (∀ K (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((family.β h).hom.app K')
        ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app
            ((stage E).integral.functor.obj K) ≫
          (pbcStageLocalization l Ω T L).map (c.hom.app K)))
  chi : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((integral_scalar h).hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
        ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
      ((pbcAmbientScalarExtension l Ω T h).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map ((ordinary h).completion l Ω P.obj))

/-- Normalized integral lifts and coherent finite rational comparisons supply precisely
all fields of the recorded coefficient datum. Source: trace-definition final sentence
(blueprint: lem-fd-common-stage-comparison-descent).

Proof: retain every supplied finite and integral field. The tensor normalization
makes the finite rational equivalences linear. Apply steps 1--8 of the node,
as in fdCommonStageComparisonDescent, to their coherent stage family. Use its
pair equivalence, descended shift, exactness in both directions and linearity
for the remaining fields. The finite-representative scalar formula follows by
computing at that common field. No integral lift is constructed by this argument. -/
theorem fdNormalizedCommonStageDescent
    (C : FdFiniteCoefficientComparison l Ω T) :
    ∃ D : FdCoefficientComparison l Ω T,
      D.stage = C.stage ∧ D.family = C.family ∧
      HEq D.finite_shift C.finite_shift ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
        D.ordinary h = C.ordinary h ∧ D.integral_scalar h = C.integral_scalar h) := by
  sorry

section Pullback
variable {T} {U : Scheme.{u}} [IsNoetherian U]
  [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [iU : Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]

/-- The actual framework pullback and its specified scalar comparison determine
one stage-system morphism, whose descent is the actual common-stage pullback.
Source: trace-definition final sentence, common-stage comparison subclaim, step 9
(blueprint: lem-fd-common-stage-comparison-descent).

Proof: use the actual rational pullbacks and commonStagePullbackComparison.
Their tower equation follows from the integral scalar/pullback comparison
normalizations and scalar associators. The representative formula identifies
the descended functor with commonStageDerivedPullback by its uniqueness theorem.
The finite functors and all beta components fix the stage-system data uniquely. -/
theorem fdFrameworkPullbackFamily_existsUnique (h : U ≅ T) :
    ∃! F : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω U),
      (∀ E, HEq (F.Φ E) (rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom)) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (e : E ≤ L)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq ((F.β e).hom.app K)
          (commonStagePullbackComparison l Ω h.hom ⟨E, K⟩ L e).hom) ∧
      F.functor = commonStageDerivedPullback l Ω h.hom := by
  sorry

/-- A mixed scalar square descends to the actual composite pullbacks, with the
specified finite components and every compatible equation.
Source: trace-definition final sentence, common-stage comparison subclaim, steps 9--12
(blueprint: lem-fd-common-stage-comparison-descent).

Proof: form the two composite stage families. In the beta orientation their
comparisons are J_U(alpha_s) composed with inverse j_U, and inverse F_p(j_T)
composed with alpha_p. Rearranging the mixed square gives Hom.comm exactly.
Apply descNatTrans, whose components are finite-stage inclusions. Finite
invertibility makes every component invertible. The functorCompIso comparisons
identify its endpoints with the actual composite functors; the supplied sfPair
equality identifies the framework pullback. Naturality at a representative
uses the mixed square at both endpoints and finite-stage naturality. The
component formula also proves uniqueness. Identities, vertical composition,
whiskering and their equations descend componentwise; apply this to the
specified identity, composition, shift and scalar equations. -/
theorem fdMixedPullbackDescent
    (JU : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω U)
      (pbcScalarSystem l Ω U dU.out iU.out))
    (JT : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (pbcScalarSystem l Ω T dT.out iT.out))
    (h : U ≅ T)
    (F : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω U))
    (sfFinite : ∀ E, HEq (F.Φ E)
      (rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom))
    (sfBeta : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (e : E ≤ L)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
      HEq ((F.β e).hom.app K)
        (commonStagePullbackComparison l Ω h.hom ⟨E, K⟩ L e).hom)
    (sfPair : F.functor = commonStageDerivedPullback l Ω h.hom)
    (b : StageSystem.Morphism.Hom
      (JT.comp (pbcQbarPullFamily l Ω h.hom)) (F.comp JU))
    (hb : ∀ E, IsIso (b.τ E)) :
    ∃! B : JT.functor ⋙ pbcQbarCompletedPull l Ω h.hom ≅
        commonStageDerivedPullback l Ω h.hom ⋙ JU.functor,
      ∀ P : generalAlgebraicallyClosedConstructibleCategory l Ω T,
        HEq (B.hom.app P)
          (((pbcScalarSystem l Ω U dU.out iU.out).ι P.stage).map
            ((b.τ P.stage).app P.obj)) := by
  sorry

/-- Under the normalized finite lifts, mixed descent fills exactly the recorded
pullback datum, preserving every supplied finite comparison.
Source: trace-definition final sentence, common-stage comparison subclaim, step 12
(blueprint: lem-fd-common-stage-comparison-descent).

Proof: take the actual framework family of fdFrameworkPullbackFamily_existsUnique.
The assumed mixed square makes the finite rational components a compatible
transformation of the two actual composite families. Use fdMixedPullbackDescent
and the pair_functor equations of the coefficient data to supply the pair field.
Its component specification is pair_components. Retain the given finite data;
all remaining fields are precisely the recorded normalization equations. -/
theorem fdNormalizedPullbackDescent
    (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
    (h : U ≅ T) (finite : ∀ E, FdPullbackComparison l Ω CU CT h E)
    (F : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω U))
    (sfFinite : ∀ E, HEq (F.Φ E)
      (rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom))
    (sfBeta : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (e : E ≤ L)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
      HEq ((F.β e).hom.app K)
        (commonStagePullbackComparison l Ω h.hom ⟨E, K⟩ L e).hom)
    (sfPair : F.functor = commonStageDerivedPullback l Ω h.hom)
    (mixed : StageSystem.Morphism.Hom
      (CT.family.comp (pbcQbarPullFamily l Ω h.hom)) (F.comp CU.family))
    (components : ∀ E, HEq (mixed.τ E) (finite E).rational.hom) :
    ∃ D : FdPullbackSystem l Ω CU CT h,
      D.finite = finite ∧ D.sfFamily = F ∧ HEq D.mixed mixed := by
  sorry

end Pullback
end WeilConjectures
