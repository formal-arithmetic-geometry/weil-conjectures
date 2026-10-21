/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.IntegralLineTensorComparisonDefinitions
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Paper.SfImmersionCompletedPullbackComparison
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Open reduction and the actual adjunctions

Source: Stacks Project, Tags 0GL1, 0E8I and 0941; agent adjunction-normalized
realization refinement (blueprint: lem-sf-open-reduction-adjunction-transport).
Natural numbers index the positive exponents n+1. Coefficients and sites have
independent universes. The canonical open operations are the existing constructions
in IntegralOpenReduction; its existence theorem is not used here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.OpenReductionAdjunctionTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (SX : CoefficientDerivedSystemCalculus l E X)

/-- Ambient representative normalization of the supplied r. This uses the existing
augmented presentations, but quantifies over all good complexes, without completeness.
The chain comparison is specified before evaluation and its components are the
canonical extension-summand tensor maps, hence commute with quotient transitions
and scalar-unit augmentations. Source: Stacks 0GL1, 0E8I and 0941
(blueprint: lem-sf-open-reduction-adjunction-transport). -/
def ExtensionModel (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U) (tensor : TensorComparison l E j o)
    (r : shriek l E j o ⋙ SX.reduction ≅ SU.reduction ⋙ J l E j o) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
    (hQ : integralOperationsGoodComplex l E U Q),
    ∃ (hJQ : integralOperationsGoodComplex l E X
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (C : CochainComplex (coefficientSequenceModules l E U) ℤ)
      (D : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (eC : SU.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj C)
      (eD : SX.reduction.obj (DerivedCategory.Q.obj
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q)) ≅ DerivedCategory.Q.obj D)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E U n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E U n).mapHomologicalComplex (.up ℤ)).obj Q)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj
            (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (f : D ≅ ((systemExtension l E j o).mapHomologicalComplex (.up ℤ)).obj C),
      CoefficientReductionPresentation l E U SU.toCoefficientDerivedSystemReduction
        Q hQ.1 C eC κC ∧
      AugmentedPresentation l E U SU Q C eC κC ∧
      CoefficientReductionPresentation l E X SX.toCoefficientDerivedSystemReduction
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q) hJQ.1 D eD κD ∧
      AugmentedPresentation l E X SX
        (((extension l E j o).mapHomologicalComplex (.up ℤ)).obj Q) D eD κD ∧
      (r.hom.app (DerivedCategory.Q.obj Q) ≫ (J l E j o).map eC.hom ≫
        (systemExtension l E j o).mapDerivedCategoryFactors.hom.app C =
      SX.reduction.map ((extension l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        eD.hom ≫ DerivedCategory.Q.map f.hom) ∧
      (∀ (n : ℕ) (i : ℤ),
        (coefficientSequenceEvaluation l E X n).map (f.hom.f i) ≫
          (extensionEvaluation l E j o n).hom.app (C.X i) ≫
          (finiteExtension l E j o n).map ((κC n).hom.f i) =
        (κD n).hom.f i ≫ (tensor.ordinary n).hom.app (Q.X i))

/-- Actual finite localized adjunction, including the coefficient equivalence.
Source: Stacks 03DI--03DJ
(blueprint: lem-sf-open-reduction-adjunction-transport). -/
def finiteAdjunction (n : ℕ) :
    finiteExtension l E j o n ⊣ finiteRestriction l E j o n :=
  (o.finite n).toAdjunction.comp
    (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
      (rings l E X n) (openObject j))

/-- The canonical restriction tensor map is the open-adjunction mate of the
inverse canonical extension tensor map. This formula uses the actual finite unit
and integral counit; on the open it sends x tensor a to that same restricted tensor.
Source: Stacks 0E8I, 03DJ
(blueprint: lem-sf-open-reduction-adjunction-transport). -/
def restrictionTensorComponent (tensor : TensorComparison l E j o) (n : ℕ)
    (M : scalarReductionSource l E X) :
    (scalarReductionExtension l E U n).obj ((restriction l E j o).obj M) ⟶
      (finiteRestriction l E j o n).obj ((scalarReductionExtension l E X n).obj M) :=
  (finiteAdjunction l E j o n).unit.app _ ≫
    (finiteRestriction l E j o n).map
      ((tensor.ordinary n).inv.app ((restriction l E j o).obj M)) ≫
    (finiteRestriction l E j o n).map
      ((scalarReductionExtension l E X n).map ((ordinaryAdjunction l E j o).counit.app M))

/-- The canonical evaluation comparison for actual system restriction, transported
through the fixed coefficient equivalences. Its formula retains both equivalence
units/counits and the recorded open-system evaluation map.
Source: Stacks 03DJ, 0941
(blueprint: lem-sf-open-reduction-adjunction-transport). -/
def restrictionEvaluationComponent (n : ℕ) (N : coefficientSequenceModules l E X) :
    (coefficientSequenceEvaluation l E U n).obj ((systemRestriction l E j o).obj N) ≅
      (finiteRestriction l E j o n).obj ((coefficientSequenceEvaluation l E X n).obj N) :=
  (o.finite n).unitIso.app _ ≪≫
    (o.finite n).inverse.mapIso
      ((o.transportEvaluation n).app ((systemRestriction l E j o).obj N)).symm ≪≫
    (o.finite n).inverse.mapIso
      ((SemilinearSections.evaluation.{t+1, t, max u (t+1)}
        ((ProEt.topology X).over (openObject j))
        (fun k ↦ (rings l E X k).over (openObject j))
        (fun k ↦ ((ProEt.topology X).overPullback CommRingCat.{max u (t+1)}
          (openObject j)).map (transitions l E X k)) n).mapIso
        (o.systems.counitIso.app _)) ≪≫
    (o.finite n).inverse.mapIso ((o.openSystems.restrictionEvaluation n).app N)

/-- Restrict the quotient tensor models simultaneously. Augmented presentations
fix the actual scalar units, and the last square fixes the finite components by
the canonical restriction tensor map. The preceding square localizes a single
strict chain isomorphism, rather than asserting equality detected by evaluations.
Source: Stacks 03DJ, 06YY, 0941
(blueprint: lem-sf-open-reduction-adjunction-transport). -/
def RestrictionModel (tensor : TensorComparison l E j o)
    (s : star l E j o ⋙ SU.reduction ≅ SX.reduction ⋙ P l E j o) : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : integralOperationsGoodComplex l E X Q),
    ∃ (hRes : integralOperationsGoodComplex l E U
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (CX : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (CU : CochainComplex (coefficientSequenceModules l E U) ℤ)
      (eX : SX.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj CX)
      (eU : SU.reduction.obj (DerivedCategory.Q.obj
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q)) ≅ DerivedCategory.Q.obj CU)
      (κX : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj CX ≅
          ((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj Q)
      (κU : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E U n).mapHomologicalComplex (.up ℤ)).obj CU ≅
          ((scalarReductionExtension l E U n).mapHomologicalComplex (.up ℤ)).obj
            (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q))
      (f : CU ≅ ((systemRestriction l E j o).mapHomologicalComplex (.up ℤ)).obj CX),
      CoefficientReductionPresentation l E X SX.toCoefficientDerivedSystemReduction
        Q hQ.1 CX eX κX ∧
      AugmentedPresentation l E X SX Q CX eX κX ∧
      CoefficientReductionPresentation l E U SU.toCoefficientDerivedSystemReduction
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) hRes.1 CU eU κU ∧
      AugmentedPresentation l E U SU
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) CU eU κU ∧
      (SU.reduction.map ((restriction l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        eU.hom ≫ DerivedCategory.Q.map f.hom =
      s.hom.app (DerivedCategory.Q.obj Q) ≫ (P l E j o).map eX.hom ≫
        (systemRestriction l E j o).mapDerivedCategoryFactors.hom.app CX) ∧
      (∀ (n : ℕ) (i : ℤ),
        (coefficientSequenceEvaluation l E U n).map (f.hom.f i) ≫
          (restrictionEvaluationComponent l E j o n (CX.X i)).hom ≫
          (finiteRestriction l E j o n).map ((κX n).hom.f i) =
        (κU n).hom.f i ≫ restrictionTensorComponent l E j o tensor n (Q.X i))

/-- Normalization of the actual completion comparison, including every positive
finite projection, on a restricted representative of a complete object.
The projection is the already defined first Roos-coordinate projection; no new
limit identification is chosen. Source: Stacks 08TC, 0941; immersion comparison
(blueprint: lem-sf-open-reduction-adjunction-transport). -/
def CompletionModel : Prop :=
  ∀ (Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (_hQ : integralOperationsGoodComplex l E X Q)
    (_hc : complete l E X (DerivedCategory.Q.obj Q))
    (hRes : IntegralOnSlice.Good l E U none
      (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q)),
    ((IntegralOnSlice.completionUnit l E U none).app
        ((star l E j o).obj (DerivedCategory.Q.obj Q)) ≫
      (IntegralOnSlice.completion l E U none).map
        ((restriction l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
      (IntegralOnSlice.completionComparison l E U none).hom.app ⟨_, hRes⟩ =
    (restriction l E j o).mapDerivedCategoryFactors.hom.app Q ≫
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E U none
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q))) ∧
    (∀ n : ℕ,
      (IntegralOnSlice.completionUnit l E U none).app
          ((star l E j o).obj (DerivedCategory.Q.obj Q)) ≫
        (IntegralOnSlice.completion l E U none).map
          ((restriction l E j o).mapDerivedCategoryFactors.hom.app Q) ≫
        (IntegralOnSlice.completionComparison l E U none).hom.app ⟨_, hRes⟩ ≫
        DerivedCategory.Q.map (integralLineRoosProjection l E U
          (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) n) =
      (restriction l E j o).mapDerivedCategoryFactors.hom.app Q ≫
        DerivedCategory.Q.map (((IntegralOnSlice.augmentation l E U none).app
          (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q)).app (op n)))

/-- Exactly the reconstruction assumptions of the node, on both schemes.
Source: the adjunction-normalized realization refinement
(blueprint: lem-sf-open-reduction-adjunction-transport). -/
structure Reconstruction : Prop where
  extension_complete : ∀ K, complete l E U K → complete l E X ((shriek l E j o).obj K)
  unit_U : ∀ K, complete l E U K → IsIso (SU.adjunction.unit.app K)
  unit_X : ∀ H, complete l E X H → IsIso (SX.adjunction.unit.app H)
  counit_U : ∀ N, IsNormalizedCoefficientSequence l E U N →
    IsIso (SU.adjunction.counit.app N)
  counit_X : ∀ N, IsNormalizedCoefficientSequence l E X N →
    IsIso (SX.adjunction.counit.app N)
  limit_U : ∀ N, IsNormalizedCoefficientSequence l E U N →
    complete l E U ((coefficientSequenceLimit l E U).obj N)
  limit_X : ∀ N, IsNormalizedCoefficientSequence l E X N →
    complete l E X ((coefficientSequenceLimit l E X).obj N)

/-- The pointwise definition of d, using the inverse of the actual unit.
Source: node's defining equation for d
(blueprint: lem-sf-open-reduction-adjunction-transport). -/
def d (r : shriek l E j o ⋙ SX.reduction ≅ SU.reduction ⋙ J l E j o)
    (h : Reconstruction l E j o SU SX) (K : (complete l E U).FullSubcategory) :=
  (coefficientSequenceLimit l E X).map (r.inv.app K.obj) ≫
    @inv _ _ _ _ (SX.adjunction.unit.app ((shriek l E j o).obj K.obj))
      (h.unit_X _ (h.extension_complete _ K.property))

/-- The pointwise definition of b, using the inverse of the actual unit.
Source: node's defining equation for b
(blueprint: lem-sf-open-reduction-adjunction-transport). -/
def b (s : star l E j o ⋙ SU.reduction ≅ SX.reduction ⋙ P l E j o)
    (H : (complete l E X).FullSubcategory)
    (h : IsIso (SU.adjunction.unit.app ((star l E j o).obj H.obj))) :=
  (coefficientSequenceLimit l E U).map (s.inv.app H.obj) ≫
    @inv _ _ _ _ (SU.adjunction.unit.app ((star l E j o).obj H.obj)) h

/-- Restriction, normalization and realization of the supplied canonical open comparison.
Source: Stacks 0GL1, 0E8I, 0941; agent adjunction-normalized realization refinement
(blueprint: lem-sf-open-reduction-adjunction-transport).

Proof, following the eight steps of the node:
1. Use lem-sf-open-semilinear-tensor-model on one flat-term K-flat representative
for the supplied r. Its generator and quotient squares are ExtensionModel.
2. Apply lem-sf-immersion-completed-pullback-comparison to the open immersion.
Restriction preserves completeness and the actual completion unit is invertible.
The ringed-topoi-derived-tensor-pullback lemma preserves good representatives.
Restrict each quotient tensor on that same representative; its identity-on-sections
maps commute with quotients and scalar units. Descend the resulting strict system
isomorphism to obtain s with RestrictionModel, retaining all finite projections.
3. The reduced unit composite sends x tensor a to that same section on the open.
The system open unit does the same. Their strict chain maps agree before localization.
4. For the counit both composites send [x] tensor a to x tensor a. The simultaneous
system adjunction of lem-coef-semilinear-derived-sections descends this equality.
5. Completeness makes the actual units invertible. Define d and b by the displayed
inverse-unit composites. Naturality of r, s and the unit gives naturality of d,b;
each factor is invertible, so the resulting natural transformations are isomorphisms.
6. The triangle identity gives R(u_A inverse)=e_(R A). Naturality of e with respect
to r then gives R(d_K) followed by r_K equal to e_(J R K).
7. Substitute b into the realized unit equation. Step 3 and functoriality reduce
it to naturality of the actual unit for the open unit eta_K.
8. Substitute d inverse into the realized counit equation. Step 4 reduces it to
naturality of that same unit for epsilon_H. All equations are in the strict-system
derived categories. No inference that evaluation detects equality is used. -/
theorem openReductionAdjunctionTransport
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    (h : Reconstruction l E j o SU SX)
    (r : shriek l E j o ⋙ SX.reduction ≅ SU.reduction ⋙ J l E j o)
    (tensor : TensorComparison l E j o)
    (hr : ExtensionModel l E j o SX SU tensor r) :
    ∃ (s : star l E j o ⋙ SU.reduction ≅ SX.reduction ⋙ P l E j o)
      (hc : ∀ H, complete l E X H → complete l E U ((star l E j o).obj H)),
      RestrictionModel l E j o SU SX tensor s ∧
      CompletionModel l E j o ∧
      (∀ (H : DerivedCategory (scalarReductionSource l E X)) (_hH : complete l E X H),
        IsIso ((IntegralOnSlice.completionUnit l E U none).app ((star l E j o).obj H))) ∧
      (∀ (K : DerivedCategory (scalarReductionSource l E U)) (_hK : complete l E U K),
        SU.reduction.map ((openAdjunction l E j o).unit.app K) ≫
          s.hom.app ((shriek l E j o).obj K) ≫ (P l E j o).map (r.hom.app K) =
        (systemAdjunction l E j o).unit.app (SU.reduction.obj K)) ∧
      (∀ (H : DerivedCategory (scalarReductionSource l E X)) (_hH : complete l E X H),
        SX.reduction.map ((openAdjunction l E j o).counit.app H) =
          r.hom.app ((star l E j o).obj H) ≫ (J l E j o).map (s.hom.app H) ≫
            (systemAdjunction l E j o).counit.app (SX.reduction.obj H)) ∧
      ∃ (di : (complete l E U).ι ⋙ SU.reduction ⋙ J l E j o ⋙
            coefficientSequenceLimit l E X ≅ (complete l E U).ι ⋙ shriek l E j o)
        (bi : (complete l E X).ι ⋙ SX.reduction ⋙ P l E j o ⋙
            coefficientSequenceLimit l E U ≅ (complete l E X).ι ⋙ star l E j o),
        (∀ K : (complete l E U).FullSubcategory,
          di.hom.app K = d l E j o SU SX r h K) ∧
        (∀ H : (complete l E X).FullSubcategory,
          bi.hom.app H = b l E j o SU SX s H (h.unit_U _ (hc _ H.property))) ∧
        (∀ K : (complete l E U).FullSubcategory,
          SX.reduction.map (di.hom.app K) ≫ r.hom.app K.obj =
            SX.adjunction.counit.app ((J l E j o).obj (SU.reduction.obj K.obj))) ∧
        (∀ K : (complete l E U).FullSubcategory,
          SU.adjunction.unit.app K.obj ≫
            (coefficientSequenceLimit l E U).map
              ((systemAdjunction l E j o).unit.app (SU.reduction.obj K.obj)) ≫
            (coefficientSequenceLimit l E U).map ((P l E j o).map (r.inv.app K.obj)) ≫
            bi.hom.app ⟨(shriek l E j o).obj K.obj, h.extension_complete _ K.property⟩ =
          (openAdjunction l E j o).unit.app K.obj) ∧
        (∀ H : (complete l E X).FullSubcategory,
          di.inv.app ⟨(star l E j o).obj H.obj, hc _ H.property⟩ ≫
            (coefficientSequenceLimit l E X).map ((J l E j o).map (s.hom.app H.obj)) ≫
            (coefficientSequenceLimit l E X).map
              ((systemAdjunction l E j o).counit.app (SX.reduction.obj H.obj)) ≫
            @inv _ _ _ _ (SX.adjunction.unit.app H.obj) (h.unit_X _ H.property) =
          (openAdjunction l E j o).counit.app H.obj) := by
  sorry

end WeilConjectures.OpenReductionAdjunctionTransport
