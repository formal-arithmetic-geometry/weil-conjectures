/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.IntegralLineTensorComparisonDefinitions
import Sheaf.Paper.CanonicalOpenRestrictionModel
import Sheaf.Paper.OpenRestrictionCompleteness

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

private def inverseUnitIso
    {I C D : Type*} [Category* I] [Category* C] [Category* D]
    {R : C ⥤ D} {L : D ⥤ C} (adj : R ⊣ L)
    (A : I ⥤ C) (B : I ⥤ D) (r : A ⋙ R ≅ B)
    (h : ∀ i, IsIso (adj.unit.app (A.obj i))) : B ⋙ L ≅ A := by
  letI (i : I) := h i
  refine NatIso.ofComponents
    (fun i ↦ L.mapIso (r.symm.app i) ≪≫ (asIso (adj.unit.app (A.obj i))).symm) ?_
  intro i k f
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.comp_map, asIso_inv]
  apply (cancel_mono (adj.unit.app (A.obj k))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hn := adj.unit.naturality (A.map f)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [hn, IsIso.inv_hom_id_assoc]
  rw [← L.map_comp, ← L.map_comp]
  exact congrArg L.map (r.inv.naturality f)

private theorem inverseUnitIso_normalization
    {I C D : Type*} [Category* I] [Category* C] [Category* D]
    {R : C ⥤ D} {L : D ⥤ C} (adj : R ⊣ L)
    (A : I ⥤ C) (B : I ⥤ D) (r : A ⋙ R ≅ B)
    (h : ∀ i, IsIso (adj.unit.app (A.obj i))) (i : I) :
    R.map ((inverseUnitIso adj A B r h).hom.app i) ≫ r.hom.app i =
      adj.counit.app (B.obj i) := by
  let := h i
  change R.map (L.map (r.inv.app i) ≫ inv (adj.unit.app (A.obj i))) ≫ _ = _
  rw [R.map_comp, Functor.map_inv, adj.inv_map_unit]
  have hn := adj.counit.naturality (r.inv.app i)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  have hn' := congrArg (fun f ↦ f ≫ r.hom.app i) hn
  simp only [Category.assoc, Iso.inv_hom_id_app] at hn'
  exact (Category.assoc _ _ _).trans
    (hn'.trans (Category.comp_id (adj.counit.app (B.obj i))))

private theorem realize_unit
    (h : Reconstruction l E j o SU SX)
    (r : shriek l E j o ⋙ SX.reduction ≅ SU.reduction ⋙ J l E j o)
    (s : star l E j o ⋙ SU.reduction ≅ SX.reduction ⋙ P l E j o)
    (hc : ∀ H, complete l E X H → complete l E U ((star l E j o).obj H))
    (hs : ∀ K, SU.reduction.map ((openAdjunction l E j o).unit.app K) ≫
      s.hom.app ((shriek l E j o).obj K) ≫ (P l E j o).map (r.hom.app K) =
        (systemAdjunction l E j o).unit.app (SU.reduction.obj K))
    (K : (complete l E U).FullSubcategory) :
    SU.adjunction.unit.app K.obj ≫
      (coefficientSequenceLimit l E U).map
        ((systemAdjunction l E j o).unit.app (SU.reduction.obj K.obj)) ≫
      (coefficientSequenceLimit l E U).map ((P l E j o).map (r.inv.app K.obj)) ≫
      b l E j o SU SX s
        ⟨(shriek l E j o).obj K.obj, h.extension_complete _ K.property⟩
        (h.unit_U _ (hc _ (h.extension_complete _ K.property))) =
      (openAdjunction l E j o).unit.app K.obj := by
  let L := coefficientSequenceLimit l E U
  have ht : (systemAdjunction l E j o).unit.app (SU.reduction.obj K.obj) ≫
      (P l E j o).map (r.inv.app K.obj) ≫
      s.inv.app ((shriek l E j o).obj K.obj) =
      SU.reduction.map ((openAdjunction l E j o).unit.app K.obj) := by
    rw [← hs K.obj]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [(P l E j o).map_id]
    simp only [Category.id_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Category.comp_id]
  let := h.unit_U _ (hc _ (h.extension_complete _ K.property))
  change _ ≫ L.map _ ≫ L.map _ ≫ (L.map _ ≫ inv _) = _
  simp only [← L.map_comp_assoc]
  rw [ht]
  apply (cancel_mono
    (SU.adjunction.unit.app ((star l E j o).obj ((shriek l E j o).obj K.obj)))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (SU.adjunction.unit.naturality ((openAdjunction l E j o).unit.app K.obj)).symm

private theorem completion_model : CompletionModel l E j o := by
  intro Q _hQ _hc hRes
  let F := restriction l E j o
  let a : (star l E j o).obj (DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q) :=
    F.mapDerivedCategoryFactors.app Q
  have hn := (IntegralOnSlice.completionUnit l E U none).naturality a.hom
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hn
  have hu := (IntegralOnSlice.completionUnit_existsUnique l E U none).exists.choose_spec
    ⟨(F.mapHomologicalComplex (.up ℤ)).obj Q, hRes⟩
  have he : (IntegralOnSlice.completionUnit l E U none).app
      ((star l E j o).obj (DerivedCategory.Q.obj Q)) ≫
      (IntegralOnSlice.completion l E U none).map a.hom ≫
      (IntegralOnSlice.completionComparison l E U none).hom.app
        ⟨(F.mapHomologicalComplex (.up ℤ)).obj Q, hRes⟩ =
      a.hom ≫ DerivedCategory.Q.map
        (IntegralOnSlice.roosUnit l E U none ((F.mapHomologicalComplex (.up ℤ)).obj Q)) := by
    erw [← Category.assoc, ← hn]
    simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj, Category.assoc] using
      congrArg (fun f ↦ a.hom ≫ f) (show
      (IntegralOnSlice.completionUnit l E U none).app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q)) ≫
        (IntegralOnSlice.completionComparison l E U none).hom.app
          ⟨(F.mapHomologicalComplex (.up ℤ)).obj Q, hRes⟩ = _ from hu)
  refine ⟨he, ?_⟩
  intro n
  have hp := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map
    (integralLineRoosProjection l E U ((F.mapHomologicalComplex (.up ℤ)).obj Q) n)) he
  simp only [Category.assoc] at hp
  have hproj : IntegralOnSlice.roosUnit l E U none
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      integralLineRoosProjection l E U ((F.mapHomologicalComplex (.up ℤ)).obj Q) n =
      ((IntegralOnSlice.augmentation l E U none).app
        ((F.mapHomologicalComplex (.up ℤ)).obj Q)).app (op n) := by
    unfold IntegralOnSlice.roosUnit integralLineRoosProjection
    rw [← Category.assoc, CochainComplex.mappingCocone.lift_fst]
    simp [IntegralOnSlice.productAugmentation]
  exact hp.trans (by
    rw [← Functor.map_comp]
    exact congrArg (fun f ↦ a.hom ≫ DerivedCategory.Q.map f) hproj)

private def restrictionMate
    (r : shriek l E j o ⋙ SX.reduction ≅ SU.reduction ⋙ J l E j o) :
    star l E j o ⋙ SU.reduction ⟶ SX.reduction ⋙ P l E j o :=
  (mateEquiv (openAdjunction l E j o) (systemAdjunction l E j o)
    (TwoSquare.mk _ _ _ _ r.inv)).natTrans

private theorem restrictionMate_unit
    (r : shriek l E j o ⋙ SX.reduction ≅ SU.reduction ⋙ J l E j o)
    (K : DerivedCategory (scalarReductionSource l E U)) :
    SU.reduction.map ((openAdjunction l E j o).unit.app K) ≫
      (restrictionMate l E j o SU SX r).app ((shriek l E j o).obj K) ≫
      (P l E j o).map (r.hom.app K) =
        (systemAdjunction l E j o).unit.app (SU.reduction.obj K) := by
  rw [← Category.assoc]
  rw [show SU.reduction.map ((openAdjunction l E j o).unit.app K) ≫
      (restrictionMate l E j o SU SX r).app ((shriek l E j o).obj K) =
      (systemAdjunction l E j o).unit.app (SU.reduction.obj K) ≫
        (P l E j o).map (r.inv.app K) from
    unit_mateEquiv (openAdjunction l E j o) (systemAdjunction l E j o)
      (TwoSquare.mk _ _ _ _ r.inv) K]
  simp [← Functor.map_comp]

private theorem restrictionMate_counit
    (r : shriek l E j o ⋙ SX.reduction ≅ SU.reduction ⋙ J l E j o)
    (H : DerivedCategory (scalarReductionSource l E X)) :
    SX.reduction.map ((openAdjunction l E j o).counit.app H) =
      r.hom.app ((star l E j o).obj H) ≫
        (J l E j o).map ((restrictionMate l E j o SU SX r).app H) ≫
        (systemAdjunction l E j o).counit.app (SX.reduction.obj H) := by
  rw [show (J l E j o).map ((restrictionMate l E j o SU SX r).app H) ≫
      (systemAdjunction l E j o).counit.app (SX.reduction.obj H) =
      r.inv.app ((star l E j o).obj H) ≫
        SX.reduction.map ((openAdjunction l E j o).counit.app H) from
    mateEquiv_counit (openAdjunction l E j o) (systemAdjunction l E j o)
      (TwoSquare.mk _ _ _ _ r.inv) H]
  simp

/-- Restriction, normalization and realization of the supplied canonical open comparison.
Source: Stacks 0GL1, 0E8I, 0941; agent adjunction-normalized realization refinement
(blueprint: lem-sf-open-reduction-adjunction-transport).

Proof: the canonical restriction model identifies s with the mate of r inverse.
The mate unit and counit equations give the two reduced adjunction equations.
Open restriction preserves completeness and makes its actual completion unit invertible.
Independently, naturality and the normalized representative completion comparison give
CompletionModel, including each Roos projection. Define di and bi pointwise by the inverse
actual units and r inverse or s inverse. Unit naturality proves naturality of these
isomorphisms. The adjunction triangle identity and counit naturality give reductionD.
For the realized unit, substitute bi and use the reduced unit equation; functoriality
and unit naturality cancel the final inverse unit. For the realized counit, substitute
di inverse, use the reduced counit equation and apply the same naturality argument.
All identities live in the derived categories of strict systems; no step infers
equality from the finite evaluations. -/
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
  classical
  obtain ⟨s, hmate, hmodel⟩ :
      ∃ s : star l E j o ⋙ SU.reduction ≅ SX.reduction ⋙ P l E j o,
        s.hom = restrictionMate l E j o SU SX r ∧
          RestrictionModel l E j o SU SX tensor s := by
    exact CanonicalOpenRestriction.canonicalOpenRestrictionModel l E j o SU SX r tensor hr
  obtain ⟨hc, hcompletion⟩ :
      ∃ hc : ∀ H, complete l E X H → complete l E U ((star l E j o).obj H),
        ∀ H, complete l E X H →
          IsIso ((IntegralOnSlice.completionUnit l E U none).app
            ((star l E j o).obj H)) := by
    have ht := OpenRestrictionCompleteness.openRestrictionComplete l E j o
    exact ⟨fun H hH ↦ (ht H hH).1, fun H hH ↦ (ht H hH).2⟩
  let di := inverseUnitIso SX.adjunction
    ((complete l E U).ι ⋙ shriek l E j o)
    ((complete l E U).ι ⋙ SU.reduction ⋙ J l E j o)
    (Functor.isoWhiskerLeft (complete l E U).ι r)
    (fun K ↦ h.unit_X _ (h.extension_complete _ K.property))
  let bi := inverseUnitIso SU.adjunction
    ((complete l E X).ι ⋙ star l E j o)
    ((complete l E X).ι ⋙ SX.reduction ⋙ P l E j o)
    (Functor.isoWhiskerLeft (complete l E X).ι s)
    (fun H ↦ h.unit_U _ (hc _ H.property))
  have hsu := restrictionMate_unit l E j o SU SX r
  have hsc := restrictionMate_counit l E j o SU SX r
  rw [← hmate] at hsu hsc
  refine ⟨s, hc, hmodel, completion_model l E j o, hcompletion,
    (fun K _ ↦ hsu K), (fun H _ ↦ hsc H), di, bi, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    rfl
  · intro H
    rfl
  · intro K
    exact inverseUnitIso_normalization SX.adjunction _ _ _ _ K
  · intro K
    exact realize_unit l E j o SU SX h r s hc hsu K
  · intro H
    let := h.unit_X H.obj H.property
    dsimp only [di, inverseUnitIso, NatIso.ofComponents_inv_app, Iso.trans_inv,
      Iso.symm_inv, Functor.mapIso_inv, asIso_hom, Iso.app_inv]
    change (SX.adjunction.unit.app _ ≫
      (coefficientSequenceLimit l E X).map (r.hom.app _)) ≫
      (coefficientSequenceLimit l E X).map ((J l E j o).map (s.hom.app H.obj)) ≫
      (coefficientSequenceLimit l E X).map
        ((systemAdjunction l E j o).counit.app (SX.reduction.obj H.obj)) ≫
      inv (SX.adjunction.unit.app H.obj) = _
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc]
    rw [← hsc H.obj]
    apply (cancel_mono (SX.adjunction.unit.app H.obj)).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (SX.adjunction.unit.naturality
      ((openAdjunction l E j o).counit.app H.obj)).symm

end WeilConjectures.OpenReductionAdjunctionTransport
