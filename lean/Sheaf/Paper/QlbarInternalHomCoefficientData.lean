/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.InternalScalarTensorComparison
public import Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Paper.DerivedInternalHomFilteredColimit
public import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Final
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.Paper.QlbarTailModuleColimit
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Sheaf.Paper.InternalSectionHomContinuityComparison
import Sheaf.Paper.InternalSectionHomComparisonData
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Paper.FiniteSubextensionsDirected
import Sheaf.Paper.CartesianCoefficients

/-! # Algebraic-closure coefficient comparison data and normalized roof

Source: Bhatt--Scholze 6.8.2, 6.8.14--6.8.15; Stacks 08J9 and 0A95
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).

The existing coefficient definitions, auxiliary lemmas and normalized roof are
kept together here. The comparison module publicly re-exports these declarations.
Their names, signatures, definition bodies and visibility are unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.braidedCategory
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralReductionSiteEssentiallySmall
attribute [local irreducible]
  AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.internalEvaluation
  CategoryTheory.derivedInternalHomOfUniverses
  AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor
  WeilConjectures.SfbHomFilteredColimit.comparison
  WeilConjectures.coefficientHomResolution
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
  AlgebraicGeometry.ProEtale.CondensedRing.derivedTensorHomAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.internalScalarTensorIso
  CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Functor.Monoidal.toLaxMonoidal
  CategoryTheory.Functor.Monoidal.toOplaxMonoidal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QlbarInternalHom

open ModuleObjectRingedComparison

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The actual evaluation transpose for any flat condensed coefficient inclusion.
Source: DAG displayed comparison; Bhatt--Scholze 6.8.14--6.8.15
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def evaluationComparison
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K L : DerivedCategory (Internal R X)) :
    (CondensedRing.internalScalarExtension a X).obj
        (((CondensedRing.derivedHom R X).obj (op K)).obj L) ⟶
      ((CondensedRing.derivedHom S X).obj
        (op ((CondensedRing.internalScalarExtension a X).obj K))).obj
          ((CondensedRing.internalScalarExtension a X).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction S
    ((CondensedRing.internalScalarExtension a X).obj K)).homEquiv _ _
      (((CondensedRing.internalScalarTensorIso a X).inv.app K).app
          (((CondensedRing.derivedHom R X).obj (op K)).obj L) ≫
        (CondensedRing.internalScalarExtension a X).map
          ((CondensedRing.derivedTensorHomAdjunction R K).counit.app L))

/-- Naturality for every flat condensed coefficient map and all derived morphisms.
Source: DAG naturality clause, Stacks 08J9
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: naturality of the scalar tensorator and both evaluation counits identifies
both evaluation transposes. Injectivity of the tensor-Hom adjunction gives equality. -/
theorem evaluationComparison_naturality
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K K' L L' : DerivedCategory (Internal R X)) (f : K' ⟶ K) (g : L ⟶ L') :
    (CondensedRing.internalScalarExtension a X).map
        (((CondensedRing.derivedHom R X).map f.op).app L ≫
          ((CondensedRing.derivedHom R X).obj (op K')).map g) ≫
        evaluationComparison X a K' L' =
      evaluationComparison X a K L ≫
        ((CondensedRing.derivedHom S X).map
          ((CondensedRing.internalScalarExtension a X).map f).op).app
            ((CondensedRing.internalScalarExtension a X).obj L) ≫
        ((CondensedRing.derivedHom S X).obj
          (op ((CondensedRing.internalScalarExtension a X).obj K'))).map
            ((CondensedRing.internalScalarExtension a X).map g) := by
  change _ ≫ internalScalarHom a K' L' = internalScalarHom a K L ≫ _
  exact internalScalarHom_naturality a K K' L L' f g

attribute [local irreducible] evaluationComparison

/-- The scalar internal-Hom adjunction is the unique isomorphism of right adjoints.
Its left-adjoint isomorphism is the unit-normalized tensor comparison above.
Source: DAG restriction formula, Stacks 08J9 and 07A4
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def scalarHomIso
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K : DerivedCategory (Internal R X)) :
    ((CondensedRing.derivedHom S X).obj
        (op ((CondensedRing.internalScalarExtension a X).obj K))) ⋙
        (Mod.comap (coefficientMap a X)).mapDerivedCategory ≅
      (Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙
        (CondensedRing.derivedHom R X).obj (op K) :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).comp
      (CondensedRing.derivedTensorHomAdjunction S
        ((CondensedRing.internalScalarExtension a X).obj K))).rightAdjointUniq
    (((CondensedRing.derivedTensorHomAdjunction R K).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))).ofNatIsoLeft
      ((CondensedRing.internalScalarTensorIso a X).app K))

attribute [local irreducible] scalarHomIso

private theorem scalarMate_restriction
    {C D : Type*} [Category C] [Category D]
    {T H : C ⥤ C} {S V : D ⥤ D} {F : C ⥤ D} {U : D ⥤ C}
    (t : T ⊣ H) (s : S ⊣ V) (a : F ⊣ U) (m : T ⋙ F ≅ F ⋙ S) (L : C) :
    a.unit.app (H.obj L) ≫
        U.map (s.homEquiv _ _ (m.inv.app (H.obj L) ≫ F.map (t.counit.app L))) ≫
        ((a.comp s).rightAdjointUniq ((t.comp a).ofNatIsoLeft m)).hom.app (F.obj L) =
      H.map (a.unit.app L) := by
  let a₁ := a.comp s
  let a₂ := (t.comp a).ofNatIsoLeft m
  let θ := a₁.rightAdjointUniq a₂
  have h (A : C) (B : D) (f : (F ⋙ S).obj A ⟶ B) :
      a₁.homEquiv A B f ≫ θ.hom.app B = a₂.homEquiv A B f := by
    rw [Adjunction.homEquiv_unit, Category.assoc, θ.hom.naturality,
      ← Category.assoc, Adjunction.unit_rightAdjointUniq_hom_app,
      ← Adjunction.homEquiv_unit]
  have hh := h (H.obj L) (F.obj L)
    (m.inv.app (H.obj L) ≫ F.map (t.counit.app L))
  dsimp only [a₁] at hh
  rw [Adjunction.comp_homEquiv] at hh
  change a.homEquiv _ _ (s.homEquiv _ _ _) ≫ θ.hom.app _ = _ at hh
  rw [a.homEquiv_unit] at hh
  trans a₂.homEquiv (H.obj L) (F.obj L)
    (m.inv.app (H.obj L) ≫ F.map (t.counit.app L))
  · simpa only [θ, a₁, Functor.id_obj, Category.assoc] using hh
  dsimp only [a₂]
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [Adjunction.comp_homEquiv]
  change t.homEquiv _ _ (a.homEquiv _ _ (F.map (t.counit.app L))) = _
  rw [a.homEquiv_unit]
  change t.homEquiv _ _ (a.unit.app _ ≫ (F ⋙ U).map (t.counit.app L)) = _
  rw [← a.unit.naturality, t.homEquiv_naturality_right]
  simp only [Functor.id_obj, Functor.id_map, ← t.homEquiv_symm_id,
    Equiv.apply_symm_apply, Category.id_comp]

/-- The restricted comparison is characterized by the scalar unit and evaluation.
Source: DAG restriction formula, Stacks 08J9 and 07A4
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: transpose through the scalar adjunction and both tensor-Hom adjunctions.
The defining mate of scalarHomIso cancels the strong tensorator. Both transposes
are evaluation followed by the scalar unit of L, giving the equality. -/
theorem evaluationComparison_restriction
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K L : DerivedCategory (Internal R X)) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app
        (((CondensedRing.derivedHom R X).obj (op K)).obj L) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map
        (evaluationComparison X a K L) ≫
      (scalarHomIso X a K).hom.app ((CondensedRing.internalScalarExtension a X).obj L) =
    ((CondensedRing.derivedHom R X).obj (op K)).map
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app L) := by
  delta scalarHomIso evaluationComparison
  exact scalarMate_restriction (CondensedRing.derivedTensorHomAdjunction R K)
    (CondensedRing.derivedTensorHomAdjunction S
      ((CondensedRing.internalScalarExtension a X).obj K))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    ((CondensedRing.internalScalarTensorIso a X).app K) L

/-- Continuity on every coefficient-small filtered index and every representative of K.
The existing exact section equivalence and evaluation-normalized Hom comparison identify
this with internal-sheaf continuity in the node, with functorial K-injective models.
Source: DAG continuity hypothesis, proof step 5; Stacks 08J9
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def Continuous (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : DerivedCategory (Internal (Profinite.continuousMapRingObj E) X)) : Prop :=
  ∀ (P : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ),
    Nonempty (DerivedCategory.Q.obj P ≅
      (forward (Profinite.continuousMapRingObj E) X).obj K) →
    ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
      WeilConjectures.SfbHomFilteredColimit.Continuous.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring (Profinite.continuousMapRingObj E) X) (I := I) P

/-- The small tail index, including E itself. Its projection is the actual inclusion.
Source: DAG proof step 1, Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def fields (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
  (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E

/-- The finite-free coefficient diagram, using the actual scalar-inclusion chain maps.
The degree-zero extension of the regular E-module is canonically the regular F-module.
Source: DAG proof steps 2--3; Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def coefficients (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ Modules (Profinite.continuousMapRingObj E) X :=
  coefficientComplexDiagram X ℓ
      ((HomologicalComplex.single (Internal (Profinite.continuousMapRingObj E) X)
          (ComplexShape.up ℤ) 0).obj
        (Mod.regular (padicSubfieldRingObj X ℓ E))) (fields ℓ E)
      (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
      (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom)) ⋙
    complexForward (Profinite.continuousMapRingObj E) X ⋙ HomologicalComplex.eval _ _ 0

/-- The cocone with the prescribed inclusions into the closure, in module sheaves.
Source: DAG proof step 3; Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def coefficientCocone (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Cocone (coefficients X ℓ E) :=
  (HomologicalComplex.eval _ _ 0).mapCocone
    ((complexForward (Profinite.continuousMapRingObj E) X).mapCocone
      (coefficientComplexCocone X ℓ
        ((HomologicalComplex.single (Internal (Profinite.continuousMapRingObj E) X)
          (ComplexShape.up ℤ) 0).obj
          (Mod.regular (padicSubfieldRingObj X ℓ E))) (fields ℓ E)
        (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
        (fun i ↦ leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))))

/-- The strict three-arrow colimit formula, for an actual coefficient-module cocone.
Source: DAG displayed formula, proof step 6; Bhatt--Scholze 6.8.14--6.8.15
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def StrictColimitFormula
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I]
    (T : I ⥤ WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u} J R)
    [HasColimit T] (c : Cocone T)
    (P L : CochainComplex
      (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u} J R) ℤ) : Prop :=
  Nonempty (IsColimit c) ∧
  QuasiIso (colimMap (Functor.whiskerLeft T
    (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L))) ∧
  WeilConjectures.SfbHomFilteredColimit.Normalized.{u + 1, u, u} J R P L
    (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L) ∧
  QuasiIso (colimit.post
    (T ⋙ WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
      ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L))
    (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)) ∧
  IsIso (colimit.post T
    (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
      ((WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).obj L))) ∧
  (∀ i, QuasiIso
    ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app
      (T.obj i))) ∧
  (∀ i, QuasiIso
    (WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L
      (T.obj i))) ∧
  QuasiIso
    ((WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app c.pt) ∧
  QuasiIso
    (WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L c.pt) ∧
  (colimit.post T
      (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
        ((WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).obj L)) ≫
        (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L).app
          (colimit T) =
    colimMap (Functor.whiskerLeft T
      (WeilConjectures.SfbHomFilteredColimit.comparison.{u + 1, u, u} J R P L)) ≫
        colimit.post T
          (WeilConjectures.SfbHomFilteredColimit.tensorFixed.{u + 1, u, u} J R
            ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L) ⋙
              WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P)) ∧
  (∀ i,
    (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).map
        ((WeilConjectures.SfbHomFilteredColimit.tensor.{u + 1, u, u} J R).map
          (c.ι.app i, 𝟙 L)) ≫
      WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L c.pt =
    WeilConjectures.SfbHomFilteredColimit.roofDenominator.{u + 1, u, u} J R P L
        (T.obj i) ≫
      (WeilConjectures.SfbHomFilteredColimit.homFixed.{u + 1, u, u} J R P).map
        ((WeilConjectures.SfbHomFilteredColimit.tensor.{u + 1, u, u} J R).map
          (c.ι.app i, 𝟙 ((WeilConjectures.coefficientHomResolution.{u, u + 1, u} J R).obj L))))

attribute [local irreducible] coefficients coefficientCocone complexForward
  StrictColimitFormula

/-- The strict formula on the given finite-field diagram and its specified closure vertex.
Source: DAG displayed three-arrow formula; Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
def ColimitFormula (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (P L : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ) : Prop :=
  StrictColimitFormula (Scheme.ProEt.topology X)
    (ring (Profinite.continuousMapRingObj E) X) (coefficients X ℓ E)
      (coefficientCocone X ℓ E) P L

/-- The tail is small, filtered and cofinal, and its stages are finite free.
Source: DAG proof steps 1--2, Bhatt--Scholze 6.8.2(2).
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: E is an initial tail object. Finite composita give common upper bounds;
EH shows cofinality above any finite field H. Transport through AsSmall. A finite
E-basis of F gives the finite free module isomorphism after inverse image; F=E
uses the rank-one identity. This is det-def-sfb-qlbar-condensed-subextensions and
sk-prop-sfb-cartesian-coefficients, without a geometric hypothesis on X. -/
theorem fieldDiagram (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsFiltered (AsSmall.{u + 1} (Under E)) ∧ (fields ℓ E).Final ∧
    ∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      ∃ d : ℕ, Nonempty
        (Mod.finiteFree (padicSubfieldRingObj X ℓ E) d ≅
          (Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
            (Mod.regular (padicSubfieldRingObj X ℓ F))) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · unfold fields
    infer_instance
  · intro F h
    exact ((cartesianCoefficients ℓ (𝟙 X)).2.2 E F h).2

attribute [local irreducible] completedSubfieldCocone ColimitFormula Continuous

private theorem regular_extension_iso
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ Y : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Y)]
    [∀ Y : C, PreservesColimitsOfSize.{0, 0} (tensorRight Y)]
    {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S]
    (a : R ⟶ S) [IsMonHom a] :
    ∃ q : (Mod.extendScalars a).obj (Mod.regular R) ≅ Mod.regular S,
      Mod.extendπ a (Mod.regular R) ≫ q.hom.hom = S ◁ a ≫ MonObj.mul := by
  let B := Bimod.ofMonHom a
  let e : ((Mod.extendScalars a).obj (Mod.regular R)).X ≅ S :=
    { hom := Bimod.RightUnitorBimod.hom B
      inv := Bimod.RightUnitorBimod.inv B
      hom_inv_id := Bimod.RightUnitorBimod.hom_inv_id B
      inv_hom_id := Bimod.RightUnitorBimod.inv_hom_id B }
  exact ⟨Mod.isoMk e (Bimod.RightUnitorBimod.hom_left_act_hom' B),
    coequalizer.π_desc _ _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem regular_extension_transition
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ Y : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Y)]
    [∀ Y : C, PreservesColimitsOfSize.{0, 0} (tensorRight Y)]
    {R S T : C} [MonObj R] [IsCommMonObj R] [MonObj S] [MonObj T]
    (f : R ⟶ S) [IsMonHom f] (g : R ⟶ T) [IsMonHom g]
    (a : S ⟶ T) [IsMonHom a] (h : f ≫ a = g)
    (q : (Mod.extendScalars f).obj (Mod.regular R) ≅ Mod.regular S)
    (q' : (Mod.extendScalars g).obj (Mod.regular R) ≅ Mod.regular T)
    (hq : Mod.extendπ f (Mod.regular R) ≫ q.hom.hom = S ◁ f ≫ MonObj.mul)
    (hq' : Mod.extendπ g (Mod.regular R) ≫ q'.hom.hom = T ◁ g ≫ MonObj.mul) :
    (Mod.mixedScalarMap f g f g a h h (Mod.regular R)).hom ≫ q'.hom.hom =
      q.hom.hom ≫ a := by
  apply (cancel_epi (Mod.extendπ f (Mod.regular R))).1
  erw [← Category.assoc, Mod.extendπ_mixedScalarMap, Category.assoc, hq']
  change a ▷ R ≫ T ◁ g ≫ MonObj.mul =
    Mod.extendπ f (Mod.regular R) ≫ q.hom.hom ≫ a
  rw [reassoc_of% hq, IsMonHom.mul_hom]
  rw [tensorHom_def']
  change a ▷ R ≫ T ◁ g ≫ MonObj.mul =
    S ◁ f ≫ (S ◁ a ≫ a ▷ T) ≫ MonObj.mul
  rw [← whisker_exchange_assoc]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, h]

set_option backward.isDefEq.respectTransparency false in
attribute [local semireducible] coefficients coefficientCocone complexForward in
/-- The complex-defined coefficient diagram has the actual regular field coefficients.
The identifications retain every field inclusion and the closure cocone legs.
Source: DAG coefficient diagram and proof steps 2--3, Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: extension of the regular E-module is the regular target module by
multiplication, s tensor e maps to s e. Its inverse sends s to s tensor 1.
Apply section reconstruction in degree zero. The actual mixedScalarMap and its
extend-pi formula give the transition and closure equations on these generators. -/
theorem coefficientModules (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ (stage : ∀ i : AsSmall.{u + 1} (Under E),
        (coefficients X ℓ E).obj i ≅ qlbarTailStage X ℓ
          (leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom)))
      (vertex : (coefficientCocone X ℓ E).pt ≅ qlbarTailVertex X ℓ E),
      (∀ (i j : AsSmall.{u + 1} (Under E)) (f : i ⟶ j) (V : X.ProEtᵒᵖ)
        (x : ((coefficients X ℓ E).obj i).val.obj V),
        (stage j).hom.val.app V (((coefficients X ℓ E).map f).val.app V x) =
          (padicSubfieldRingObjMap X ℓ (leOfHom ((fields ℓ E).map f))).hom.app V
            ((stage i).hom.val.app V x)) ∧
      (∀ (i : AsSmall.{u + 1} (Under E)) (V : X.ProEtᵒᵖ)
        (x : ((coefficients X ℓ E).obj i).val.obj V),
        vertex.hom.val.app V (((coefficientCocone X ℓ E).ι.app i).val.app V x) =
          (padicSubfieldRingObjToPadicAlgCl X ℓ ((fields ℓ E).obj i)).hom.app V
            ((stage i).hom.val.app V x)) := by
  classical
  unfold coefficients coefficientCocone
  let f (i : AsSmall.{u + 1} (Under E)) :=
    padicSubfieldRingObjMap X ℓ
      (leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
  choose q hq using fun i : AsSmall.{u + 1} (Under E) ↦ regular_extension_iso (f i)
  refine Exists.elim (regular_extension_iso
    (padicSubfieldRingObjToPadicAlgCl X ℓ E)) ?_
  intro qClosure hqClosure
  let stage (i : AsSmall.{u + 1} (Under E)) :
      (coefficients X ℓ E).obj i ≅ qlbarTailStage X ℓ
        (leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom)) :=
    (equivalence (Profinite.continuousMapRingObj E) X).functor.mapIso
      ((Mod.comap (f i)).mapIso (q i))
  let vertex : (coefficientCocone X ℓ E).pt ≅ qlbarTailVertex X ℓ E :=
    (equivalence (Profinite.continuousMapRingObj E) X).functor.mapIso
      ((Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapIso qClosure)
  refine ⟨stage, vertex, ?_, ?_⟩
  · intro i j a V x
    have h := regular_extension_transition (f i) (f j)
      (padicSubfieldRingObjMap X ℓ (leOfHom ((fields ℓ E).map a)))
      (coefficientComplex_ringMap_comp X ℓ _ _) (q i) (q j) (hq i) (hq j)
    exact congrArg (fun k ↦ k.hom.app V x) h
  · intro i V x
    have h := regular_extension_transition (f i)
      (padicSubfieldRingObjToPadicAlgCl X ℓ E)
      (padicSubfieldRingObjToPadicAlgCl X ℓ ((fields ℓ E).obj i))
      (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ _) (q i) qClosure (hq i) hqClosure
    exact congrArg (fun k ↦ k.hom.app V x) h

/-- The algebraic-closure cocone is also the ring-algebra colimit on the tail.
Source: DAG coefficient-colimit clause, Bhatt--Scholze 6.8.2(2)
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: fieldDiagram gives cofinality. Restrict completedSubfieldCocone along fields.
For a tail cocone extend its H-leg through EH. The full coefficient colimit yields
a unique map; its E-leg fixes the E-algebra structure, so it is the algebra colimit. -/
theorem coefficientRingColimit (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Nonempty (IsColimit ((completedSubfieldCocone X ℓ).whisker (fields ℓ E))) := by
  obtain ⟨h⟩ := completedCondensedAlgebraicClosure X ℓ
  unfold fields
  exact ⟨(Functor.Final.isColimitWhiskerEquiv _ (completedSubfieldCocone X ℓ)).symm h⟩

set_option backward.isDefEq.respectTransparency.types false

/-- Evaluation normalization of the internal-to-section Hom isomorphism.
This is precisely the equation in the recorded module-object comparison.
Source: DAG proof step 5, Stacks 08J9
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison). -/
@[no_expose] def HomTransportNormalized
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (S : WeilConjectures.CoefficientClosedStructure (hom R X))
    (T : WeilConjectures.CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring R X) S)
    (t : TensorComparison R X S T)
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom R X) ⋙ forward R X ≅
      ((forward R X).op.prod (forward R X)) ⋙ hom R X) : Prop :=
  -- Share the named evaluation map with `HomPresentation.evaluation`.
  ∀ K N : DerivedCategory (Internal R X),
    (forward R X).map (internalEvaluation R X K N) =
      t.iso.hom.app (((CondensedRing.derivedHom R X).obj (op K)).obj N, K) ≫
        S.tensor.map
          (X := ((forward R X).obj (((CondensedRing.derivedHom R X).obj (op K)).obj N),
            (forward R X).obj K))
          (Y := ((hom R X).obj (op ((forward R X).obj K), (forward R X).obj N),
            (forward R X).obj K))
          (θ.hom.app (op K, N), 𝟙 ((forward R X).obj K)) ≫
        S.evaluation ((forward R X).obj K) ((forward R X).obj N)

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_unit_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ C) (G : B ⥤ D) {E : A ⥤ B} {U : B ⥤ A}
    {E' : C ⥤ D} {U' : D ⥤ C} (adj : E ⊣ U) (adj' : E' ⊣ U')
    (ρ : U ⋙ F ≅ G ⋙ U') (γ : E ⋙ G ≅ F ⋙ E')
    (h : ∀ (K : A) (N : B) (f : E.obj K ⟶ N),
      F.map (adj.homEquiv K N f) ≫ ρ.hom.app N =
        adj'.homEquiv _ _ (γ.inv.app K ≫ G.map f)) (K : A) :
    F.map (adj.unit.app K) ≫ ρ.hom.app (E.obj K) ≫ U'.map (γ.hom.app K) =
      adj'.unit.app (F.obj K) := by
  have h' : F.map (adj.unit.app K) ≫ ρ.hom.app (E.obj K) =
      adj'.unit.app (F.obj K) ≫ U'.map (γ.inv.app K) := by
    simpa [Adjunction.homEquiv_unit] using h K (E.obj K) (𝟙 _)
  calc
    F.map (adj.unit.app K) ≫ ρ.hom.app (E.obj K) ≫ U'.map (γ.hom.app K) =
        (adj'.unit.app (F.obj K) ≫ U'.map (γ.inv.app K)) ≫ U'.map (γ.hom.app K) := by
      rw [← Category.assoc, h']
    _ = adj'.unit.app (F.obj K) := by
      rw [Category.assoc, ← U'.map_comp, Iso.inv_hom_id_app]
      exact (congrArg (fun f ↦ adj'.unit.app (F.obj K) ≫ f)
        (U'.map_id (E'.obj (F.obj K)))).trans (Category.comp_id _)

attribute [local semireducible] Functor.mapDerivedCategory

section ScalarRoof
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]

set_option hygiene false in
local notation "B" => CondensedRing.internalScalarExtension a X
set_option hygiene false in
local notation "U" => Mod.comap (coefficientMap a X)
set_option hygiene false in
local notation "b" => InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
  (Scheme.ProEt.topology X) (coefficientMap a X)

/-- The native evaluation transpose agrees with the normalized ringed evaluation roof.
The scalar unit fixes the extension transport, restriction fixes every section, and
both Hom transports preserve evaluation. The fixed roof supplies the strict numerator
and inverse denominator in coefficient_colimit_formula.
Source: DAG displayed formula and proof steps 5--6, Stacks 08J9 and 0A95
(blueprint: lem-sfb-qlbar-internal-hom-coefficient-comparison).
Proof: apply the section scalar-adjunction comparison to a. Localize its identity
restriction and generator-normalized extension. Choose simultaneous normalized ringed
closed and scalar models. The module-object tensor-Hom comparison supplies tR,tS and
the evaluation-normalized theta maps. The scalar-unit equation follows from equality
of the derived transposes. Transpose both sides of the final equation: the pure-tensor
normalizations give the same extended evaluation, hence the maps are equal. The
recorded flat evaluation-roof theorem provides the last roof data. -/
theorem coefficient_comparison_roof :
    letI : ∀ A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
        HasDerivedCategory.{u + 1}
          (SheafOfModules.scalarModules (Scheme.ProEt.topology X) A) :=
      fun A ↦ inferInstanceAs (HasDerivedCategory.{u + 1}
        (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
          (Scheme.ProEt.topology X) A))
    ∃ (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))
      (μ : ∀ {A D : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (f : A ⟶ D),
        ScalarHomTensorComparison.{u + 1, u, u, u + 1} M f)
      (α : ScalarInternalHomAdjunction.{u + 1, u, u, u + 1} M μ)
      (r : U ⋙ (equivalence R X).functor ≅
        (equivalence S X).functor ⋙ SheafOfModules.scalarRestriction.{u + 1, u, u + 1} b),
      (∀ (N : Internal S X) (V : X.ProEtᵒᵖ)
        (x : (((U ⋙ (equivalence R X).functor).obj N).val.obj V)),
        HEq ((r.hom.app N).val.app V x) x) ∧
      ∃ (γ : B ⋙ forward S X ≅ forward R X ⋙ (M.scalar b).derived)
        (ρ : (Mod.comap (coefficientMap a X)).mapDerivedCategory ⋙ forward R X ≅
          forward S X ⋙ SheafOfModules.scalarDerivedRestriction b)
        (tR : TensorComparison R X (M.closed (ring R X)) (M.model (ring R X)))
        (tS : TensorComparison S X (M.closed (ring S X)) (M.model (ring S X)))
        (θR : Functor.uncurry.obj (CondensedRing.derivedHom R X) ⋙ forward R X ≅
          ((forward R X).op.prod (forward R X)) ⋙ hom R X)
        (θS : Functor.uncurry.obj (CondensedRing.derivedHom S X) ⋙ forward S X ≅
          ((forward S X).op.prod (forward S X)) ⋙ hom S X),
        HomTransportNormalized X R (M.closed (ring R X)) (M.model (ring R X)) tR θR ∧
        HomTransportNormalized X S (M.closed (ring S X)) (M.model (ring S X)) tS θS ∧
        HEq ρ
          ((Functor.mapDerivedCategoryCompIso U (equivalence R X).functor).symm ≪≫
            Functor.mapDerivedCategoryNatIso r ≪≫
            Functor.mapDerivedCategoryCompIso (equivalence S X).functor
              (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} b)) ∧
        (∀ K : DerivedCategory (Internal R X),
          (forward R X).map
              ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).unit.app K) ≫
            ρ.hom.app ((CondensedRing.internalScalarExtension a X).obj K) ≫
            (SheafOfModules.scalarDerivedRestriction b).map (γ.hom.app K) =
          (M.scalar b).adjunction.unit.app ((forward R X).obj K)) ∧
        Nonempty (SfbFlatHom.EvaluationRoof.{u + 1, u, u, u + 1} M μ α) ∧
        ∀ K L : DerivedCategory (Internal R X),
          (forward S X).map (evaluationComparison X a K L) ≫
              θS.hom.app (op ((CondensedRing.internalScalarExtension a X).obj K),
                (CondensedRing.internalScalarExtension a X).obj L) ≫
              (hom S X).map (Prod.mkHom (γ.inv.app K).op (γ.hom.app L)) =
            γ.hom.app (((CondensedRing.derivedHom R X).obj (op K)).obj L) ≫
              (M.scalar b).derived.map (θR.hom.app (op K, L)) ≫
              SfbFlatHom.comparison.{u + 1, u, u, u + 1} M μ b
                ((forward R X).obj K) ((forward R X).obj L) := by
  dsimp only
  let : ∀ A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1},
      HasDerivedCategory.{u + 1}
        (SheafOfModules.scalarModules (Scheme.ProEt.topology X) A) :=
    fun A ↦ HasDerivedCategory.ofIsGrothendieckAbelian
      (WeilConjectures.SfbHomFilteredColimit.Modules.{u + 1, u, u}
        (Scheme.ProEt.topology X) A)
  refine Exists.elim (scalarInternalHomAdjunction_exists.{u + 1, u, u, u + 1}
    (J := Scheme.ProEt.topology X)) ?_
  intro M hM
  refine Exists.elim hM ?_
  intro μ hα
  refine Nonempty.elim hα ?_
  intro α
  refine Nonempty.elim
    (homPresentation_nonempty R X (M.closed (ring R X)) (M.model (ring R X))) ?_
  intro PR
  refine Nonempty.elim
    (homPresentation_nonempty S X (M.closed (ring S X)) (M.model (ring S X))) ?_
  intro PS
  refine Nonempty.elim (internal_section_hom_continuity_comparison X a M μ PR PS) ?_
  intro t
  refine ⟨M, μ, α, t.restriction, ?_, t.extension, t.derivedRestriction,
    PR.tensor, PS.tensor, PR.homIso, PS.homIso, PR.evaluation, PS.evaluation,
    ?_, ?_, SfbFlatHom.evaluationRoof M μ α, ?_⟩
  · intro N V x
    exact heq_of_eq (t.sections N V x)
  · set_option backward.isDefEq.respectTransparency.types true in
      have hh : t.derivedRestriction = _ := t.restrictionNormalization
      exact heq_of_eq hh
  · have hu := scalar_unit_transport (forward R X) (forward S X)
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
      (M.scalar b).adjunction t.derivedRestriction t.extension t.adjunction
    exact hu
  · intro K L
    simpa only [evaluationComparison, internalScalarHom, SfbFlatHom.comparison,
      WeilConjectures.coefficientBaseChangeHom] using t.hom K L

end ScalarRoof

end AlgebraicGeometry.ProEtale.QlbarInternalHom
