/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusCohomologyRealization
import WeilConjectures.SixFunctors.FrobeniusCohomologyRationalCocycle
import WeilConjectures.SixFunctors.FrobeniusCohomologyCoefficientCocycle

/-! # Coefficient transport of the canonical cohomology representative formula

Source: Deligne, Weil II (1.1.10)--(1.1.14), common-stage coefficient recipe
(blueprint: lem-weil-frobenius-cohomology-realization-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w x y z t u' v'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
open CohomologyRealization
open AlgebraicallyClosedCoefficients (Index)
open GeneralAlgebraicallyClosedCoefficients (stageSystem)

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
set_option allowUnsafeReducibility true in
attribute [local reducible] DerivedCategory.fieldDerivedScalarExtension
  frobeniusCohomologyRealizedStage
  CohomologyRealization.rationalStage DerivedCategory.pointFdScalarExtension

set_option allowUnsafeReducibility true in
attribute [local irreducible] frobeniusCohomologyCoefficientExtension
  frobeniusCohomologyRationalFunctor frobeniusCohomologyRationalScalar
  operationStageTransitionIso frobeniusCoefficientTower DerivedCategory.fieldScalarTower

private theorem comparison_app
    {C₀ C₁ : Type u} [Category.{v} C₀] [Category.{v} C₁]
    {D₀ D₁ : Type w} [Category.{x} D₀] [Category.{x} D₁]
    {D : Type y} [Category.{z} D] {P : Sort t}
    (A : P → D₀ ⥤ D) (s r : P) (hs : s = r)
    (H₀ : C₀ ⥤ D₀) (H₁ : C₁ ⥤ D₁) (F : D₀ ⥤ D₁)
    (B : D₁ ⥤ D) (T : C₀ ⥤ C₁) (Z : C₀ ⥤ D₁)
    (e : F ⋙ B ≅ A s) (q₀ : H₀ ⋙ F ≅ Z) (q₁ : Z ≅ T ⋙ H₁) (K : C₀) :
    (Functor.isoWhiskerLeft H₀ (e ≪≫ eqToIso (congrArg A hs)).symm ≪≫
      (Functor.associator H₀ F B).symm ≪≫
      Functor.isoWhiskerRight (q₀ ≪≫ q₁) B ≪≫ Functor.associator T H₁ B).app K =
    eqToIso (congrArg (fun p ↦ (A p).obj (H₀.obj K)) hs.symm) ≪≫
      e.symm.app (H₀.obj K) ≪≫ B.mapIso (q₀.app K) ≪≫ B.mapIso (q₁.app K) := by
  subst r
  apply Iso.ext
  simp only [Iso.app_hom, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.mapIso_hom,
    Functor.map_comp, eqToIso.hom, eqToIso.inv, eqToHom_refl,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private theorem factorComparison_hom_app
    {C₀ C₁ : Type u} [Category.{v} C₀] [Category.{v} C₁]
    {D₀ D₁ : Type w} [Category.{x} D₀] [Category.{x} D₁]
    {D : Type y} [Category.{z} D]
    (H₀ : C₀ ⥤ D₀) (H₁ : C₁ ⥤ D₁) (F : D₀ ⥤ D₁)
    (A₀ : D₀ ⥤ D) (A₁ : D₁ ⥤ D) (T : C₀ ⥤ C₁)
    (p : F ⋙ A₁ ≅ A₀) (q : H₀ ⋙ F ≅ T ⋙ H₁) (K : C₀) :
    (Functor.isoWhiskerLeft H₀ p.symm ≪≫ (Functor.associator H₀ F A₁).symm ≪≫
      Functor.isoWhiskerRight q A₁ ≪≫ Functor.associator T H₁ A₁).hom.app K =
      p.inv.app (H₀.obj K) ≫ A₁.map (q.hom.app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp]

private theorem pasteComparisonCocycles
    {C₀ C₁ C₂ : Type u} [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    {D₀ D₁ D₂ : Type w} [Category.{x} D₀] [Category.{x} D₁] [Category.{x} D₂]
    {D : Type y} [Category.{z} D]
    (H₀ : C₀ ⥤ D₀) (H₁ : C₁ ⥤ D₁) (H₂ : C₂ ⥤ D₂)
    (T : C₀ ⥤ C₁) (U : C₁ ⥤ C₂) (V : C₀ ⥤ C₂) (a : T ⋙ U ≅ V)
    (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₂) (J : D₀ ⥤ D₂) (c : F ⋙ G ≅ J)
    (A₀ : D₀ ⥤ D) (A₁ : D₁ ⥤ D) (A₂ : D₂ ⥤ D)
    (p₀₁ : F ⋙ A₁ ≅ A₀) (p₁₂ : G ⋙ A₂ ≅ A₁) (p₀₂ : J ⋙ A₂ ≅ A₀)
    (q₀₁ : H₀ ⋙ F ≅ T ⋙ H₁) (q₁₂ : H₁ ⋙ G ≅ U ⋙ H₂)
    (q₀₂ : H₀ ⋙ J ≅ V ⋙ H₂)
    (hq : ∀ K, G.map (q₀₁.hom.app K) ≫ q₁₂.hom.app (T.obj K) ≫
      H₂.map (a.hom.app K) = c.hom.app (H₀.obj K) ≫ q₀₂.hom.app K)
    (hp : ∀ W, A₂.map (c.hom.app W) ≫ p₀₂.hom.app W =
      p₁₂.hom.app (F.obj W) ≫ p₀₁.hom.app W) (K : C₀) :
    (p₀₁.inv.app (H₀.obj K) ≫ A₁.map (q₀₁.hom.app K)) ≫
      (p₁₂.inv.app (H₁.obj (T.obj K)) ≫ A₂.map (q₁₂.hom.app (T.obj K))) ≫
      A₂.map (H₂.map (a.hom.app K)) =
    p₀₂.inv.app (H₀.obj K) ≫ A₂.map (q₀₂.hom.app K) := by
  have hn := p₁₂.inv.naturality (q₀₁.hom.app K)
  simp only [Functor.comp_map] at hn
  have hi : p₀₁.inv.app (H₀.obj K) ≫ p₁₂.inv.app (F.obj (H₀.obj K)) ≫
      A₂.map (c.hom.app (H₀.obj K)) = p₀₂.inv.app (H₀.obj K) := by
    apply (cancel_mono (p₀₂.hom.app (H₀.obj K))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hp]
    simp
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  rw [← A₂.map_comp, ← A₂.map_comp, hq, A₂.map_comp]
  rw [reassoc_of% hi]

private def ComparisonCoherent
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : Type u'} [Category.{v'} D] (S : StageSystem C) (R : ∀ i, C i ⥤ D)
    (b : ∀ (i j : I) (h : i ≤ j), R i ≅ S.T h ⋙ R j) : Prop :=
  ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
    (b i j h).hom.app X ≫ (b j k h').hom.app ((S.T h).obj X) ≫
      (R k).map ((S.assoc h h').hom.app X) = (b i k (h.trans h')).hom.app X

private theorem transportByComparison
    {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : Type u'} [Category.{v'} D] (S : StageSystem C) (R : ∀ i, C i ⥤ D)
    (b : ∀ (i j : I) (h : i ≤ j), R i ≅ S.T h ⋙ R j)
    (hb : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k) (X : C i),
      (b i j h).hom.app X ≫ (b j k h').hom.app ((S.T h).obj X) ≫
        (R k).map ((S.assoc h h').hom.app X) = (b i k (h.trans h')).hom.app X)
    (K M : S.PairCategory) (L N : I) (hK : K.stage ≤ L) (hM : M.stage ≤ L)
    (h : L ≤ N) (f : K.toStage hK ⟶ M.toStage hM) :
    (b K.stage N (hK.trans h)).hom.app K.obj ≫ (R N).map (S.tr h f) ≫
      (b M.stage N (hM.trans h)).inv.app M.obj =
    (b K.stage L hK).hom.app K.obj ≫ (R L).map f ≫
      (b M.stage L hM).inv.app M.obj := by
  have eK : (b K.stage L hK).app K.obj ≪≫ (b L N h).app (K.toStage hK) ≪≫
      (R N).mapIso ((S.assoc hK h).app K.obj) =
        (b K.stage N (hK.trans h)).app K.obj :=
    Iso.ext (hb K.stage L N hK h K.obj)
  have eM : (b M.stage L hM).app M.obj ≪≫ (b L N h).app (M.toStage hM) ≪≫
      (R N).mapIso ((S.assoc hM h).app M.obj) =
        (b M.stage N (hM.trans h)).app M.obj :=
    Iso.ext (hb M.stage L N hM h M.obj)
  change ((b K.stage N (hK.trans h)).app K.obj).hom ≫ (R N).map (S.tr h f) ≫
      ((b M.stage N (hM.trans h)).app M.obj).inv = _
  rw [← eK, ← eM]
  simp only [StageSystem.tr, Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, Category.comp_id]
  rw [← reassoc_of% (b L N h).hom.naturality f]
  simp only [Iso.hom_inv_id_app_assoc]

section AbstractFactors

variable {I : Type u'} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {B : I → Type w} [bCategory : ∀ i, Category.{x} (B i)]
  {D : Type y} [Category.{z} D] {S : StageSystem C}

private theorem factorDataComparison_app (d : FactorData (B := B) (D := D) S)
    (i j : I) (h : i ≤ j) (K : C i) :
    (factorDataComparison d i j h).hom.app K =
      (d.p i j h).inv.app ((d.H i).obj K) ≫ (d.A j).map ((d.q i j h).hom.app K) := by
  exact factorComparison_hom_app (d.H i) (d.H j) (d.F i j h)
    (d.A i) (d.A j) (S.T h) (d.p i j h) (d.q i j h) K

private theorem factorDataCoherence (d : FactorData (B := B) (D := D) S)
    (hq : factorRationalCocycle d) (hp : factorCoefficientCocycle d.toCoefficientData) :
    ComparisonCoherent S (factorDataStage d) (factorDataComparison d) := by
  intro i j k h h' K
  rw [factorDataComparison_app, factorDataComparison_app, factorDataComparison_app]
  unfold factorDataStage
  dsimp only [Functor.comp_map, Functor.comp_obj]
  exact pasteComparisonCocycles (d.H i) (d.H j) (d.H k)
    (S.T h) (S.T h') (S.T (h.trans h')) (S.assoc h h')
    (d.F i j h) (d.F j k h') (d.F i k (h.trans h')) (d.c i j k h h')
    (d.A i) (d.A j) (d.A k) (d.p i j h) (d.p j k h') (d.p i k (h.trans h'))
    (d.q i j h) (d.q j k h') (d.q i k (h.trans h')) (hq i j k h h')
    (factorCoefficientCocycle_app d.toCoefficientData hp i j k h h') K

end AbstractFactors

private abbrev factoredRealizedStage
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c₀ : Compactification Y₀.hom) (compact : Bool) (E : Index l Ω)
    : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber Y₀).left E ⥤
      @DerivedCategory (ModuleCat.{max u v} Ω) _ _ (HasDerivedCategory.standard _) :=
  factorDataStage (bCategory := coefficientDerivedCategoryFamily.{u, v} l Ω)
    (realizationParts D l hl Y₀ Ω c₀ compact) E

private abbrev realizedStageComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    (E L : Index l Ω) (h : E ≤ L) :
    factoredRealizedStage D l hl Y₀ Ω c₀ compact E ≅
      (stageSystem l Ω (D.geometricFiber Y₀).left).T h ⋙
        factoredRealizedStage D l hl Y₀ Ω c₀ compact L :=
  factorDataComparison (bCategory := coefficientDerivedCategoryFamily.{u, v} l Ω)
    (realizationParts D l hl Y₀ Ω c₀ compact) E L h

private theorem realizedStageComparison_app
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (L : Index l Ω) (h : K.stage ≤ L) :
    (realizedStageComparison D l hl Y₀ Ω c₀ compact K.stage L h).app K.obj =
      frobeniusCohomologyRealizedComparison D l hl Y₀ Ω c₀ compact K L h := by
  exact comparison_app
    (fun φ : AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage →+* Ω ↦
      frobeniusCohomologyCoefficientExtension.{u, v} φ)
    ((frobeniusCohomologyStageEmbedding l Ω L).comp
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h).toRingHom)
    (frobeniusCohomologyStageEmbedding l Ω K.stage)
    (frobeniusCohomologyStageEmbedding_comp l Ω K.stage L h)
    (CohomologyRealization.rationalStage l Ω D hl Y₀ c₀ compact K.stage)
    (CohomologyRealization.rationalStage l Ω D hl Y₀ c₀ compact L)
    (DerivedCategory.fieldDerivedScalarExtension
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h).toRingHom)
    (CohomologyRealization.coefficient l Ω L)
    ((stageSystem l Ω (D.geometricFiber Y₀).left).T h) _
    (frobeniusCoefficientTower
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h).toRingHom
      (frobeniusCohomologyStageEmbedding l Ω L))
    (Functor.isoWhiskerRight
      (frobeniusCohomologyRationalScalar D l hl
        (AlgebraicallyClosedCoefficients.Coefficient l Ω K.stage) Y₀ c₀ compact
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h))
      (DerivedCategory.pointFiniteDimensional
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L)).ι)
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (operationStageTransitionIso l Ω (D.geometricFiber Y₀).left K.stage L h).symm
        (frobeniusCohomologyRationalFunctor D l hl
          (AlgebraicallyClosedCoefficients.Coefficient l Ω L) Y₀ c₀ compact))
      (DerivedCategory.pointFiniteDimensional
        (AlgebraicallyClosedCoefficients.Coefficient l Ω L)).ι) K.obj

set_option allowUnsafeReducibility true in
attribute [local irreducible] frobeniusCohomologyRealizedStage factoredRealizedStage
  realizedStageComparison CohomologyRealization.rationalStage
  DerivedCategory.fieldDerivedScalarExtension CohomologyRealization.rationalComparison
  CohomologyRealization.coefficientComparison CohomologyRealization.fieldAssociator
  CohomologyRealization.scalarAssociator CohomologyRealization.coefficientRingComparison

private theorem realizedStageComparison_coherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    : ComparisonCoherent
      (stageSystem l Ω (D.geometricFiber Y₀).left)
      (factoredRealizedStage D l hl Y₀ Ω c₀ compact)
      (realizedStageComparison D l hl Y₀ Ω c₀ compact) := by
  unfold factoredRealizedStage realizedStageComparison
  exact factorDataCoherence (bCategory := coefficientDerivedCategoryFamily.{u, v} l Ω)
    (realizationParts D l hl Y₀ Ω c₀ compact)
    (CohomologyRealization.rationalComparison_cocycle l Ω D hl Y₀ c₀ compact)
    (CohomologyRealization.coefficientParts_cocycle l Ω)

/-- Enlarging the common coefficient field leaves the actual cohomology arrow unchanged.
This is an equality of specified arrows in D(Ω), before quotient descent; it asserts
neither the existence of a descended functor nor any Frobenius invertibility.

Source: Deligne, Weil II (1.1.10)--(1.1.14), common-stage coefficient recipe;
coefficient-enlargement step of frobeniusCohomologyQbarFunctor_existsUnique
(blueprint: lem-weil-frobenius-cohomology-realization-transport).

Proof: write the comparison as the composite of coefficient embedding equality,
inverse balanced tensor tower, realized rational cohomology scalar comparison,
and inverse operation-stage transition comparison. The point-fibre and operation
comparisons are natural in each stage morphism. For successive field extensions,
their tower equations identify the composite comparison with the direct one,
with the stage-system associator inserted. These equations follow on the integral
system models from naturality and pasting of the scalar adjunction units and
counits; scalar restriction and the total derived limit preserve them. The rational
comparison is their specified localization, so tensor induction proves the same
identities for all rational morphisms. The point comparison is the tensor
associativity map and has the same tower identity. For the final scalar-and-size
extension, double tensor induction and frobeniusCohomologyStageEmbedding_comp
identify both tower maps on a tensor a tensor b tensor m with multiplication
of the coefficient scalars. Substituting these two endpoint tower identities in
the displayed formula, expand StageSystem.tr into the inverse source associator,
extension of f, and target associator. Naturality moves f past the intermediate
comparison; each associator cancels with its inverse. The remaining composite is
exactly the formula at L. The argument includes repeated stages and zero objects;
no faithfulness of cohomology or choice of representative is used. -/
theorem frobeniusCohomologyRealization_transport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    (K M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (L N : Index l Ω) (hK : K.stage ≤ L) (hM : M.stage ≤ L) (h : L ≤ N)
    (f : K.toStage hK ⟶ M.toStage hM) :
    (frobeniusCohomologyRealizedComparison D l hl Y₀ Ω c₀ compact K N (hK.trans h)).hom ≫
        (frobeniusCohomologyRealizedStage D l hl Y₀ Ω c₀ compact N).map
          ((stageSystem l Ω (D.geometricFiber Y₀).left).tr h f) ≫
        (frobeniusCohomologyRealizedComparison D l hl Y₀ Ω c₀ compact M N
          (hM.trans h)).inv =
      (frobeniusCohomologyRealizedComparison D l hl Y₀ Ω c₀ compact K L hK).hom ≫
        (frobeniusCohomologyRealizedStage D l hl Y₀ Ω c₀ compact L).map f ≫
        (frobeniusCohomologyRealizedComparison D l hl Y₀ Ω c₀ compact M L hM).inv := by
  have ht := transportByComparison
    (stageSystem l Ω (D.geometricFiber Y₀).left)
    (factoredRealizedStage D l hl Y₀ Ω c₀ compact)
    (realizedStageComparison D l hl Y₀ Ω c₀ compact)
    (realizedStageComparison_coherence D l hl Y₀ Ω c₀ compact)
    K M L N hK hM h f
  simp only [← Iso.app_hom, ← Iso.app_inv, realizedStageComparison_app] at ht
  unfold factoredRealizedStage factorDataStage realizationParts coefficientParts
    coefficientDataOfFields coefficientDataWithCocycle
    CohomologyRealization.rationalStage at ht
  unfold frobeniusCohomologyRealizedStage
  dsimp only [Functor.comp_map, Functor.comp_obj] at ht ⊢
  exact ht

end WeilConjectures
