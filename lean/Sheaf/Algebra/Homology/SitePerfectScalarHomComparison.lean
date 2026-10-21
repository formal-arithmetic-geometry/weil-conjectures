/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor
import Sheaf.Algebra.Homology.RingedScalarTensorMonoidal
import Sheaf.CategoryTheory.RingedSitePerfectDualityForModel
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison

/-! # Evaluation-normalized scalar Hom comparison for a site-perfect source

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, lemma-dual-perfect-complex;
current blueprint lem-fix-operation-reduction.proof.md, paragraph 1.
(blueprint: lem-fix-site-perfect-scalar-hom).

The auxiliary data retain the existing scalar universal pair, fixed K-flat tensor
models, and Koszul symmetry. The comparison is constructed by the specified transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
attribute [local irreducible] SheafOfModules.monoidalCategory derivedInternalHomOfUniverses

namespace CategoryTheory

private abbrev coefficientMonoidalClosed
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (T : CoefficientClosedStructure H) (s : @SymmetricCategory A _ T.monoidal) :
    @MonoidalClosed A _ T.monoidal := by
  let _ := T.monoidal
  let _ := s
  exact ⟨fun P ↦ ⟨Prod.sectR (op P) A ⋙ H,
    (T.adjunction P).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight P).symm⟩⟩

private theorem coefficientDualComparison_eq
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (T : CoefficientClosedStructure H) (s : @SymmetricCategory A _ T.monoidal)
    (O : A) (u : T.monoidal.tensorUnit ≅ O) (P N : A) :
    letI := T.monoidal
    letI := s
    letI := coefficientMonoidalClosed T s
    (H.map (Prod.mkHom (𝟙 (op P)) u.hom) ▷ N) ≫
      ringedSiteDualEvaluationLeft T s O u P N =
        MonoidalClosed.ihomUnitTensorToIhom P N := by
  let _ := T.monoidal
  let _ := s
  let _ := coefficientMonoidalClosed T s
  let d := H.map (Prod.mkHom (𝟙 (op P)) u.hom)
  have hu : d ▷ P ≫ T.evaluation P O ≫ u.inv = T.evaluation P (𝟙_ A) := by
    have he := (T.adjunction P).counit.naturality u.hom
    change d ▷ P ≫ T.evaluation P O = T.evaluation P (𝟙_ A) ≫ u.hom at he
    rw [← Category.assoc, he]
    simp
  unfold ringedSiteDualEvaluationLeft ringedSiteDualEvaluation
  dsimp only [CoefficientClosedStructure.transpose]
  erw [← (T.adjunction P).homEquiv_naturality_left,
    ← (T.adjunction P).homEquiv_naturality_left]
  unfold MonoidalClosed.ihomUnitTensorToIhom MonoidalClosed.curry
  change (T.adjunction P).homEquiv _ _ _ =
    ((T.adjunction P).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight P).symm).homEquiv _ _ _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  congr 1
  dsimp only [CoefficientClosedStructure.tensor, tensor_map, tensorRight, curriedTensor,
    Functor.flip,
    BraidedCategory.tensorLeftIsoTensorRight, NatIso.ofComponents, Iso.symm_hom,
    coefficientMonoidalClosed, ihom.ev, ihom.adjunction, Adjunction.ofNatIsoLeft,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [id_tensorHom]
  change d ▷ N ▷ P ≫ (β_ (H.obj (op P, O)) N).hom ▷ P ≫
    (α_ N (H.obj (op P, O)) P).hom ≫ N ◁ T.evaluation P O ≫
      N ◁ u.inv ≫ (ρ_ N).hom =
    (β_ P (H.obj (op P, 𝟙_ A) ⊗ N)).inv ≫
      (α_ P (H.obj (op P, 𝟙_ A)) N).inv ≫
        ((β_ P (H.obj (op P, 𝟙_ A))).hom ≫ T.evaluation P (𝟙_ A)) ▷ N ≫ (λ_ N).hom
  rw [← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left,
    comp_whiskerRight_assoc, associator_naturality_middle_assoc]
  simp only [← whiskerLeft_comp, ← Category.assoc]
  rw [Category.assoc (d ▷ P) (T.evaluation P O) u.inv, hu]
  simp only [Category.assoc]
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  let e := T.evaluation P (𝟙_ A)
  change (β_ _ N).hom ▷ P ≫ (α_ N _ P).hom ≫ N ◁ e ≫ (ρ_ N).hom =
    (β_ _ P).hom ≫ (α_ P _ N).inv ≫ ((β_ P _).hom ≫ e) ▷ N ≫ (λ_ N).hom
  have hn : N ◁ e ≫ (ρ_ N).hom =
      (β_ N (_ ⊗ P)).hom ≫ e ▷ N ≫ (λ_ N).hom := by
    erw [← BraidedCategory.braiding_naturality_right_assoc,
      braiding_tensorUnit_right]
    simp
  rw [hn, BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]
  rw [BraidedCategory.braiding_tensor_left_hom]
  rw [comp_whiskerRight]
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, SymmetricCategory.symmetry_assoc]

private theorem closed_evaluation_both
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (T : CoefficientClosedStructure H) (P P' Q Q' : A)
    (a : P' ⟶ P) (b : Q ⟶ Q') :
    T.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op b)) (𝟙 P')) ≫
        T.evaluation P' Q' =
      T.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) a) ≫ T.evaluation P Q ≫ b := by
  have hb (K N N' : A) (n : N ⟶ N') :
      T.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op K)) n)) (𝟙 K)) ≫
        T.evaluation K N' = T.evaluation K N ≫ n := by
    simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
      Prod.sectR] using (T.adjunction K).counit.naturality n
  have hf : Prod.mkHom a.op b =
      Prod.mkHom a.op (𝟙 Q) ≫ Prod.mkHom (𝟙 (op P')) b := by simp
  have ht : Prod.mkHom
      (H.map (Prod.mkHom a.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) b)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) b)) (𝟙 P') := by simp
  rw [hf, H.map_comp, ht, T.tensor.map_comp, Category.assoc, hb,
    ← Category.assoc]
  have he : T.tensor.map (Prod.mkHom (H.map (Prod.mkHom a.op (𝟙 Q))) (𝟙 P')) ≫
      T.evaluation P' Q =
    T.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) a) ≫ T.evaluation P Q := by
    simpa [CoefficientClosedStructure.evaluation, CoefficientClosedStructure.tensor,
      Prod.sectR] using T.evaluation_naturality P P' Q a
  rw [he, Category.assoc]

private theorem closed_uncurry_naturality
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (T : CoefficientClosedStructure H) (X P P' Q Q' : A)
    (t : X ⟶ H.obj (op P, Q)) (a : P' ⟶ P) (b : Q ⟶ Q') :
    (T.transpose X P' Q').symm (t ≫ H.map (Prod.mkHom a.op b)) =
      T.tensor.map (Prod.mkHom (𝟙 X) a) ≫ (T.transpose X P Q).symm t ≫ b := by
  have hu (Y K N : A) (f : Y ⟶ H.obj (op K, N)) :
      (T.transpose Y K N).symm f =
        T.tensor.map (Prod.mkHom f (𝟙 K)) ≫ T.evaluation K N := by
    let _ := T.monoidal
    change (tensorRight K).map f ≫ T.evaluation K N = _
    simp [CoefficientClosedStructure.tensor]
  rw [hu, hu]
  have ht : Prod.mkHom (t ≫ H.map (Prod.mkHom a.op b)) (𝟙 P') =
      Prod.mkHom t (𝟙 P') ≫ Prod.mkHom (H.map (Prod.mkHom a.op b)) (𝟙 P') := by simp
  rw [ht, T.tensor.map_comp, Category.assoc, closed_evaluation_both]
  have ht' : Prod.mkHom t (𝟙 P') ≫ Prod.mkHom (𝟙 (H.obj (op P, Q))) a =
      Prod.mkHom (𝟙 X) a ≫ Prod.mkHom t (𝟙 P) := by simp
  rw [← Category.assoc, ← Category.assoc, ← T.tensor.map_comp, ht', T.tensor.map_comp]
  simp only [Category.assoc]

private def coefficientSourceEvaluation
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (T : CoefficientClosedStructure H) (s : @SymmetricCategory A _ T.monoidal)
    (P Q : A) : T.tensor.obj (P, H.obj (op P, Q)) ⟶ Q :=
  (s.braiding P (H.obj (op P, Q))).hom ≫ T.evaluation P Q

private def coefficientHomComparison
    {A B : Type*} [Category A] [Category B]
    {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
    (T : CoefficientClosedStructure H) (S : CoefficientClosedStructure I)
    (s : @SymmetricCategory A _ T.monoidal) (t : @SymmetricCategory B _ S.monoidal)
    (F : A ⥤ B) (μ : T.tensor ⋙ F ≅ F.prod F ⋙ S.tensor)
    (P Q : A) : F.obj (H.obj (op P, Q)) ⟶ I.obj (op (F.obj P), F.obj Q) :=
  S.transpose _ (F.obj P) (F.obj Q)
    ((t.braiding (F.obj (H.obj (op P, Q))) (F.obj P)).hom ≫
      μ.inv.app (P, H.obj (op P, Q)) ≫ F.map (coefficientSourceEvaluation T s P Q))

private theorem coefficientHomComparison_naturality
    {A B : Type*} [Category A] [Category B]
    {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
    (T : CoefficientClosedStructure H) (S : CoefficientClosedStructure I)
    (s : @SymmetricCategory A _ T.monoidal) (t : @SymmetricCategory B _ S.monoidal)
    (F : A ⥤ B) (μ : T.tensor ⋙ F ≅ F.prod F ⋙ S.tensor)
    (P P' Q Q' : A) (a : P' ⟶ P) (b : Q ⟶ Q') :
    coefficientHomComparison T S s t F μ P Q ≫
        I.map (Prod.mkHom (F.map a).op (F.map b)) =
      F.map (H.map (Prod.mkHom a.op b)) ≫ coefficientHomComparison T S s t F μ P' Q' := by
  let _ := T.monoidal
  let _ := S.monoidal
  let _ := s
  let _ := t
  let HR := H
  let h := HR.map (Prod.mkHom a.op b)
  apply (S.transpose _ (F.obj P') (F.obj Q')).symm.injective
  rw [closed_uncurry_naturality]
  rw [show (S.transpose _ (F.obj P') (F.obj Q')).symm
      (F.map h ≫ coefficientHomComparison T S s t F μ P' Q') =
      (tensorRight (F.obj P')).map (F.map h) ≫
        (S.transpose _ (F.obj P') (F.obj Q')).symm
          (coefficientHomComparison T S s t F μ P' Q') from
    (S.adjunction (F.obj P')).homEquiv_naturality_left_symm
      (F.map h) (coefficientHomComparison T S s t F μ P' Q')]
  dsimp only [h, HR]
  simp only [coefficientHomComparison, Equiv.symm_apply_apply]
  dsimp only [CoefficientClosedStructure.tensor, tensor_map]
  simp only [id_tensorHom, tensorRight, curriedTensor, Functor.flip,
    Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_naturality_left_assoc]
  congr 1
  have hn₁ : F.map a ▷ F.obj (HR.obj (op P, Q)) ≫
      μ.inv.app (P, HR.obj (op P, Q)) =
      μ.inv.app (P', HR.obj (op P, Q)) ≫
        F.map (a ▷ HR.obj (op P, Q)) := by
    have hn := μ.inv.naturality (Prod.mkHom a (𝟙 (HR.obj (op P, Q))))
    dsimp only [Functor.comp_map, Functor.prod_map,
      CoefficientClosedStructure.tensor, tensor_map] at hn
    simp only [Functor.map_id] at hn
    erw [@tensorHom_id _ _ S.monoidal _ _ (F.map a)
      (F.obj (HR.obj (op P, Q)))] at hn
    simpa only [tensorHom_id] using hn
  have hn₂ : F.obj P' ◁ F.map h ≫
      μ.inv.app (P', HR.obj (op P', Q')) =
      μ.inv.app (P', HR.obj (op P, Q)) ≫ F.map (P' ◁ h) := by
    have hn := μ.inv.naturality (Prod.mkHom (𝟙 P') h)
    dsimp only [Functor.comp_map, Functor.prod_map,
      CoefficientClosedStructure.tensor, tensor_map] at hn
    simp only [Functor.map_id] at hn
    erw [@id_tensorHom _ _ S.monoidal (F.obj P') _ _
      (F.map h)] at hn
    simpa only [id_tensorHom] using hn
  erw [← Category.assoc, hn₁, Category.assoc, ← F.map_comp,
    ← F.map_comp]
  conv_rhs => erw [← Category.assoc, hn₂, Category.assoc, ← F.map_comp]
  congr 1
  congr 1
  dsimp only [coefficientSourceEvaluation, CoefficientClosedStructure.tensor, tensor_map]
  simp only [Category.assoc]
  dsimp only [HR, h]
  erw [BraidedCategory.braiding_naturality_left_assoc,
    BraidedCategory.braiding_naturality_right_assoc]
  congr 1
  simpa only [CoefficientClosedStructure.tensor, tensor_map,
    @tensorHom_id _ _ T.monoidal,
    @id_tensorHom _ _ T.monoidal] using
    (closed_evaluation_both T P P' Q Q' a b).symm

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J S)]

/-- The canonical ordinary scalar tensor formula on pure generators, before localization.
Source: Stacks 07A4; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def SiteScalarHomGeneratorFormula
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ)
    (κ : coefficientTotalTensor.{r, c, v} J R ⋙ D.E.mapHomologicalComplex (.up ℤ) ≅
      (D.E.mapHomologicalComplex (.up ℤ)).prod (D.E.mapHomologicalComplex (.up ℤ)) ⋙
        coefficientTotalTensor.{r, c, v} J S) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
      (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      ((κ.hom.app (P, Q)).f (p + q)).val.app U
        (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq
          (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
          U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
            P Q p q (p + q) rfl U x y)) =
      WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
        ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
        (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (P.X p) U 1 x)
        (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (Q.X q) U 1 y)

/-- The canonical derived tensor comparison is fixed by its K-flat counit square.
This is the same representative characterization as ringed-topos tensor pullback.
Source: Stacks 07A4; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def SiteScalarHomTensorNormalization
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ)
    (AR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (AS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (MR : CoefficientTensorModels.{r, c, v, w} J R AR)
    (MS : CoefficientTensorModels.{r, c, v, w} J S AS)
    (κ : coefficientTotalTensor.{r, c, v} J R ⋙ D.E.mapHomologicalComplex (.up ℤ) ≅
      (D.E.mapHomologicalComplex (.up ℤ)).prod (D.E.mapHomologicalComplex (.up ℤ)) ⋙
        coefficientTotalTensor.{r, c, v} J S)
    (μ : AR.tensor ⋙ D.T ≅ D.T.prod D.T ⋙ AS.tensor) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
      ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
        D.T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
            μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            AS.tensor.map (Prod.mkHom (D.ε.app P) (D.ε.app Q)) =
          D.ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
            DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
            (MS.iso J S AS _ _ hEP hEQ).hom

attribute [local irreducible] SiteScalarHomGeneratorFormula SiteScalarHomTensorNormalization

/-- A presentation of the actual scalar and tensor operations used in the Hom map.
The final two fields are exactly the canonical pure-tensor and K-flat counit squares
of the published scalar tensor comparison, with no finite-free hypothesis on S.
These data are existential conclusions of the main theorem, not extra hypotheses.
Source: Stacks 07A4, 08J9 and 08JJ; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
structure SitePerfectScalarHomData where
  /-- The existing universal derived change of rings, with actual ordinary extension. -/
  scalar : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ
  /-- The closed structure with the fixed derived internal Hom over R. -/
  sourceClosed : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- The closed structure with the fixed derived internal Hom over S. -/
  targetClosed : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S)
  /-- Its actual K-flat tensor and Hom-evaluation normalization over R. -/
  sourceModel : CoefficientTensorModels.{r, c, v, w} J R sourceClosed
  /-- Its actual K-flat tensor and Hom-evaluation normalization over S. -/
  targetModel : CoefficientTensorModels.{r, c, v, w} J S targetClosed
  /-- The symmetry over R. -/
  sourceSymmetry : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ sourceClosed.monoidal
  /-- The symmetry over S. -/
  targetSymmetry : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J S))
    _ targetClosed.monoidal
  /-- The source symmetry is the Koszul symmetry and its unit is R in degree zero. -/
  sourceCoherence : RingedDerivedTensorCoherence.{c, v, r, w} J R
    sourceClosed sourceModel sourceSymmetry
  /-- The target symmetry is the Koszul symmetry and its unit is S in degree zero. -/
  targetCoherence : RingedDerivedTensorCoherence.{c, v, r, w} J S
    targetClosed targetModel targetSymmetry
  /-- The ordinary total-tensor scalar comparison. -/
  complexIso : coefficientTotalTensor.{r, c, v} J R ⋙
      scalar.E.mapHomologicalComplex (.up ℤ) ≅
    (scalar.E.mapHomologicalComplex (.up ℤ)).prod
      (scalar.E.mapHomologicalComplex (.up ℤ)) ⋙ coefficientTotalTensor.{r, c, v} J S
  /-- The derived comparison t: F(P tensor Q) = FP tensor FQ. -/
  tensorIso : sourceClosed.tensor ⋙ scalar.T ≅ scalar.T.prod scalar.T ⋙ targetClosed.tensor
  /-- The ordinary comparison is fixed on sheafified pure tensor generators. -/
  generators : SiteScalarHomGeneratorFormula J φ scalar complexIso
  /-- The derived comparison is the localization of this same chain comparison. -/
  normalization : SiteScalarHomTensorNormalization J φ scalar sourceClosed targetClosed
    sourceModel targetModel complexIso tensorIso

variable (M : SitePerfectScalarHomData.{c, v, r, w} J φ)

/-- The evaluation P tensor RHom(P,Q) to Q in the tensor order of the node.
It is the recorded counit preceded by the canonical Koszul symmetry.
Source: Stacks 08J9 and 08JJ; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def siteScalarHomSourceEvaluation
    (P Q : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    M.sourceClosed.tensor.obj
      (P, (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ⟶ Q :=
  (M.sourceSymmetry.braiding P
    ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q))).hom ≫
      M.sourceClosed.evaluation P Q

/-- The canonical comparison is the left tensor-Hom transpose of F(evaluation) after
inverse tensor comparison. The leading target symmetry converts the published
Hom-tensor-P adjunction into the P-tensor-Hom adjunction, with no choice of map.
Source: Stacks 08JJ and 07A4; blueprint proof paragraph 1
(blueprint: lem-fix-site-perfect-scalar-hom). -/
def siteScalarHomComparison
    (P Q : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    M.scalar.T.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op (M.scalar.T.obj P), M.scalar.T.obj Q) :=
  M.targetClosed.transpose _ (M.scalar.T.obj P) (M.scalar.T.obj Q)
    ((M.targetSymmetry.braiding
      (M.scalar.T.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)))
      (M.scalar.T.obj P)).hom ≫
        M.tensorIso.inv.app
          (P, (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ≫
        M.scalar.T.map (siteScalarHomSourceEvaluation J φ M P Q))


private theorem siteScalarHomComparison_evaluation
    (P Q : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    M.targetClosed.tensor.map (Prod.mkHom (𝟙 (M.scalar.T.obj P))
        (siteScalarHomComparison J φ M P Q)) ≫
      (M.targetSymmetry.braiding (M.scalar.T.obj P)
        ((derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
          (op (M.scalar.T.obj P), M.scalar.T.obj Q))).hom ≫
      M.targetClosed.evaluation (M.scalar.T.obj P) (M.scalar.T.obj Q) =
    M.tensorIso.inv.app
        (P, (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ≫
      M.scalar.T.map (siteScalarHomSourceEvaluation J φ M P Q) := by
  let _ := M.targetClosed.monoidal
  let _ := M.targetSymmetry
  have h := (M.targetClosed.transpose _ (M.scalar.T.obj P) (M.scalar.T.obj Q)).symm_apply_apply
    ((M.targetSymmetry.braiding
      (M.scalar.T.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)))
      (M.scalar.T.obj P)).hom ≫
        M.tensorIso.inv.app
          (P, (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ≫
        M.scalar.T.map (siteScalarHomSourceEvaluation J φ M P Q))
  change (siteScalarHomComparison J φ M P Q ▷ M.scalar.T.obj P) ≫
    M.targetClosed.evaluation _ _ = _ at h
  simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.id_tensorHom]
  rw [BraidedCategory.braiding_naturality_right_assoc, h]
  simp

private theorem siteScalarHomComparison_naturality
    (P P' Q Q' : DerivedCategory (RingedTensorModules.{c, v, r} J R))
    (a : P' ⟶ P) (b : Q ⟶ Q') :
    siteScalarHomComparison J φ M P Q ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J S).map
          (Prod.mkHom (M.scalar.T.map a).op (M.scalar.T.map b)) =
      M.scalar.T.map ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom a.op b)) ≫ siteScalarHomComparison J φ M P' Q' := by
  exact coefficientHomComparison_naturality M.sourceClosed M.targetClosed
    M.sourceSymmetry M.targetSymmetry M.scalar.T M.tensorIso P P' Q Q' a b

attribute [local semireducible] SheafOfModules.monoidalCategory in
private noncomputable def siteScalarSourceDualityModel :
    RingedSiteDualityModel.{c, v, r, w} J R := by
  let K := M.sourceCoherence
  have hunit : CochainComplex.IsKFlatIndependentCoefficients
      (J := J) (R := R) (ringedSiteDualityUnitComplex.{c, v, r} J R) := by
    intro F hF n
    exact (hF n).of_iso (HomologicalComplex.rightUnitor F).symm
  refine ⟨M.sourceClosed, M.sourceModel, M.sourceSymmetry, K.unitIso, hunit, ?_, ?_, ?_⟩
  · intro P Q hP hQ
    obtain ⟨s, hs, he⟩ := K.symmetry_model P Q hP hQ
    exact ⟨s.hom, hs, he⟩
  · intro P hP
    obtain ⟨ρ, hρ, he⟩ := K.rightUnitor_model P hP
    refine ⟨ρ.hom, ?_, ?_⟩
    · intro p U x a
      exact hρ p (Int.add_zero p) U a x
    · rw [K.tensorIso_both P (ringedTensorUnitComplex.{c, v, r} J R) hP hunit] at he
      exact he
  · intro P Q V hP hQ hV
    obtain ⟨α, hα, he⟩ := K.associator_model P Q V hP hQ hV
    refine ⟨α.hom, ?_, ?_⟩
    · intro p q t i j k hpq hit hqt hpj U x y z
      exact hα p q t i j k hpq hqt hit hpj U x y z
    · rw [K.tensorIso_both _ V
        (coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV,
        K.tensorIso_both P _ hP
          (coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)] at he
      exact he

private theorem sitePerfectScalarHomData_nonempty :
    ∃ M : SitePerfectScalarHomData.{c, v, r, w} J φ,
      ∃ m : @Functor.CoreMonoidal _ _ M.sourceClosed.monoidal
        _ _ M.targetClosed.monoidal M.scalar.T,
      ∀ P Q, (@Functor.CoreMonoidal.μIso _ _ M.sourceClosed.monoidal
        _ _ M.targetClosed.monoidal M.scalar.T m P Q).hom = M.tensorIso.inv.app (P, Q) := by
  obtain ⟨D⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel φ
  obtain ⟨AR, MR, βR, ⟨hR⟩⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J R
  obtain ⟨AS, MS, βS, ⟨hS⟩⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J S
  obtain ⟨κ, μ, hκ, hμ⟩ := ringedFiniteFreeHomBaseChange_tensor J φ D AR AS MR MS
  obtain ⟨m, hm⟩ :=
    ringedScalarTensorMonoidal J φ D AR AS MR MS βR βS hR hS κ μ hκ hμ
  exact ⟨⟨D, AR, AS, MR, MS, βR, βS, hR, hS, κ, μ,
    by unfold SiteScalarHomGeneratorFormula; exact hκ,
    by unfold SiteScalarHomTensorNormalization; exact hμ⟩, m, hm⟩

private theorem siteScalarHomComparison_isIso
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (m : @Functor.CoreMonoidal _ _ M.sourceClosed.monoidal
      _ _ M.targetClosed.monoidal M.scalar.T)
    (hm : ∀ P Q, (@Functor.CoreMonoidal.μIso _ _ M.sourceClosed.monoidal
      _ _ M.targetClosed.monoidal M.scalar.T m P Q).hom = M.tensorIso.inv.app (P, Q))
    (P : DerivedCategory (RingedTensorModules.{c, v, r} J R))
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R P)
    (Q : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    IsIso (siteScalarHomComparison J φ M P Q) := by
  let _ := M.sourceClosed.monoidal
  let _ := M.targetClosed.monoidal
  let _ := M.sourceSymmetry
  let _ := M.targetSymmetry
  let _ := coefficientMonoidalClosed M.sourceClosed M.sourceSymmetry
  let _ := coefficientMonoidalClosed M.targetClosed M.targetSymmetry
  let _ := m.toMonoidal
  let D := siteScalarSourceDualityModel J φ M
  have hl := ringedSitePerfectDualityForModel.{c, v, r, w} J R P hP D
  have hi : IsIso (ringedSiteDualEvaluationLeft M.sourceClosed M.sourceSymmetry
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.sourceCoherence.unitIso P P) := by
    have := hl
    exact NatIso.hom_app_isIso (asIso
      (ringedSiteDualEvaluationLeftNatTrans D.closed D.symmetric
        (ringedSiteDualityUnit.{c, v, r, w} J R) D.unitIso P)) P
  have : IsIso (MonoidalClosed.ihomUnitTensorToIhom P P) := by
    rw [← coefficientDualComparison_eq M.sourceClosed M.sourceSymmetry
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.sourceCoherence.unitIso P P]
    have := hi
    have : IsIso ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (𝟙 (op P)) M.sourceCoherence.unitIso.hom)) := by
      exact inferInstanceAs (IsIso ((derivedInternalHomOfUniverses.{c, v, r, w} J R).mapIso
        ((Iso.refl (op P)).prod M.sourceCoherence.unitIso)).hom)
    infer_instance
  let _ := MonoidalClosed.exactPairingOfIsIso P
  have hi := Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing M.scalar.T
    ((ihom P).obj (𝟙_ _)) P Q
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry] at hi
  suffices he : siteScalarHomComparison J φ M P Q =
      MonoidalClosed.curry
        (Functor.LaxMonoidal.μ M.scalar.T P ((ihom P).obj Q) ≫
          M.scalar.T.map ((ihom.ev P).app Q)) by
    rw [he]
    exact hi
  unfold siteScalarHomComparison MonoidalClosed.curry
  change (M.targetClosed.adjunction (M.scalar.T.obj P)).homEquiv _ _ _ =
    ((M.targetClosed.adjunction (M.scalar.T.obj P)).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight (M.scalar.T.obj P)).symm).homEquiv _ _ _
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  rw [show Functor.LaxMonoidal.μ M.scalar.T P ((ihom P).obj Q) =
      M.tensorIso.inv.app (P, (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op P, Q)) from hm P _]
  simp only [SymmetricCategory.braiding_swap_eq_inv_braiding]
  rfl

end Site

/-- Scalar extension commutes with internal Hom from a site-perfect object, by the
specified evaluation transpose, naturally in both variables. No flatness of S over R
or boundedness, constructibility or Tor-amplitude restriction on Q is assumed.

Source: Stacks Project, Tag 08JJ, lemma-dual-perfect-complex, applied over both rings;
current blueprint lem-fix-operation-reduction.proof.md, paragraph 1.
(blueprint: lem-fix-site-perfect-scalar-hom).

Proof:
1. Regard the ring map as a morphism of ringed topoi over the identity topos. Use
   lem-pur-derived-change-of-rings for F and its K-flat universal pair. The canonical
   comparison of lem-weil-pbc-ringed-topoi-derived-tensor-pullback and the coherent
   structures of lem-sf-ringed-derived-closed-symmetric-monoidal and
   lem-sfb-ringed-derived-monoidal-comparisons give the displayed normalized data.
2. For perfect P put D = RHom(P,R). By lem-sfb-ringed-site-duality-maps the evaluation
   comparison D tensor N to RHom(P,N) is the transpose of evaluation tensor 1_N,
   after symmetry. Its invertibility for every unbounded N is exactly
   lem-sfb-ringed-site-perfect-duality, checked locally on bounded finite-free retracts.
3. Apply lem-fix-closed-evaluation-dual-criterion to those actual comparisons. Its
   coevaluation is the inverse evaluation comparison at P applied to the transpose
   of 1_P. Both triangle identities hold for the specified evaluation.
4. Apply lem-fix-monoidal-dual-hom-comparison to this dual pair and the canonical
   strong tensor structure on F. Its comparison is the same transpose as
   siteScalarHomComparison, so that specified map is invertible for every Q.
5. Inverse transposition gives the displayed evaluation equation. Transposing both
   sides of the naturality square for a:P' to P and b:Q to Q' gives the same map,
   by naturality of evaluation and the tensor comparison. Hence both naturalities
   hold, including zero objects, identity ring maps and the zero coefficient ring. -/
theorem sitePerfectScalarHomComparison
    (X : AlgebraicGeometry.Scheme.{u})
    [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max (u + 1) r}]
    [(AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) r}]
    [∀ U : X.ProEt, HasSheafify ((AlgebraicGeometry.Scheme.ProEt.topology X).over U)
      AddCommGrpCat.{max (u + 1) r}]
    [∀ U : X.ProEt, ((AlgebraicGeometry.Scheme.ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) r}]
    (R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{max (u + 1) r})
    (φ : R ⟶ S)
    [HasDerivedCategory.{w} (RingedTensorModules.{u + 1, u, r}
      (AlgebraicGeometry.Scheme.ProEt.topology X) R)]
    [HasDerivedCategory.{w} (RingedTensorModules.{u + 1, u, r}
      (AlgebraicGeometry.Scheme.ProEt.topology X) S)] :
    ∃ M : SitePerfectScalarHomData.{u + 1, u, r, w}
        (AlgebraicGeometry.Scheme.ProEt.topology X) φ,
      (∀ P : DerivedCategory (RingedTensorModules.{u + 1, u, r}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R),
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, r, w} R P →
        ∀ Q : DerivedCategory (RingedTensorModules.{u + 1, u, r}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R),
        IsIso (siteScalarHomComparison _ φ M P Q)) ∧
      (∀ (P P' Q Q' : DerivedCategory (RingedTensorModules.{u + 1, u, r}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R)) (a : P' ⟶ P) (b : Q ⟶ Q'),
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, r, w} R P →
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, r, w} R P' →
        siteScalarHomComparison _ φ M P Q ≫
            (derivedInternalHomOfUniverses.{u + 1, u, r, w} _ S).map
              (Prod.mkHom (M.scalar.T.map a).op (M.scalar.T.map b)) =
          M.scalar.T.map ((derivedInternalHomOfUniverses.{u + 1, u, r, w} _ R).map
            (Prod.mkHom a.op b)) ≫ siteScalarHomComparison _ φ M P' Q') ∧
      (∀ P Q : DerivedCategory (RingedTensorModules.{u + 1, u, r}
          (AlgebraicGeometry.Scheme.ProEt.topology X) R),
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, r, w} R P →
        M.targetClosed.tensor.map (Prod.mkHom (𝟙 (M.scalar.T.obj P))
            (siteScalarHomComparison _ φ M P Q)) ≫
          (M.targetSymmetry.braiding (M.scalar.T.obj P)
            ((derivedInternalHomOfUniverses.{u + 1, u, r, w} _ S).obj
              (op (M.scalar.T.obj P), M.scalar.T.obj Q))).hom ≫
          M.targetClosed.evaluation (M.scalar.T.obj P) (M.scalar.T.obj Q) =
        M.tensorIso.inv.app
            (P, (derivedInternalHomOfUniverses.{u + 1, u, r, w} _ R).obj (op P, Q)) ≫
          M.scalar.T.map (siteScalarHomSourceEvaluation _ φ M P Q)) := by
  obtain ⟨M, m, hm⟩ := sitePerfectScalarHomData_nonempty _ φ
  refine ⟨M, ?_, ?_, ?_⟩
  · intro P hP Q
    exact siteScalarHomComparison_isIso _ φ M m hm P hP Q
  · intro P P' Q Q' a b _ _
    exact siteScalarHomComparison_naturality _ φ M P P' Q Q' a b
  · intro P Q _
    exact siteScalarHomComparison_evaluation _ φ M P Q

end CategoryTheory
