/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomData
public import Sheaf.Algebra.Homology.StrictScalarHomChain
import all Sheaf.Algebra.Homology.ScalarHomTensorCoherence
import all Sheaf.Algebra.Homology.StrictScalarHomChain
import all Sheaf.Algebra.Homology.ScalarOrdinaryEvaluationCoefficientSquare
import all Sheaf.CategoryTheory.ClosedScalarHomComparison
import all Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Algebra.Homology.RingedTensorComparisonExtension
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Whiskering

/-! # The representative of the scalar-unit tensor map

The assertion concerns the tensor map itself, before postcomposition with any evaluation.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6 and 06YP, and steps 3--5
of the flat scalar evaluation refinement.
(blueprint: lem-sfb-scalar-tensor-exact-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
  SheafOfModules WeilConjectures

attribute [local irreducible] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  scalarPairComplexComparison CoefficientTensorModels.iso
  SheafOfModules.monoidalCategory homComplexFunctor derivedInternalHomOfUniverses
  CoefficientClosedStructure.tensor

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.IsFlatOnSite

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

namespace ScalarTensorRepresentative

attribute [local instance] ScalarDerivedPair.extension_additive

private theorem adjunct_transport_cancel
    {A : Type*} {B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
    {X Y : A} {Z W : B} (e : W ≅ Z) (r : U.obj Z ≅ Y)
    (f : F.obj X ⟶ Z) (k : X ⟶ Y)
    (h : adj.homEquiv _ _ f = k ≫ r.inv) :
    adj.homEquiv _ _ (f ≫ e.inv) ≫ (U.mapIso e ≪≫ r).hom = k := by
  rw [adj.homEquiv_naturality_right, h]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    ← U.map_comp_assoc, Iso.inv_hom_id, U.map_id, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]

private theorem scalar_tensor_adjunct
    {A : Type*} {B : Type*} [Category A] [Category B]
    {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
    (m : S.tensor ⋙ F ≅ F.prod F ⋙ T.tensor)
    (X K : A) (N : B) (f : X ⟶ U.obj N) :
    S.tensor.map (Prod.mkHom f (𝟙 K)) ≫
      S.tensor.map (Prod.mkHom (𝟙 _) (adj.unit.app K)) ≫
      ClosedScalarHom.restrictionTensor S T adj m N (F.obj K) =
    adj.homEquiv _ _ (m.hom.app (X, K) ≫
      T.tensor.map (Prod.mkHom ((adj.homEquiv X N).symm f) (𝟙 (F.obj K)))) := by
  rw [ClosedScalarHom.restrictionTensor_unit S T adj m N K]
  rw [← Category.assoc, ← adj.unit_naturality]
  rw [Category.assoc, ← U.map_comp]
  have hn := m.hom.naturality (Prod.mkHom f (𝟙 K))
  change F.map (S.tensor.map (Prod.mkHom f (𝟙 K))) ≫ m.hom.app _ =
    m.hom.app _ ≫ T.tensor.map (Prod.mkHom (F.map f) (F.map (𝟙 K))) at hn
  rw [F.map_id] at hn
  rw [reassoc_of% hn, ← T.tensor.map_comp]
  have hp : Prod.mkHom (F.map f) (𝟙 (F.obj K)) ≫
      Prod.mkHom (adj.counit.app N) (𝟙 (F.obj K)) =
      Prod.mkHom ((adj.homEquiv X N).symm f) (𝟙 (F.obj K)) := by
    change Prod.mkHom (F.map f ≫ adj.counit.app N) (𝟙 _ ≫ 𝟙 _) = _
    rw [Category.id_comp, ← adj.homEquiv_counit X N f]
  rw [hp, Adjunction.homEquiv_unit]

private theorem scalar_tensor_representative_paste
    {A : Type*} {B : Type*} [Category A] [Category B]
    {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure I)
    {F : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ U)
    (m : S.tensor ⋙ F ≅ F.prod F ⋙ T.tensor)
    {A0 P0 D0 XA XD RD RTD : A} {EA ED EP ETA ETD : B}
    (xA : XA ≅ S.tensor.obj (A0, P0)) (xD : XD ≅ S.tensor.obj (D0, P0))
    (eA : F.obj A0 ⟶ EA) (eD : F.obj D0 ≅ ED) (_eP : F.obj P0 ≅ EP)
    (rD : U.obj ED ≅ RD) (n : A0 ⟶ RD)
    (eTA : F.obj XA ⟶ ETA) (eTD : F.obj XD ≅ ETD)
    (rTD : U.obj ETD ≅ RTD) (k : XA ⟶ RTD) (l : ETA ⟶ ETD) (t : EA ⟶ ED)
    (hn : adj.homEquiv _ _ (eA ≫ t ≫ eD.inv) = n ≫ (U.mapIso eD ≪≫ rD).inv)
    (hh : F.map xA.hom ≫ m.hom.app (A0, P0) ≫
      T.tensor.map (Prod.mkHom (eA ≫ t ≫ eD.inv) (𝟙 (F.obj P0))) ≫
      m.inv.app (D0, P0) ≫ F.map xD.inv ≫ eTD.hom = eTA ≫ l)
    (hl : adj.homEquiv _ _ (eTA ≫ l) = k ≫ rTD.inv) :
    xA.hom ≫ S.tensor.map (Prod.mkHom (n ≫ (U.mapIso eD ≪≫ rD).inv) (𝟙 P0)) ≫
      S.tensor.map (Prod.mkHom (𝟙 _) (adj.unit.app P0)) ≫
      ClosedScalarHom.restrictionTensor S T adj m (F.obj D0) (F.obj P0) ≫
      U.map (m.inv.app (D0, P0)) ≫ U.map (F.map xD.inv) ≫
      (U.mapIso eTD ≪≫ rTD).hom = k := by
  have hs := scalar_tensor_adjunct S T adj m A0 P0 (F.obj D0)
    (n ≫ (U.mapIso eD ≪≫ rD).inv)
  have ht := congrArg (adj.homEquiv _ _).symm hn
  simp only [Equiv.symm_apply_apply] at ht
  rw [← ht] at hs
  rw [reassoc_of% hs]
  simp only [← Category.assoc]
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right,
    ← adj.homEquiv_naturality_right]
  simp only [Category.assoc]
  have hh' := congrArg (fun f ↦ f ≫ eTD.inv) hh
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh'
  rw [hh']
  simpa only [Category.assoc] using adjunct_transport_cancel adj eTD rTD (eTA ≫ l) k hl

private theorem tensor_normalization_conjugate
    {D : Type*} [Category D] (B : D × D ⥤ D)
    {A K L EA EK EL TA TK TA' TK' A0 K0 : D}
    (eA : A ⟶ EA) (eK : K ≅ EK) (eL : L ≅ EL) (t : EA ⟶ EL)
    (xA : TA ≅ A0) (xK : TK ≅ K0)
    (mA : A0 ≅ B.obj (A, K)) (mK : K0 ≅ B.obj (L, K))
    (eTA : TA ⟶ TA') (eTK : TK ⟶ TK')
    (cA : TA' ≅ B.obj (EA, EK)) (cK : TK' ≅ B.obj (EL, EK))
    (hA : xA.hom ≫ mA.hom ≫ B.map (Prod.mkHom eA eK.hom) = eTA ≫ cA.hom)
    (hK : xK.hom ≫ mK.hom ≫ B.map (Prod.mkHom eL.hom eK.hom) = eTK ≫ cK.hom) :
    xA.hom ≫ mA.hom ≫ B.map (Prod.mkHom (eA ≫ t ≫ eL.inv) (𝟙 K)) ≫
        mK.inv ≫ xK.inv ≫ eTK =
      eTA ≫ cA.hom ≫ B.map (Prod.mkHom t (𝟙 EK)) ≫ cK.inv := by
  have hh : mK.inv ≫ xK.inv ≫ eTK ≫ cK.hom =
      B.map (Prod.mkHom eL.hom eK.hom) := by
    have hk := congrArg (fun f ↦ mK.inv ≫ xK.inv ≫ f) hK
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hk.symm
  apply (cancel_mono cK.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hh, ← B.map_comp]
  have hp : Prod.mkHom (eA ≫ t ≫ eL.inv) (𝟙 K) ≫
      Prod.mkHom eL.hom eK.hom =
      Prod.mkHom eA eK.hom ≫ Prod.mkHom t (𝟙 EK) := by
    apply Prod.ext <;> simp [Category.assoc]
  rw [hp, B.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ f ≫ B.map (Prod.mkHom t (𝟙 EK))) hA


set_option maxHeartbeats 800000 in
-- Naturality transports the normalized square along the resolution isomorphism.
private theorem extension_unit_map
    (M : ScalarHomModels.{c, v, r, w} J)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    {X Y : CochainComplex (scalarModules J R) ℤ} (f : X ⟶ Y)
    (n : ℤ) (V : Cᵒᵖ) (x : (X.X n).val.obj V) :
    ((((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map f).f n).val.app V)
        (scalarHomUnitSection (J := J) M a (X.X n) V x) =
      scalarHomUnitSection (J := J) M a (Y.X n) V ((f.f n).val.app V x) := by
  have h := congrArg (fun z ↦ z.val.app V x)
    ((M.scalar a).ordinaryAdjunction.unit.naturality (f.f n)).symm
  exact h

set_option maxHeartbeats 800000 in
-- The chain tensor maps carry independent site and module universe presentations.
private theorem complexIso_natural
    (M : ScalarHomModels.{c, v, r, w} J)
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison (J := J) M a)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    {X X' Y Y' : CochainComplex (scalarModules J R) ℤ} (f : X ⟶ X') (g : Y ⟶ Y') :
    (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map
        ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom f g)) ≫
        ((μ a).complexIso X' Y').hom =
      ((μ a).complexIso X Y).hom ≫
        (coefficientTotalTensor.{r, c, v} J S).map
          (Prod.mkHom
            ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map f)
            ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map g)) := by
  apply ((ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _).injective
  ext n : 1
  apply ScalarHomTensor.total_pure_hom_ext X Y n
  intro p q h V x y
  change ((((μ a).complexIso X' Y').hom.f n).val.app V
      (((((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map
        ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom f g))).f n).val.app V
          (scalarHomUnitSection (J := J) M a _ V
            (coefficientTensorGenerator.{r, c, v} J R X Y p q n h V x y)))) =
    (((((coefficientTotalTensor.{r, c, v} J S).map
      (Prod.mkHom
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map f)
        ((scalarComplex (M.scalar a).extension
          (M.scalar a).extension_additive).map g))).f n).val.app V
          ((((μ a).complexIso X Y).hom.f n).val.app V
            (scalarHomUnitSection (J := J) M a _ V
              (coefficientTensorGenerator.{r, c, v} J R X Y p q n h V x y))))))
  let E := scalarComplex (M.scalar a).extension (M.scalar a).extension_additive
  let TR := coefficientTotalTensor.{r, c, v} J R
  let TS := coefficientTotalTensor.{r, c, v} J S
  let u := fun (Z : CochainComplex (scalarModules J R) ℤ) (j : ℤ) ↦
    scalarHomUnitSection (J := J) M a (Z.X j) V
  let genR := coefficientTensorGenerator.{r, c, v} J R X Y p q n h V x y
  let genS := coefficientTensorGenerator.{r, c, v} J S (E.obj X) (E.obj Y)
    p q n h V (u X p x) (u Y q y)
  have h1 := extension_unit_map.{c, v, r, w} (J := J) M a
    (TR.map (Prod.mkHom f g)) n V genR
  have h2 := ScalarHomTensor.tensor_generator_map.{c, v, r} (J := J) (R := R)
    f g p q n h V x y
  have h3 := (μ a).generators X' Y' p q n h V
    ((f.f p).val.app V x) ((g.f q).val.app V y)
  have h4 := (μ a).generators X Y p q n h V x y
  have h5 := ScalarHomTensor.tensor_generator_map.{c, v, r} (J := J) (R := S)
    (E.map f) (E.map g) p q n h V (u X p x) (u Y q y)
  have hf := extension_unit_map.{c, v, r, w} (J := J) M a f p V x
  have hg := extension_unit_map.{c, v, r, w} (J := J) M a g q V y
  have hh := congrArg₂ (fun x' y' ↦ coefficientTensorGenerator.{r, c, v} J S
    (E.obj X') (E.obj Y') p q n h V x' y') hf hg
  exact ((congrArg (fun z ↦ (((μ a).complexIso X' Y').hom.f n).val.app V z)
    (h1.trans (congrArg (u (TR.obj (X', Y')) n) h2))).trans h3).trans
      ((h5.trans hh).symm.trans
        (congrArg (fun z ↦ (((TS.map (Prod.mkHom (E.map f) (E.map g))).f n).val.app V z))
          h4).symm)

set_option maxHeartbeats 800000 in
-- Naturality transports the normalized square along the resolution isomorphism.
private theorem normalization_oneFactor
    (M : ScalarHomModels.{c, v, r, w} J)
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison (J := J) M a)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (P : CochainComplex (scalarModules J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (i : ∀ X : CochainComplex (scalarModules J R) ℤ,
      DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (X, P)) ≅
        (M.closed R).tensor.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj P))
    (hi : ∀ X hX, i X =
      CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R) X P hX hP)
    (hn : ∀ X Y (f : X ⟶ Y),
      DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom f (𝟙 P))) ≫ (i Y).hom =
      (i X).hom ≫ (M.closed R).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map f) (𝟙 (DerivedCategory.Q.obj P))))
    (j : RingedDerivedTensorComparison.{c, v, r, w} J S (M.closed S))
    (hj : RingedDerivedTensorBothModel J S (M.closed S) (M.model S) j)
    (hjn : RingedDerivedTensorNaturality J S (M.closed S) j)
    (X : CochainComplex (scalarModules J R) ℤ) :
    let F := (M.scalar a).derived
    let E := scalarComplex (M.scalar a).extension (M.scalar a).extension_additive
    let e := fun Z ↦ scalarPairComplexComparison (M.scalar a).extension
      (M.scalar a).extension_additive F (M.scalar a).counit Z
    F.map (i X).hom ≫ (μ a).iso.hom.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj P) ≫
        (M.closed S).tensor.map (Prod.mkHom (e X) (e P)) =
      e ((coefficientTotalTensor.{r, c, v} J R).obj (X, P)) ≫
        DerivedCategory.Q.map ((μ a).complexIso X P).hom ≫
          (j (E.obj X) (E.obj P) (Or.inr ((μ a).preservesKFlat P hP))).hom := by
  let F := (M.scalar a).derived
  let E := scalarComplex (M.scalar a).extension (M.scalar a).extension_additive
  let Q := DerivedCategory.Q (C := scalarModules J R)
  let QS := DerivedCategory.Q (C := scalarModules J S)
  let T := coefficientTotalTensor.{r, c, v} J R
  let TS := coefficientTotalTensor.{r, c, v} J S
  let B := (M.closed R).tensor
  let BS := (M.closed S).tensor
  let e := fun Z ↦ scalarPairComplexComparison (M.scalar a).extension
    (M.scalar a).extension_additive F (M.scalar a).counit Z
  obtain ⟨V, t, hV, _, ht, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients X
  let := ht
  have hnt := hn V X t
  have : IsIso (Q.map t) := inferInstance
  have hB : IsIso (B.map (Prod.mkHom (Q.map t) (𝟙 (Q.obj P)))) := by
    let qIso : Q.obj V ≅ Q.obj X := asIso (Q.map t)
    exact (B.mapIso (Iso.prod qIso (Iso.refl (Q.obj P)))).isIso_hom
  have hTf : IsIso (Q.map (T.map (Prod.mkHom t (𝟙 P)))) := by
    have hh : IsIso (Q.map (T.map (Prod.mkHom t (𝟙 P))) ≫ (i X).hom) := by
      rw [hnt]
      infer_instance
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (i X).hom (by infer_instance) hh
  let := hTf
  apply (cancel_epi (F.map (Q.map (T.map (Prod.mkHom t (𝟙 P)))))).mp
  have hni := congrArg F.map hnt
  simp only [F.map_comp] at hni
  have hnm := (μ a).iso.hom.naturality (Prod.mkHom (Q.map t) (𝟙 (Q.obj P)))
  change F.map (B.map (Prod.mkHom (Q.map t) (𝟙 (Q.obj P)))) ≫
      (μ a).iso.hom.app (Q.obj X, Q.obj P) =
    (μ a).iso.hom.app (Q.obj V, Q.obj P) ≫
      BS.map (Prod.mkHom (F.map (Q.map t)) (F.map (𝟙 (Q.obj P)))) at hnm
  rw [F.map_id] at hnm
  have hne := (ScalarHomTensor.pairComparison (J := J) M a).naturality t
  have hneT := (ScalarHomTensor.pairComparison (J := J) M a).naturality
    (T.map (Prod.mkHom t (𝟙 P)))
  simp only [ScalarHomTensor.pairComparison_app] at hne hneT
  have hnj := hjn (E.obj V) (E.obj P) (E.obj X) (E.obj P)
    (Or.inr ((μ a).preservesKFlat P hP)) (Or.inr ((μ a).preservesKFlat P hP))
    (E.map t) (𝟙 (E.obj P))
  have hnc := complexIso_natural (J := J) M μ a t (𝟙 P)
  simp only [Functor.map_id] at hnc hnj
  have hncQ := congrArg QS.map hnc
  simp only [QS.map_comp] at hncQ
  have hflat := (μ a).normalization V P hV hP
  rw [← hi V hV, ← hj (E.obj V) (E.obj P) ((μ a).preservesKFlat V hV)
    ((μ a).preservesKFlat P hP)] at hflat
  have hp : BS.map (Prod.mkHom (F.map (Q.map t)) (𝟙 (F.obj (Q.obj P)))) ≫
      BS.map (Prod.mkHom (e X) (e P)) =
    BS.map (Prod.mkHom (e V) (e P)) ≫
      BS.map (Prod.mkHom (QS.map (E.map t)) (𝟙 (QS.obj (E.obj P)))) := by
    rw [← BS.map_comp, ← BS.map_comp]
    congr 1
    apply Prod.ext
    · exact hne
    · change 𝟙 _ ≫ e P = e P ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
  rw [reassoc_of% hni]
  change F.map (i V).hom ≫ F.map (B.map (Prod.mkHom (Q.map t) (𝟙 (Q.obj P)))) ≫
      (μ a).iso.hom.app (Q.obj X, Q.obj P) ≫ BS.map (Prod.mkHom (e X) (e P)) =
    F.map (Q.map (T.map (Prod.mkHom t (𝟙 P)))) ≫ e (T.obj (X, P)) ≫
      QS.map ((μ a).complexIso X P).hom ≫
        (j (E.obj X) (E.obj P) (Or.inr ((μ a).preservesKFlat P hP))).hom
  have hstep := congrArg (fun z ↦ F.map (i V).hom ≫ z ≫
    BS.map (Prod.mkHom (e X) (e P))) hnm
  have hstep2 := congrArg (fun z ↦ F.map (i V).hom ≫
    (μ a).iso.hom.app (Q.obj V, Q.obj P) ≫ z) hp
  have hstep3 := congrArg (fun z ↦ z ≫
    BS.map (Prod.mkHom (QS.map (E.map t)) (𝟙 (QS.obj (E.obj P))))) hflat
  have hstep4 := congrArg (fun z ↦ e (T.obj (V, P)) ≫
    QS.map ((μ a).complexIso V P).hom ≫ z) hnj.symm
  have hstep5 := congrArg (fun z ↦ e (T.obj (V, P)) ≫ z ≫
    (j (E.obj X) (E.obj P) (Or.inr ((μ a).preservesKFlat P hP))).hom) hncQ.symm
  have hstep6 := congrArg (fun z ↦ z ≫ QS.map ((μ a).complexIso X P).hom ≫
    (j (E.obj X) (E.obj P) (Or.inr ((μ a).preservesKFlat P hP))).hom) hneT.symm
  simp only [Category.assoc] at hstep hstep2 hstep3 hstep4 hstep5 hstep6
  exact hstep.trans (hstep2.trans (hstep3.trans (hstep4.trans (hstep5.trans hstep6))))


variable (M : ScalarHomModels.{c, v, r, w} J)
  (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    ScalarHomTensorComparison (J := J) M a)

omit [∀ R : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J R)] in
private theorem generator_smul_left {R : Sheaf J CommRingCat.{max c v r}}
    (D P : StrictScalarHom.Complex.{c, v, r} R) (n i k : ℤ) (h : n + i = k)
    (V : Cᵒᵖ) (s : R.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V) :
    coefficientTensorGenerator.{r, c, v} J R D P n i k h V (s • x) p =
      s • coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p := by
  delta coefficientTotalTensor coefficientTensorGenerator
  simp only [← TensorProduct.smul_tmul', _root_.map_smul]

private theorem tensorComparison_inv_pure {R S : Sheaf J CommRingCat.{max c v r}}
    (a : R ⟶ S) (D P : StrictScalarHom.Complex.{c, v, r} R)
    (n i k : ℤ) (h : n + i = k) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V) :
    (((μ a).complexIso D P).inv.f k).val.app V
      (coefficientTensorGenerator.{r, c, v} J S
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj D)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) n i k h V
        ((s • scalarHomUnitSection (J := J) M a (D.X n) V x))
        ((1 • scalarHomUnitSection (J := J) M a (P.X i) V p))) =
      (fun z ↦ s • scalarHomUnitSection (J := J) M a
        (((coefficientTotalTensor.{r, c, v} J R).obj (D, P)).X k) V z)
        (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p) := by
  have he := congrArg (fun f ↦ (f.f k).val.app V
    (scalarHomUnitSection (J := J) M a _ V
      (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p)))
    ((μ a).complexIso D P).hom_inv_id
  change (((μ a).complexIso D P).inv.f k).val.app V
    ((((μ a).complexIso D P).hom.f k).val.app V
      (scalarHomUnitSection (J := J) M a _ V
        (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p))) = _ at he
  rw [(μ a).generators] at he
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at he
  simp only [one_smul]
  erw [generator_smul_left, _root_.map_smul]
  exact congrArg (fun z ↦ s • z) he

omit [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)] in
private theorem scalar_tensor_ext {R S : Sheaf J CommRingCat.{max c v r}}
    (a : R ⟶ S) (D P I : StrictScalarHom.Complex.{c, v, r} R)
    (f g : (coefficientTotalTensor.{r, c, v} J R).obj
      ((StrictScalarHom.tensor.{c, v, r} a).obj D, P) ⟶ I)
    (hfg : ∀ (n i k : ℤ) (h : n + i = k) (V : Cᵒᵖ)
      (s : S.obj.obj V) (x : (D.X n).val.obj V) (p : (P.X i).val.obj V),
      (f.f k).val.app V (coefficientTensorGenerator.{r, c, v} J R
          ((StrictScalarHom.tensor.{c, v, r} a).obj D) P n i k h V
          (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p) =
        (g.f k).val.app V (coefficientTensorGenerator.{r, c, v} J R
          ((StrictScalarHom.tensor.{c, v, r} a).obj D) P n i k h V
          (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p)) : f = g := by
  exact ScalarOrdinaryEvaluation.scalar_tensor_ext a D P I f g hfg

private theorem ordinary_tensor_adjunct
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (ν : StrictScalarHom.tensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        StrictScalarHom.restriction.{c, v, r} a)
    (hν : ∀ (X : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (V : Cᵒᵖ)
      (s : S.obj.obj V) (x : (X.X n).val.obj V),
      (((ν.hom.app X).f n).val.app V)
          (StrictScalarHom.tensorSection.{c, v, r} a X n V s x) =
        s • scalarHomUnitSection (J := J) M a (X.X n) V x)
    (D P : CochainComplex (scalarModules J R) ℤ) :
    let A := (StrictScalarHom.tensor.{c, v, r} a).obj D
    let t := ((ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _).symm (ν.hom.app D)
    let l := ((μ a).complexIso A P).hom ≫
      (coefficientTotalTensor.{r, c, v} J S).map (Prod.mkHom t (𝟙 _)) ≫
        ((μ a).complexIso D P).inv
    ∀ (n i k : ℤ) (h : n + i = k) (V : Cᵒᵖ) (s : S.obj.obj V)
      (x : (D.X n).val.obj V) (p : (P.X i).val.obj V),
      ((((ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _ l).f k).val.app V)
          (coefficientTensorGenerator.{r, c, v} J R A P n i k h V
            (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p) =
        s • scalarHomUnitSection (J := J) M a
          (((coefficientTotalTensor.{r, c, v} J R).obj (D, P)).X k) V
          (coefficientTensorGenerator.{r, c, v} J R D P n i k h V x p) := by
  dsimp only
  intro n i k h V s x p
  let t := ((ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _).symm (ν.hom.app D)
  have ht := ((ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _).apply_symm_apply
    (ν.hom.app D)
  have htx := congrArg (fun f ↦ (f.f n).val.app V
    (StrictScalarHom.tensorSection.{c, v, r} a D n V s x)) ht
  rw [Adjunction.homEquiv_unit] at htx ⊢
  dsimp only [scalarComplex] at htx ⊢
  change ((t.f n).val.app V
    (scalarHomUnitSection (J := J) M a _ V
      (StrictScalarHom.tensorSection.{c, v, r} a D n V s x))) = _ at htx
  have htx' := htx.trans (hν D n V s x)
  change (((μ a).complexIso D P).inv.f k).val.app V
    ((((coefficientTotalTensor.{r, c, v} J S).map
      (Prod.mkHom t (𝟙 _))).f k).val.app V
      ((((μ a).complexIso _ P).hom.f k).val.app V
        (scalarHomUnitSection (J := J) M a _ V
          (coefficientTensorGenerator.{r, c, v} J R _ P n i k h V
            (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p)))) = _
  erw [(μ a).generators, ScalarHomTensor.tensor_generator_map, htx']
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  simpa only [one_smul] using tensorComparison_inv_pure (J := J) M μ a D P n i k h V s x p

end ScalarTensorRepresentative

set_option maxHeartbeats 1200000 in
-- The comparison pastes three tensor squares and both scalar adjunctions.
/-- Exact scalar extension identifies the scalar-unit tensor map with its ordinary
sheafified pure-tensor formula, for an arbitrary first complex and a flat-term
K-flat right complex. No Hom complex or K-injective object occurs in this assertion.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6 and 06YP;
steps 3--5 of lem-sfb-hom-flat-scalar-evaluation-model.
(blueprint: lem-sfb-scalar-tensor-exact-representative).

Proof: choose a natural S-tensor representative comparison with either factor K-flat.
Resolve an arbitrary first R-complex by a flat-term K-flat one. Naturality of i makes
the localized resolution tensored with P invertible. Transport the normalized scalar
tensor square along that isomorphism to obtain the square for every first complex.
Let A be S tensor D, and let t:EA -> ED be the ordinary scalar adjunct of nu_D.
The composite E(A tensor P) -> EA tensor EP -> ED tensor EP -> E(D tensor P)
has ordinary adjunct k, by the generator formula for nu and the scalar tensor
comparison. The normalized derived adjunction identifies the derived adjunct of
(e_A Q(t) e_D^-1) with Q(nu_D) rho_D^-1. Taking its tensor with the unit on P is
the adjunct of the strong tensor comparison followed by the tensor of that adjunct.
Conjugate the arbitrary-first-factor normalization by e_D and e_P and use naturality
of the S-tensor representative comparison for t. This gives e_(A tensor P) Q(l)
e_(D tensor P)^-1, where l is the ordinary composite above. Transpose and cancel
rho_(D tensor P) to obtain Q(k). Every equality holds on the actual sheafified
tensor generators, including for zero rings and zero complexes. -/
theorem scalarTensorExactRepresentative
    (M : ScalarHomModels.{c, v, r, w} J)
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison (J := J) M a)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (q : ∀ X : CochainComplex (scalarModules J R) ℤ,
      IsIso (scalarPairComplexComparison (M.scalar a).extension
        (M.scalar a).extension_additive (M.scalar a).derived (M.scalar a).counit X))
    (ν : StrictScalarHom.tensor.{c, v, r} a ≅
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        StrictScalarHom.restriction.{c, v, r} a)
    (hν : ∀ (X : CochainComplex (scalarModules J R) ℤ) (n : ℤ) (V : Cᵒᵖ)
      (s : S.obj.obj V) (x : (X.X n).val.obj V),
      (((ν.hom.app X).f n).val.app V)
          (StrictScalarHom.tensorSection.{c, v, r} a X n V s x) =
        s • scalarHomUnitSection (J := J) M a (X.X n) V x)
    (P D : CochainComplex (scalarModules J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (i : ∀ X : CochainComplex (scalarModules J R) ℤ,
      DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (X, P)) ≅
        (M.closed R).tensor.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj P))
    (hi : ∀ (X : CochainComplex (scalarModules J R) ℤ)
      (hX : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) X),
      i X = CoefficientTensorModels.iso.{r, c, v, w} J R (M.closed R) (M.model R)
        X P hX hP)
    (hn : ∀ (X Y : CochainComplex (scalarModules J R) ℤ) (f : X ⟶ Y),
      DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J R).map
          (Prod.mkHom f (𝟙 P))) ≫ (i Y).hom =
        (i X).hom ≫ (M.closed R).tensor.map
          (Prod.mkHom (DerivedCategory.Q.map f) (𝟙 (DerivedCategory.Q.obj P))))
    (k : (coefficientTotalTensor.{r, c, v} J R).obj
        ((StrictScalarHom.tensor.{c, v, r} a).obj D, P) ⟶
      (StrictScalarHom.restriction.{c, v, r} a).obj
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj
          ((coefficientTotalTensor.{r, c, v} J R).obj (D, P))))
    (hk : ∀ (n j l : ℤ) (h : n + j = l) (V : Cᵒᵖ) (s : S.obj.obj V)
      (x : (D.X n).val.obj V) (p : (P.X j).val.obj V),
      (k.f l).val.app V
          (coefficientTensorGenerator.{r, c, v} J R _ P n j l h V
            (StrictScalarHom.tensorSection.{c, v, r} a D n V s x) p) =
        s • scalarHomUnitSection (J := J) M a
          (((coefficientTotalTensor.{r, c, v} J R).obj (D, P)).X l) V
          (coefficientTensorGenerator.{r, c, v} J R D P n j l h V x p)) :
    let F := (M.scalar a).derived
    let U := scalarDerivedRestriction a
    let E := scalarComplex (M.scalar a).extension (M.scalar a).extension_additive
    let ρ := fun X : CochainComplex (scalarModules J R) ℤ ↦
      letI := q X
      U.mapIso (asIso (scalarPairComplexComparison (M.scalar a).extension
        (M.scalar a).extension_additive F (M.scalar a).counit X)) ≪≫
          (scalarRestrictionComparison a).app (E.obj X)
    (i ((StrictScalarHom.tensor.{c, v, r} a).obj D)).hom ≫
      (M.closed R).tensor.map
        (Prod.mkHom (DerivedCategory.Q.map (ν.hom.app D) ≫ (ρ D).inv)
          (𝟙 (DerivedCategory.Q.obj P))) ≫
      (M.closed R).tensor.map
        (Prod.mkHom (𝟙 _) ((M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj P))) ≫
      scalarHomRestrictionTensor (J := J) M a (μ a) (F.obj (DerivedCategory.Q.obj D))
        (F.obj (DerivedCategory.Q.obj P)) ≫
      U.map ((μ a).iso.inv.app (DerivedCategory.Q.obj D, DerivedCategory.Q.obj P)) ≫
      U.map (F.map (i D).inv) ≫
      (ρ ((coefficientTotalTensor.{r, c, v} J R).obj (D, P))).hom =
        DerivedCategory.Q.map k := by
  classical
  let F := (M.scalar a).derived
  let U := scalarDerivedRestriction a
  let E := scalarComplex (M.scalar a).extension (M.scalar a).extension_additive
  let T := coefficientTotalTensor.{r, c, v} J R
  let B := (M.closed S).tensor
  let A := (StrictScalarHom.tensor.{c, v, r} a).obj D
  let e := fun X ↦ scalarPairComplexComparison (M.scalar a).extension
    (M.scalar a).extension_additive F (M.scalar a).counit X
  let (X : CochainComplex (scalarModules J R) ℤ) : IsIso (e X) := q X
  let ρ := fun X ↦ U.mapIso (asIso (e X)) ≪≫ (scalarRestrictionComparison a).app (E.obj X)
  let t := ((ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _).symm (ν.hom.app D)
  let l := ((μ a).complexIso A P).hom ≫
    (coefficientTotalTensor.{r, c, v} J S).map (Prod.mkHom t (𝟙 _)) ≫
      ((μ a).complexIso D P).inv
  have hl : (ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _ l = k := by
    apply ScalarTensorRepresentative.scalar_tensor_ext a D P
    intro n j l h V s x p
    rw [ScalarTensorRepresentative.ordinary_tensor_adjunct (J := J) M μ a ν hν D P n j l h V s x p]
    exact (hk n j l h V s x p).symm
  obtain ⟨j, hj, hjn⟩ := ringedTensorComparison_extension.{c, v, r, w}
    J S (M.closed S) (M.model S)
  let c := fun X ↦ DerivedCategory.Q.mapIso ((μ a).complexIso X P) ≪≫
    j (E.obj X) (E.obj P) (Or.inr ((μ a).preservesKFlat P hP))
  have hc (X : CochainComplex (scalarModules J R) ℤ) :
      F.map (i X).hom ≫ (μ a).iso.hom.app (DerivedCategory.Q.obj X, DerivedCategory.Q.obj P) ≫
          B.map (Prod.mkHom (e X) (e P)) = e (T.obj (X, P)) ≫ (c X).hom := by
    exact ScalarTensorRepresentative.normalization_oneFactor (J := J) M μ a P hP i hi hn j hj hjn X
  have ht : (M.scalar a).adjunction.homEquiv _ _
      (e A ≫ DerivedCategory.Q.map t ≫ inv (e D)) =
        DerivedCategory.Q.map (ν.hom.app D) ≫ (ρ D).inv := by
    have h := ScalarHomTensor.transpose_comparison (J := J) M a A (E.obj D) t
    rw [ScalarHomTensor.pairComparison_app] at h
    change (M.scalar a).adjunction.homEquiv _ _ (e A ≫ DerivedCategory.Q.map t) =
      DerivedCategory.Q.map ((ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _ t) ≫
        (scalarRestrictionComparison a).inv.app (E.obj D) at h
    have htν : (ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _ t = ν.hom.app D :=
      ((ScalarHomTensor.chainAdj (J := J) M a).homEquiv _ _).apply_symm_apply _
    rw [htν] at h
    rw [← Category.assoc, (M.scalar a).adjunction.homEquiv_naturality_right, h]
    simp only [ρ, Iso.trans_inv, Functor.mapIso_inv, asIso_inv, Iso.app_inv, Category.assoc]
    rfl
  have hcj := hjn (E.obj A) (E.obj P) (E.obj D) (E.obj P)
    (Or.inr ((μ a).preservesKFlat P hP)) (Or.inr ((μ a).preservesKFlat P hP)) t (𝟙 _)
  simp only [Functor.map_id] at hcj
  have hcmap : (c A).hom ≫ B.map (Prod.mkHom (DerivedCategory.Q.map t) (𝟙 _)) ≫
      (c D).inv = DerivedCategory.Q.map l := by
    dsimp only [c, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv]
    simp only [Category.assoc]
    erw [← reassoc_of% hcj]
    simp only [Iso.hom_inv_id_assoc, ← DerivedCategory.Q.map_comp]
    rfl
  have hh := ScalarTensorRepresentative.tensor_normalization_conjugate B
    (e A) (asIso (e P)) (asIso (e D)) (DerivedCategory.Q.map t)
    (F.mapIso (i A)) (F.mapIso (i D))
    ((μ a).iso.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj P))
    ((μ a).iso.app (DerivedCategory.Q.obj D, DerivedCategory.Q.obj P))
    (e (T.obj (A, P))) (e (T.obj (D, P))) (c A) (c D) (hc A) (hc D)
  rw [hcmap] at hh
  have htL := ScalarHomTensor.transpose_comparison (J := J) M a (T.obj (A, P))
    (E.obj (T.obj (D, P))) l
  rw [ScalarHomTensor.pairComparison_app, hl] at htL
  change (M.scalar a).adjunction.homEquiv _ _
      (e (T.obj (A, P)) ≫ DerivedCategory.Q.map l) =
    DerivedCategory.Q.map k ≫ (scalarRestrictionComparison a).inv.app _ at htL
  exact
    ScalarTensorRepresentative.scalar_tensor_representative_paste
      (M.closed R) (M.closed S) (M.scalar a).adjunction (μ a).iso (i A) (i D)
      (e A) (asIso (e D)) (asIso (e P))
      ((scalarRestrictionComparison a).app (E.obj D)) (DerivedCategory.Q.map (ν.hom.app D))
      (e (T.obj (A, P))) (asIso (e (T.obj (D, P))))
      ((scalarRestrictionComparison a).app (E.obj (T.obj (D, P))))
      (DerivedCategory.Q.map k) (DerivedCategory.Q.map l) (DerivedCategory.Q.map t)
      ht hh htL

end CategoryTheory
