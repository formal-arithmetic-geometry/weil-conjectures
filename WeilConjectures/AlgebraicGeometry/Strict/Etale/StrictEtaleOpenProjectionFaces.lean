/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelInverseConstruction
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOpenInverseEvaluation
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleLevelInverseQuotient
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison

/-! # Normalized geometric projection faces

Source: Zheng, Construction 5.15 and Lemma 5.22.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem openInverseMate_isIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {L' : D ⥤ E} {R' : E ⥤ D}
    {G : A ⥤ D} {H : B ⥤ E} [G.IsEquivalence] [H.IsEquivalence]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : R ⋙ G ≅ H ⋙ R') :
    IsIso (((mateEquiv adj adj').symm (.mk _ _ _ _ s.hom)).natTrans) := by
  let b := ((mateEquiv adj adj').symm (.mk _ _ _ _ s.hom)).natTrans
  let sop : H.op ⋙ R'.op ≅ R.op ⋙ G.op := NatIso.op s
  have hi := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    adj.op adj'.op H.op G.op sop
  have he : NatTrans.op b =
      (mateEquiv adj.op adj'.op (.mk _ _ _ _ sop.hom)).natTrans := by
    ext X
    simp [b, sop, mateEquiv]
  have : IsIso (NatTrans.op b) := by rw [he]; exact hi
  have (X : A) : IsIso (b.app X) := by
    have : IsIso ((b.app X).op) :=
      NatIso.isIso_app_of_isIso (NatTrans.op b) (Opposite.op X)
    exact isIso_of_op (b.app X)
  exact NatIso.isIso_of_isIso_app b

private theorem openLeftMate_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : A' ⥤ B'} {R₃ : B' ⥤ A'} {L₄ : C' ⥤ D'} {R₄ : D' ⥤ C'}
    {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (tX : G ⋙ c ≅ a ⋙ G') (tZ : H ⋙ d ≅ b ⋙ H')
    (τ : R₁ ⋙ G ⟶ H ⋙ R₂) (τ' : R₃ ⋙ G' ⟶ H' ⋙ R₄)
    (δA : a ⋙ L₃ ⟶ L₁ ⋙ b) (δB : c ⋙ L₄ ⟶ L₂ ⋙ d)
    (h : ∀ M,
      c.map (τ.app M) ≫
          (mateEquiv a₂ a₄ (.mk _ _ _ _ δB)).natTrans.app (H.obj M) ≫
          R₄.map (tZ.hom.app M) =
        tX.hom.app (R₁.obj M) ≫
          G'.map ((mateEquiv a₁ a₃ (.mk _ _ _ _ δA)).natTrans.app M) ≫
          τ'.app (b.obj M))
    (K : A) :
    L₄.map (tX.hom.app K) ≫
        ((mateEquiv a₃ a₄).symm (.mk _ _ _ _ τ')).natTrans.app (a.obj K) ≫
        H'.map (δA.app K) =
      δB.app (G.obj K) ≫
        d.map (((mateEquiv a₁ a₂).symm (.mk _ _ _ _ τ)).natTrans.app K) ≫
        tZ.hom.app (L₁.obj K) := by
  apply (a₄.homEquiv _ _).injective
  rw [a₄.homEquiv_naturality_left]
  erw [adjunctionMate_transpose a₃ a₄ (.mk _ _ _ _ τ') (a.obj K)
    (b.obj (L₁.obj K)) (δA.app K)]
  have hA := unit_mateEquiv a₁ a₃ (.mk _ _ _ _ δA) K
  have hB := unit_mateEquiv a₂ a₄ (.mk _ _ _ _ δB) (G.obj K)
  have hT := unit_mateEquiv_symm a₁ a₂ (.mk _ _ _ _ τ) K
  change a.map (a₁.unit.app K) ≫
      (mateEquiv a₁ a₃ (.mk _ _ _ _ δA)).natTrans.app (L₁.obj K) =
    a₃.unit.app (a.obj K) ≫ R₃.map (δA.app K) at hA
  change c.map (a₂.unit.app (G.obj K)) ≫
      (mateEquiv a₂ a₄ (.mk _ _ _ _ δB)).natTrans.app (L₂.obj (G.obj K)) =
    a₄.unit.app (c.obj (G.obj K)) ≫ R₄.map (δB.app (G.obj K)) at hB
  change G.map (a₁.unit.app K) ≫ τ.app (L₁.obj K) =
    a₂.unit.app (G.obj K) ≫
      R₂.map (((mateEquiv a₁ a₂).symm (.mk _ _ _ _ τ)).natTrans.app K) at hT
  rw [Adjunction.homEquiv_unit]
  change tX.hom.app K ≫
      G'.map (a₃.unit.app (a.obj K) ≫ R₃.map (δA.app K)) ≫
      τ'.app (b.obj (L₁.obj K)) = _
  rw [← hA]
  simp only [Functor.map_comp, Category.assoc]
  have hn := tX.hom.naturality (a₁.unit.app K)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← h]
  rw [a₄.homEquiv_naturality_right]
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj]
  rw [← reassoc_of% hB]
  rw [← c.map_comp_assoc, hT]
  simp only [Functor.map_comp, Category.assoc]
  have hd := (mateEquiv a₂ a₄ (.mk _ _ _ _ δB)).natTrans.naturality
    (((mateEquiv a₁ a₂).symm (.mk _ _ _ _ τ)).natTrans.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hd
  rw [reassoc_of% hd]

private theorem openDerivedEvaluation_mate
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :
    (mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)
      (.mk _ _ _ _ (S.openDerivedEvaluation n).inv)).natTrans =
        (S.openDerived.inverseEvaluation n).hom := by
  let τ := (NatIso.mapHomologicalComplex
    (S.openImage.inverseEvaluation n) (.up ℤ)).hom
  let ι := (NatIso.mapHomologicalComplex (S.val.openEvaluation n) (.up ℤ)).inv
  have hι (P : CochainComplex (strictEtaleCoefficientSystem X O ell) ℤ) :
      ((S.val.levelOpenAdjunction n).mapHomologicalComplex (.up ℤ)).homEquiv
          (((coefficientEvaluation (J := X.smallEtaleTopology)
            (O := O) (ell := ell) n).mapHomologicalComplex (.up ℤ)).obj P)
          (((coefficientEvaluation (J := c.Z.smallEtaleTopology)
            (O := O) (ell := ell) n).mapHomologicalComplex (.up ℤ)).obj
              ((S.val.openExtension.mapHomologicalComplex (.up ℤ)).obj P)) (ι.app P) =
        ((coefficientEvaluation (J := X.smallEtaleTopology)
          (O := O) (ell := ell) n).mapHomologicalComplex (.up ℤ)).map
          (((S.val.openAdjunction).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        τ.app (((S.val.openExtension).mapHomologicalComplex (.up ℤ)).obj P) := by
    ext k : 1
    change (S.val.levelOpenAdjunction n).homEquiv _ _
        ((S.val.openEvaluation n).inv.app (P.X k)) =
      (coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := ell) n).map
        (S.val.openAdjunction.unit.app (P.X k)) ≫
      (S.openImage.inverseEvaluation n).hom.app (S.val.openExtension.obj (P.X k))
    erw [S.property.2.1 n]
    have hu := (unit_mateEquiv S.val.openAdjunction (S.val.levelOpenAdjunction n)
      (.mk _ _ _ _ (S.val.openEvaluation n).inv) (P.X k)).symm
    change (S.val.levelOpenAdjunction n).unit.app
          ((coefficientEvaluation (J := X.smallEtaleTopology)
            (O := O) (ell := ell) n).obj (P.X k)) ≫
        (S.openImage.lift n).modules.map ((S.val.openEvaluation n).inv.app (P.X k)) =
      (coefficientEvaluation (J := X.smallEtaleTopology)
        (O := O) (ell := ell) n).map (S.val.openAdjunction.unit.app (P.X k)) ≫
        (mateEquiv S.val.openAdjunction (S.val.levelOpenAdjunction n)
          (.mk _ _ _ _ (S.val.openEvaluation n).inv)).natTrans.app
            (S.val.openExtension.obj (P.X k)) at hu
    rw [Adjunction.homEquiv_unit]
    exact hu
  have hr P := derivedMate_comparison
    (S.val.openAdjunction.mapHomologicalComplex (.up ℤ))
    ((S.val.levelOpenAdjunction n).mapHomologicalComplex (.up ℤ))
    S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)
    S.val.openFactors.hom (S.val.levelOpenFactors n).hom
    S.openDerived.system.inverseFactors (S.openDerived.level n).inverseFactors
    (S.PX.evaluationFactors n) (S.PZ.evaluationFactors n)
    S.property.2.2.1 (S.property.2.2.2.1 n)
    (.mk _ _ _ _ τ) (.mk _ _ _ _ (S.openDerived.inverseEvaluation n).hom)
    (S.openDerived.inverseEvaluation_rep n) ι hι P
  have hleft :
      ((mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)).symm
        (.mk _ _ _ _ (S.openDerived.inverseEvaluation n).hom)).natTrans =
      (S.openDerivedEvaluation n).inv := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleCoefficientSystem X O ell) (.up ℤ))
    intro P
    apply (cancel_mono ((S.PZ.evaluation n).map (S.val.openFactors.hom.app P) ≫
      (S.PZ.evaluationFactors n).hom.app
        ((S.val.openExtension.mapHomologicalComplex (.up ℤ)).obj P))).1
    erw [hr]
    have he := S.property.2.2.2.2 n P
    have he' := congrArg (fun z ↦ (S.openDerivedEvaluation n).inv.app
      (DerivedCategory.Q.obj P) ≫ z ≫ DerivedCategory.Q.map (ι.app P)) he
    simp only [ι, Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app] at he'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at he'
    exact he'
  have hm := Equiv.apply_symm_apply
    (mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n))
      (.mk _ _ _ _ (S.openDerived.inverseEvaluation n).hom)
  rw [show ((mateEquiv S.derivedOpenAdjunction (S.levelDerivedOpenAdjunction n)).symm
      (.mk _ _ _ _ (S.openDerived.inverseEvaluation n).hom)) =
      (.mk _ _ _ _ (S.openDerivedEvaluation n).inv) from hleft] at hm
  exact hm

theorem openProjectionFaces_of_mates
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (qX : StrictEtaleTransportQuotient TX) (qZ : StrictEtaleTransportQuotient TZ)
    (square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.system SB.openDerived.system)
    (b : TX.derived ⋙ SB.derivedOpen ⟶ SA.derivedOpen ⋙ TZ.derived)
    (hb : (mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction
      (.mk _ _ _ _ b)).natTrans = square.derived.inv)
    (bn : ∀ n, (TX.level n).derived ⋙ SB.levelDerivedOpen n ⟶
      SA.levelDerivedOpen (index n) ⋙ (TZ.level n).derived)
    (hbn : ∀ n, IsIso (bn n))
    (heval : ∀ n K,
      (SB.openDerivedEvaluation n).hom.app (TX.derived.obj K) ≫
          (SB.levelDerivedOpen n).map ((TX.derivedEvaluation n).hom.app K) ≫
          (bn n).app ((SA.PX.evaluation (index n)).obj K) =
        (SB.PZ.evaluation n).map (b.app K) ≫
          (TZ.derivedEvaluation n).hom.app (SA.derivedOpen.obj K) ≫
          (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K))
    (hcube : ∀ (QA : StrictEtaleQuotientProjection SA)
        (QB : StrictEtaleQuotientProjection SB) {m n : ℕ} (h : n ≤ m) K,
      (SB.levelDerivedOpen n).map ((qX.derived h).hom.app K) ≫
          (QB.openProjection h).hom.app ((TX.level m).derived.obj K) ≫
          (SB.PZ.scalar h).derived.map ((bn m).app K) =
        (bn n).app ((SA.PX.scalar (index.monotone h)).derived.obj K) ≫
          (TZ.level n).derived.map ((QA.openProjection (index.monotone h)).hom.app K) ≫
          (qZ.derived h).hom.app ((SA.levelDerivedOpen (index m)).obj K)) :
    ∃ (square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
        SA.openDerived.system SB.openDerived.system)
      (openComparison : SA.derivedOpen ⋙ TZ.derived ≅ TX.derived ⋙ SB.derivedOpen)
      (level : ∀ n, SA.levelDerivedOpen (index n) ⋙ (TZ.level n).derived ≅
        (TX.level n).derived ⋙ SB.levelDerivedOpen n),
      ((mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction
          (.mk _ _ _ _ openComparison.inv)).natTrans = square.derived.inv) ∧
      (∀ n K,
        (TZ.derivedEvaluation n).hom.app (SA.derivedOpen.obj K) ≫
            (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K) ≫
            (level n).hom.app ((SA.PX.evaluation (index n)).obj K) =
          (SB.PZ.evaluation n).map (openComparison.hom.app K) ≫
            (SB.openDerivedEvaluation n).hom.app (TX.derived.obj K) ≫
            (SB.levelDerivedOpen n).map ((TX.derivedEvaluation n).hom.app K)) ∧
      (∀ (QA : StrictEtaleQuotientProjection SA) (QB : StrictEtaleQuotientProjection SB)
          {m n : ℕ} (h : n ≤ m) K,
        (SB.levelDerivedOpen n).map ((qX.derived h).hom.app K) ≫
            (QB.openProjection h).hom.app ((TX.level m).derived.obj K) ≫
            (SB.PZ.scalar h).derived.map ((level m).inv.app K) =
          (level n).inv.app ((SA.PX.scalar (index.monotone h)).derived.obj K) ≫
            (TZ.level n).derived.map ((QA.openProjection (index.monotone h)).hom.app K) ≫
            (qZ.derived h).hom.app ((SA.levelDerivedOpen (index m)).obj K)) := by
  have : ∀ n, IsIso (bn n) := hbn
  have hbi : IsIso b := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    apply (SB.properDerived.detectsIso (b.app K)).2
    intro n
    have : IsIso ((SB.PZ.evaluation n).map (b.app K) ≫
        (TZ.derivedEvaluation n).hom.app (SA.derivedOpen.obj K) ≫
        (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K)) := by
      rw [← heval n K]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((TZ.derivedEvaluation n).hom.app (SA.derivedOpen.obj K) ≫
        (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K))
  let := hbi
  let op : SA.derivedOpen ⋙ TZ.derived ≅ TX.derived ⋙ SB.derivedOpen := (asIso b).symm
  let ol n : SA.levelDerivedOpen (index n) ⋙ (TZ.level n).derived ≅
      (TX.level n).derived ⋙ SB.levelDerivedOpen n := (asIso (bn n)).symm
  refine ⟨square, op, ol, hb, ?_, ?_⟩
  · intro n K
    have h := heval n K
    change (SB.openDerivedEvaluation n).hom.app (TX.derived.obj K) ≫
        (SB.levelDerivedOpen n).map ((TX.derivedEvaluation n).hom.app K) ≫
        (ol n).inv.app ((SA.PX.evaluation (index n)).obj K) =
      (SB.PZ.evaluation n).map (op.inv.app K) ≫
        (TZ.derivedEvaluation n).hom.app (SA.derivedOpen.obj K) ≫
        (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K) at h
    have h' := congrArg (fun z ↦ (SB.PZ.evaluation n).map (op.hom.app K) ≫ z ≫
      (ol n).hom.app ((SA.PX.evaluation (index n)).obj K)) h
    dsimp only [Functor.comp_obj] at h' ⊢
    simp only [Category.assoc, Iso.inv_hom_id_app,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at h'
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h'
    exact h'.symm
  · exact hcube

private theorem openProjectionFaces_of_inverseData
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (hTX : ∀ n, (TX.level n).derived.IsEquivalence)
    (hTZ : ∀ n, (TZ.level n).derived.IsEquivalence)
    (qX : StrictEtaleTransportQuotient TX) (qZ : StrictEtaleTransportQuotient TZ)
    (square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.system SB.openDerived.system)
    (finite : ∀ n, StrictEtaleLevelInverseTransport TX TZ SA.openImage SB.openImage
      SA.openDerived.level SB.openDerived.level n)
    (rightEval : ∀ n M,
      (SB.PX.evaluation n).map (square.derived.inv.app M) ≫
          (SB.openDerived.inverseEvaluation n).hom.app (TZ.derived.obj M) ≫
          (SB.openDerived.level n).inverse.map ((TZ.derivedEvaluation n).hom.app M) =
        (TX.derivedEvaluation n).hom.app (SA.openDerived.system.inverse.obj M) ≫
          (TX.level n).derived.map
            ((SA.openDerived.inverseEvaluation (index n)).hom.app M) ≫
          (finite n).derived.inv.app ((SA.PZ.evaluation (index n)).obj M))
    (rightQuotient : ∀ {m n : ℕ} (h : n ≤ m) M,
      (SB.PX.scalar h).derived.map ((finite m).derived.inv.app M) ≫
          (SB.openDerived.derivedTensor h).inv.app ((TZ.level m).derived.obj M) ≫
          (SB.openDerived.level n).inverse.map ((qZ.derived h).inv.app M) =
        (qX.derived h).inv.app ((SA.openDerived.level (index m)).inverse.obj M) ≫
          (TX.level n).derived.map
            ((SA.openDerived.derivedTensor (index.monotone h)).inv.app M) ≫
          (finite n).derived.inv.app ((SA.PZ.scalar (index.monotone h)).derived.obj M)) :
    ∃ (square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
        SA.openDerived.system SB.openDerived.system)
      (openComparison : SA.derivedOpen ⋙ TZ.derived ≅ TX.derived ⋙ SB.derivedOpen)
      (level : ∀ n, SA.levelDerivedOpen (index n) ⋙ (TZ.level n).derived ≅
        (TX.level n).derived ⋙ SB.levelDerivedOpen n),
      ((mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction
          (.mk _ _ _ _ openComparison.inv)).natTrans = square.derived.inv) ∧
      (∀ n K,
        (TZ.derivedEvaluation n).hom.app (SA.derivedOpen.obj K) ≫
            (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K) ≫
            (level n).hom.app ((SA.PX.evaluation (index n)).obj K) =
          (SB.PZ.evaluation n).map (openComparison.hom.app K) ≫
            (SB.openDerivedEvaluation n).hom.app (TX.derived.obj K) ≫
            (SB.levelDerivedOpen n).map ((TX.derivedEvaluation n).hom.app K)) ∧
      (∀ (QA : StrictEtaleQuotientProjection SA) (QB : StrictEtaleQuotientProjection SB)
          {m n : ℕ} (h : n ≤ m) K,
        (SB.levelDerivedOpen n).map ((qX.derived h).hom.app K) ≫
            (QB.openProjection h).hom.app ((TX.level m).derived.obj K) ≫
            (SB.PZ.scalar h).derived.map ((level m).inv.app K) =
          (level n).inv.app ((SA.PX.scalar (index.monotone h)).derived.obj K) ≫
            (TZ.level n).derived.map ((QA.openProjection (index.monotone h)).hom.app K) ≫
            (qZ.derived h).hom.app ((SA.levelDerivedOpen (index m)).obj K)) := by
  let b := ((mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction).symm
    (.mk _ _ _ _ square.derived.inv)).natTrans
  let bn n := ((mateEquiv (SA.levelDerivedOpenAdjunction (index n))
    (SB.levelDerivedOpenAdjunction n)).symm (.mk _ _ _ _ (finite n).derived.inv)).natTrans
  have hb : (mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction
      (.mk _ _ _ _ b)).natTrans = square.derived.inv := by
    exact congrArg TwoSquare.natTrans
      ((mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction).apply_symm_apply _)
  have hbn n : IsIso (bn n) := by
    let := hTX n
    let := hTZ n
    exact openInverseMate_isIso (SA.levelDerivedOpenAdjunction (index n))
      (SB.levelDerivedOpenAdjunction n) (finite n).derived.symm
  apply openProjectionFaces_of_mates a c SA SB TX TZ qX qZ square b hb bn hbn
  · intro n K
    have ht := openLeftMate_cube SA.derivedOpenAdjunction SB.derivedOpenAdjunction
      (SA.levelDerivedOpenAdjunction (index n)) (SB.levelDerivedOpenAdjunction n)
      (SA.PX.evaluation (index n)) (SA.PZ.evaluation (index n))
      (SB.PX.evaluation n) (SB.PZ.evaluation n)
      (TX.derivedEvaluation n) (TZ.derivedEvaluation n)
      square.derived.inv (finite n).derived.inv
      (SA.openDerivedEvaluation (index n)).inv (SB.openDerivedEvaluation n).inv
      (by simpa only [openDerivedEvaluation_mate] using rightEval n) K
    have ht' := congrArg (fun z ↦
      (SB.openDerivedEvaluation n).hom.app (TX.derived.obj K) ≫ z ≫
        (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K)) ht
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      Iso.hom_inv_id_app_assoc] at ht'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht'
    exact ht'
  · intro QA QB m n h K
    have ht := openLeftMate_cube
      (SA.levelDerivedOpenAdjunction (index m)) (SB.levelDerivedOpenAdjunction m)
      (SA.levelDerivedOpenAdjunction (index n)) (SB.levelDerivedOpenAdjunction n)
      (SA.PX.scalar (index.monotone h)).derived
      (SA.PZ.scalar (index.monotone h)).derived
      (SB.PX.scalar h).derived (SB.PZ.scalar h).derived
      (qX.derived h).symm (qZ.derived h).symm
      (finite m).derived.inv (finite n).derived.inv
      (QA.openProjection (index.monotone h)).hom (QB.openProjection h).hom
      (by simpa only [QA.open_mate, QB.open_mate, Iso.symm_hom, TwoSquare.natTrans]
        using rightQuotient h) K
    have ht' := congrArg (fun z ↦
      (SB.levelDerivedOpen n).map ((qX.derived h).hom.app K) ≫ z ≫
        (qZ.derived h).hom.app ((SA.levelDerivedOpen (index m)).obj K)) ht
    simp only [Iso.symm_hom, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app] at ht'
    erw [Category.comp_id] at ht'
    exact ht'.symm

/-- The open-extension face of coefficient transport, including evaluation and
its quotient square. The system and level comparisons point in the direction used
in compact support.
Source: Zheng, Construction 5.15 and Lemma 5.22.
(blueprint: lem-pur-strict-etale-open-projection-faces).

Proof: at each selected coefficient stage, extend scalars and commute it with the
algebraic inverse image of the open immersion. The ring square holds on constant
coefficient generators. Its comparison is the unique map preserving the tensor
unit. These maps commute with successor transitions by the same unit uniqueness,
so they form the ordinary inverse-image comparison of strict systems. Localize its
exact functors with their given factorization isomorphisms to obtain the normalized
derived square. Take its inverse mate under the two open-extension adjunctions.
At a finite level the mate is invertible because both vertical scalar functors are
equivalences. Its evaluated square agrees with the system mate: on complexes this
follows by transposing the normalized representative equations, and localization
extends the equality to every derived object. Evaluation detects invertibility,
so the system mate is invertible as well. For quotient compatibility, compare the
two scalar/inverse-image composites before taking the open mate. On ordinary tensor
units they agree because the two composite coefficient maps agree. The universal
derived counits give the same equality after deriving, using a K-flat replacement
and their prescribed representative equations. Taking the open mates and cancelling
the scalar equivalences gives the displayed cube. The mate equations of arbitrary
QA and QB identify their open faces with these canonical mates. -/
theorem nonempty_strictEtaleOpenProjectionFaces
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
    (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
    (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
    (hTX : ∀ n, (TX.level n).derived.IsEquivalence)
    (hTZ : ∀ n, (TZ.level n).derived.IsEquivalence)
    (qX : StrictEtaleTransportQuotient TX) (qZ : StrictEtaleTransportQuotient TZ) :
    ∃ (square : StrictEtaleInverseTransport TX TZ SA.openImage SB.openImage
        SA.openDerived.system SB.openDerived.system)
      (openComparison : SA.derivedOpen ⋙ TZ.derived ≅ TX.derived ⋙ SB.derivedOpen)
      (level : ∀ n, SA.levelDerivedOpen (index n) ⋙ (TZ.level n).derived ≅
        (TX.level n).derived ⋙ SB.levelDerivedOpen n),
      ((mateEquiv SA.derivedOpenAdjunction SB.derivedOpenAdjunction
          (.mk _ _ _ _ openComparison.inv)).natTrans = square.derived.inv) ∧
      (∀ n K,
        (TZ.derivedEvaluation n).hom.app (SA.derivedOpen.obj K) ≫
            (TZ.level n).derived.map ((SA.openDerivedEvaluation (index n)).hom.app K) ≫
            (level n).hom.app ((SA.PX.evaluation (index n)).obj K) =
          (SB.PZ.evaluation n).map (openComparison.hom.app K) ≫
            (SB.openDerivedEvaluation n).hom.app (TX.derived.obj K) ≫
            (SB.levelDerivedOpen n).map ((TX.derivedEvaluation n).hom.app K)) ∧
      (∀ (QA : StrictEtaleQuotientProjection SA) (QB : StrictEtaleQuotientProjection SB)
          {m n : ℕ} (h : n ≤ m) K,
        (SB.levelDerivedOpen n).map ((qX.derived h).hom.app K) ≫
            (QB.openProjection h).hom.app ((TX.level m).derived.obj K) ≫
            (SB.PZ.scalar h).derived.map ((level m).inv.app K) =
          (level n).inv.app ((SA.PX.scalar (index.monotone h)).derived.obj K) ≫
            (TZ.level n).derived.map ((QA.openProjection (index.monotone h)).hom.app K) ≫
            (qZ.derived h).hom.app ((SA.levelDerivedOpen (index m)).obj K)) := by
  classical
  let finite n := Classical.choice
    (nonempty_strictEtaleLevelInverseTransport a c SA SB TX TZ n)
  obtain ⟨square, heval⟩ :=
    nonempty_strictEtaleOpenInverseEvaluation a c SA SB TX TZ finite
  exact openProjectionFaces_of_inverseData a c SA SB TX TZ hTX hTZ qX qZ square finite
    heval (strictEtaleLevelInverse_quotient a c SA SB TX TZ qX qZ finite)

end AlgebraicGeometry
