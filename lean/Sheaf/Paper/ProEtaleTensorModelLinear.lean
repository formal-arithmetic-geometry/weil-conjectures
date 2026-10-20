/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Monoidal.Linear
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import Mathlib.CategoryTheory.Localization.Linear
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Preadditive.Opposite
/-!
# Linearity of a normalized pro-etale tensor model

Source: Stacks Project, Tags 06YT and 06YU
(blueprint: lem-wf-proetale-tensor-model-linear).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
private theorem wfRestrictionCalculus {C : Type*} [Category* C]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C)
    (res : ∀ X : C, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    (W.inverseImage P.ι).HasRightCalculusOfFractions := by
  exact
    { exists_rightFraction := by
        intro X Y φ
        obtain ⟨ψ, hψ⟩ := (MorphismProperty.LeftFraction.mk φ.f.hom φ.s.hom φ.hs
          : W.LeftFraction X.obj Y.obj).exists_rightFraction
        obtain ⟨Z, r, hr⟩ := res ψ.X'
        refine ⟨MorphismProperty.RightFraction.mk
          (ObjectProperty.homMk (r ≫ ψ.s)) (W.comp_mem _ _ hr ψ.hs)
          (ObjectProperty.homMk (r ≫ ψ.f)), ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hψ).trans
          (Category.assoc _ _ _).symm)
      ext := by
        intro X Y Y' f g s hs h
        obtain ⟨Z, t, ht, heq⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
          f.hom g.hom s.hom hs (congrArg (fun k ↦ k.hom) h)
        obtain ⟨T, r, hr⟩ := res Z
        refine ⟨T, ObjectProperty.homMk (r ≫ t), W.comp_mem _ _ hr ht, ?_⟩
        apply ObjectProperty.hom_ext
        exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) heq).trans
          (Category.assoc _ _ _).symm) }

private theorem wfRightTransfer {R : Type*} [CommRing R]
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive E] [Linear R E] [Preadditive C] [Linear R C]
    [Preadditive D] [Linear R D] (L : C ⥤ D) [L.EssSurj]
    (F : C ⥤ C ⥤ E) (B : D × D ⥤ E)
    (c : (L.prod L) ⋙ B ≅ Functor.uncurry.obj F)
    (hf : ∀ M, (F.obj M).Additive ∧ (F.obj M).Linear R)
    (transfer : ∀ G : D ⥤ E, (L ⋙ G).Additive ∧ (L ⋙ G).Linear R →
      G.Additive ∧ G.Linear R) :
    ∀ M, ((Functor.curry.obj B).obj M).Additive ∧
      ((Functor.curry.obj B).obj M).Linear R := by
  intro M
  let N := L.objPreimage M
  let G := (Functor.curry.obj B).obj (L.obj N)
  let e : L ⋙ G ≅ F.obj N :=
    ((Functor.curryObjProdComp L L B).app N).symm ≪≫
      (Functor.curry.mapIso c).app N ≪≫
        ((Functor.currying.unitIso.app F).app N).symm
  have h := hf N
  let := h.1
  let := h.2
  have hG : G.Additive ∧ G.Linear R := transfer G
    ⟨Functor.additive_of_iso e.symm, Functor.linear_of_iso R e.symm⟩
  let := hG.1
  let := hG.2
  let i := (Functor.curry.obj B).mapIso (L.objObjPreimageIso M)
  exact ⟨Functor.additive_of_iso i, Functor.linear_of_iso R i⟩

private theorem wfTransferFull {R : Type*} [CommRing R]
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [Linear R C] [Linear R D] [Linear R E]
    (L : C ⥤ D) [L.Full] [L.EssSurj] [L.Additive] [L.Linear R]
    (G : D ⥤ E) (h : (L ⋙ G).Additive ∧ (L ⋙ G).Linear R) :
    G.Additive ∧ G.Linear R := by
  let := h.1
  let := h.2
  exact ⟨Functor.additive_of_full_essSurj_comp L G,
    Functor.linear_of_full_essSurj_comp (R := R) L G⟩

private theorem wfTransferLocalization {R : Type*} [CommRing R]
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [Linear R C] [Linear R D] [Linear R E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasRightCalculusOfFractions] [L.Additive] [L.Linear R]
    (G : D ⥤ E) (h : (L ⋙ G).Additive ∧ (L ⋙ G).Linear R) :
    G.Additive ∧ G.Linear R := by
  let := h.1
  let := h.2
  have : (L.op ⋙ G.op).Additive := inferInstanceAs (L ⋙ G).op.Additive
  have : G.op.Additive := (Localization.functor_additive_iff L.op W.op G.op).mpr this
  have hG : G.Additive := inferInstanceAs G.op.unop.Additive
  let : Localization.Lifting L W (L ⋙ G) G := ⟨Iso.refl _⟩
  exact ⟨hG, (Localization.functor_linear_iff L W R (L ⋙ G) G).mp h.2⟩

private theorem wfBothTransfer {R : Type*} [CommRing R]
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive E] [Linear R E] [Preadditive C] [Linear R C]
    [Preadditive D] [Linear R D] (L : C ⥤ D) [L.EssSurj]
    (F : C ⥤ C ⥤ E) (B : D × D ⥤ E)
    (c : (L.prod L) ⋙ B ≅ Functor.uncurry.obj F)
    (hf : ∀ M, (F.obj M).Additive ∧ (F.obj M).Linear R)
    (hf' : ∀ M, (F.flip.obj M).Additive ∧ (F.flip.obj M).Linear R)
    (transfer : ∀ G : D ⥤ E, (L ⋙ G).Additive ∧ (L ⋙ G).Linear R →
      G.Additive ∧ G.Linear R) :
    (∀ M, ((Functor.curry.obj B).obj M).Additive ∧
      ((Functor.curry.obj B).obj M).Linear R) ∧
    ∀ M, ((Functor.curry.obj B).flip.obj M).Additive ∧
      ((Functor.curry.obj B).flip.obj M).Linear R := by
  refine ⟨wfRightTransfer L F B c hf transfer, ?_⟩
  let B' := CategoryTheory.Prod.swap D D ⋙ B
  let c' : (L.prod L) ⋙ B' ≅ Functor.uncurry.obj F.flip :=
    Functor.isoWhiskerLeft (CategoryTheory.Prod.swap C C) c ≪≫ (Functor.uncurryObjFlip F).symm
  exact wfRightTransfer L F.flip B' c' hf' transfer

private theorem wfHomotopyRestrictionIso
    {C E : Type*} [Category* C] [Preadditive C] [Category* E]
    (S : ObjectProperty (CochainComplex C ℤ))
    (P : ObjectProperty (HomotopyCategory C (.up ℤ)))
    (hs : ∀ K : P.FullSubcategory, S K.obj.as)
    (F G : HomotopyCategory C (.up ℤ) × HomotopyCategory C (.up ℤ) ⥤ E)
    (sigma : (((S.ι ⋙ HomotopyCategory.quotient C (.up ℤ)).prod
      (S.ι ⋙ HomotopyCategory.quotient C (.up ℤ))) ⋙ F) ≅
        (((S.ι ⋙ HomotopyCategory.quotient C (.up ℤ)).prod
          (S.ι ⋙ HomotopyCategory.quotient C (.up ℤ))) ⋙ G)) :
    ∃ tau : (P.ι.prod P.ι) ⋙ F ≅ (P.ι.prod P.ι) ⋙ G,
      ∀ MN, tau.hom.app MN =
        sigma.hom.app (⟨MN.1.obj.as, hs MN.1⟩, ⟨MN.2.obj.as, hs MN.2⟩) := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let rep (K : P.FullSubcategory) : S.FullSubcategory := ⟨K.obj.as, hs K⟩
  refine ⟨NatIso.ofComponents (fun MN ↦ sigma.app (rep MN.1, rep MN.2)) ?_, fun _ ↦ rfl⟩
  intro MN MN' fg
  obtain ⟨f, hf⟩ := Q.map_surjective (X := MN.1.obj.as) (Y := MN'.1.obj.as) fg.1.hom
  obtain ⟨g, hg⟩ := Q.map_surjective (X := MN.2.obj.as) (Y := MN'.2.obj.as) fg.2.hom
  have hn := sigma.hom.naturality
    (X := (rep MN.1, rep MN.2)) (Y := (rep MN'.1, rep MN'.2))
    (Prod.mkHom (ObjectProperty.homMk f) (ObjectProperty.homMk g))
  change F.map (Prod.mkHom (Q.map f) (Q.map g)) ≫ _ =
    _ ≫ G.map (Prod.mkHom (Q.map f) (Q.map g)) at hn
  rw [hf, hg] at hn
  exact hn

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
@[instance_reducible] private def wfPresheafLinear :
    Linear A (_root_.PresheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (pbcAdicCompletion X d)).obj) where
  homModule M N := Module.compHom (M ⟶ N)
    ((PresheafOfModules.sectionsSMulHom N).comp (pbcCompletedScalarSections X d))
  smul_comp M N P t f g := by
    change (f ≫ PresheafOfModules.sectionsSMul N _) ≫ g =
      (f ≫ g) ≫ PresheafOfModules.sectionsSMul P _
    rw [PresheafOfModules.sectionsSMul_naturality f,
      PresheafOfModules.sectionsSMul_naturality (f ≫ g), Category.assoc]
  comp_smul M N P f t g := by rfl

private theorem wfForget_linear :
    let := wfPresheafLinear X d
    (SheafOfModules.forget.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (pbcAdicCompletion X d))).Linear A := by
  let := wfPresheafLinear X d
  constructor
  intro M N f t
  rfl

private theorem wfPresheafTensorRight_linear
    (M : _root_.PresheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (pbcAdicCompletion X d)).obj) :
    let := wfPresheafLinear X d
    (tensorRight M).Linear A := by
  let := wfPresheafLinear X d
  constructor
  intro N N' f t
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change ((pbcCompletedSection X d U t) • (f.app U).hom x) ⊗ₜ[(pbcAdicCompletion X d).obj.obj U] y =
    (pbcCompletedSection X d U t) • ((f.app U).hom x ⊗ₜ[(pbcAdicCompletion X d).obj.obj U] y)
  exact TensorProduct.smul_tmul' _ _ _

private theorem wfTensorRight_linear (M : pbcModules X (pbcAdicCompletion X d)) :
    let := SheafOfModules.isMonoidal_W_independentCoefficients (pbcAdicCompletion X d)
    let := SheafOfModules.monoidalCategory (pbcAdicCompletion X d)
    (tensorRight M).Linear A := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (pbcAdicCompletion X d)
  let := SheafOfModules.monoidalCategory (pbcAdicCompletion X d)
  let := wfPresheafLinear X d
  let O := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (pbcAdicCompletion X d)
  have : (SheafOfModules.forget.{u + 1} O).Linear A := wfForget_linear X d
  have : (PresheafOfModules.restrictScalars (𝟙 O.obj)).Linear A := by
    constructor
    intro N N' f t
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rfl
  have : (PresheafOfModules.sheafification.{u + 1} (𝟙 O.obj)).Linear A :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 O.obj)).left_adjoint_linear
  have : (tensorRight M.val).Linear A := wfPresheafTensorRight_linear X d M.val
  exact Functor.linear_of_iso A
    (SheafOfModules.tensorRightPresentation (pbcAdicCompletion X d) M).symm
private theorem wfTensorLeft_linear (M : pbcModules X (pbcAdicCompletion X d)) :
    let := SheafOfModules.isMonoidal_W_independentCoefficients (pbcAdicCompletion X d)
    let := SheafOfModules.monoidalCategory (pbcAdicCompletion X d)
    (tensorLeft M).Linear A := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (pbcAdicCompletion X d)
  let := SheafOfModules.monoidalCategory (pbcAdicCompletion X d)
  let := SheafOfModules.symmetricCategory (pbcAdicCompletion X d)
  have : (tensorRight M).Linear A := wfTensorRight_linear X d M
  exact Functor.linear_of_iso A (BraidedCategory.tensorLeftIsoTensorRight M).symm

private theorem wfTotalRight_linear (M : CochainComplex
    (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    ((proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ) |>.obj M).Linear A := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (pbcAdicCompletion X d)
  let := SheafOfModules.monoidalCategory (pbcAdicCompletion X d)
  have (N : pbcModules X (pbcAdicCompletion X d)) : (tensorLeft N).Linear A :=
    wfTensorLeft_linear X d N
  constructor
  intro N N' f t
  apply HomologicalComplex.Hom.ext
  funext q
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [Functor.map₂HomologicalComplex_obj_map, HomologicalComplex.smul_f_apply,
    Linear.comp_smul, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.smul_f_apply, Functor.map_smul, Linear.comp_smul, Linear.smul_comp]

private theorem wfTotalLeft_linear (M : CochainComplex
    (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    ((proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ) |>.flip.obj M).Linear A := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (pbcAdicCompletion X d)
  let := SheafOfModules.monoidalCategory (pbcAdicCompletion X d)
  have (N : pbcModules X (pbcAdicCompletion X d)) : (tensorRight N).Linear A :=
    wfTensorRight_linear X d N
  have h : (proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).Linear A := by
    constructor
    intro N N' f t
    apply NatTrans.ext
    funext P
    exact (tensorRight P).map_smul t f
  let := h
  constructor
  intro N N' f t
  apply HomologicalComplex.Hom.ext
  funext q
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [Functor.flip_obj_map, Functor.map₂HomologicalComplex_map_app,
    HomologicalComplex.smul_f_apply, Linear.comp_smul, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.smul_f_apply, Functor.map_smul, NatTrans.app_smul,
    Linear.comp_smul, Linear.smul_comp]
/-- Every normalized K-flat tensor model is linear in both variables over the original
coefficient ring, including for completed coefficient sheaves.
Source: Stacks Project, Tags 06YT and 06YU
(blueprint: lem-wf-proetale-tensor-model-linear).
Proof: sectionwise tensor and sheafification are linear. Their total complex is therefore
linear in each variable. Fullness of the homotopy quotient transfers these assertions to
the homotopy tensor bifunctor. Restrict to flat-term K-flat objects. They resolve every
complex, so their quasi-isomorphisms have a right calculus of fractions and their inclusion
in the derived category is a localization. The normalized representative isomorphism
identifies this restricted bifunctor with the given model. Linearity and additivity then
descend through that localization in each variable. -/
theorem proEtaleTensorModel_linear (b : ProEtaleTensorModel X (pbcAdicCompletion X d)) :
    (∀ M, ((Functor.curry.obj b.tensor).obj M).Additive ∧
      ((Functor.curry.obj b.tensor).obj M).Linear A) ∧
    ∀ M, ((Functor.curry.obj b.tensor).flip.obj M).Additive ∧
      ((Functor.curry.obj b.tensor).flip.obj M).Linear A := by
  let O := pbcAdicCompletion X d
  let J := ProEt.topology X
  let C := proEtaleRingModules X O
  let := SheafOfModules.isMonoidal_W_independentCoefficients O
  let := SheafOfModules.monoidalCategory O
  let H := HomotopyCategory C (.up ℤ)
  let Q := HomotopyCategory.quotient C (.up ℤ)
  let F := (proEtaleOrdinaryTensor X O).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)
  obtain ⟨P, hP, hl, hb, _⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u + 1, u, u + 1, u + 2,
      0, 0} J O
  obtain ⟨G, hG, ⟨eps⟩⟩ := hl
  obtain ⟨B, ⟨c⟩, _, _⟩ := hb
  have : G.IsEquivalence := hG
  let L := P.ι ⋙ (DerivedCategory.Qh : H ⥤ DerivedCategory C)
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let V := W.inverseImage P.ι
  have : L.IsLocalization V := Functor.IsLocalization.of_iso _ eps
  have : L.EssSurj := Localization.essSurj L V
  have hres (K : H) : ∃ (N : P.FullSubcategory) (s : N.obj ⟶ K), W s := by
    obtain ⟨K', f, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (C := X.ProEt) (J := J) (R := O) K.as
    have hs : ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := O) (K'.X n) :=
      fun n ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso O (K'.X n)).symm (hf n)
    refine ⟨⟨Q.obj K', (hP _).2 ⟨hk, hs⟩⟩, Q.map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  have : V.HasRightCalculusOfFractions := wfRestrictionCalculus W P hres
  let S := proEtaleFlatRepresentatives X O
  have sigma := Functor.isoWhiskerLeft (S.ι.prod S.ι)
    (Functor.isoWhiskerRight c DerivedCategory.Qh) ≪≫ b.representative
  obtain ⟨tau', _⟩ := wfHomotopyRestrictionIso S P (fun K ↦ (hP _).1 K.property)
    (B ⋙ DerivedCategory.Qh)
    ((DerivedCategory.Qh.prod DerivedCategory.Qh) ⋙ b.tensor) sigma
  have tau : (L.prod L) ⋙ b.tensor ≅ (P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh := tau'.symm
  let F' := F ⋙ (Functor.whiskeringRight _ _ H).obj Q
  have ec : Functor.uncurry.obj F ⋙ Q ≅ Functor.uncurry.obj F' :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro MN MN' fg
      change Q.map ((F.map fg.1).app MN.2 ≫ (F.obj MN'.1).map fg.2) ≫ 𝟙 _ =
        𝟙 _ ≫ (Q.map ((F.map fg.1).app MN.2) ≫ Q.map ((F.obj MN'.1).map fg.2))
      rw [Q.map_comp, Category.id_comp, Category.comp_id])
  have hf (M : CochainComplex C ℤ) : (F'.obj M).Additive ∧ (F'.obj M).Linear A := by
    have : (F.obj M).Linear A := wfTotalRight_linear X d M
    change (F.obj M ⋙ Q).Additive ∧ (F.obj M ⋙ Q).Linear A
    exact ⟨inferInstance, inferInstance⟩
  have hf' (M : CochainComplex C ℤ) :
      (F'.flip.obj M).Additive ∧ (F'.flip.obj M).Linear A := by
    have : (F.flip.obj M).Linear A := wfTotalLeft_linear X d M
    change (F.flip.obj M ⋙ Q).Additive ∧ (F.flip.obj M ⋙ Q).Linear A
    exact ⟨inferInstance, inferInstance⟩
  have hB := wfBothTransfer Q F' B (c ≪≫ ec) hf hf' (wfTransferFull Q)
  let U := Functor.curry.obj ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh)
  have hu (M : P.FullSubcategory) : (U.obj M).Additive ∧ (U.obj M).Linear A := by
    have h := hB.1 M.obj
    let := h.1
    let := h.2
    let i : U.obj M ≅ P.ι ⋙ (Functor.curry.obj B).obj M.obj ⋙ DerivedCategory.Qh :=
      (Functor.curryObjProdComp P.ι P.ι (B ⋙ DerivedCategory.Qh)).app M
    exact ⟨Functor.additive_of_iso i.symm, Functor.linear_of_iso A i.symm⟩
  have hu' (M : P.FullSubcategory) :
      (U.flip.obj M).Additive ∧ (U.flip.obj M).Linear A := by
    have h := hB.2 M.obj
    let := h.1
    let := h.2
    let i : U.flip.obj M ≅ P.ι ⋙ (Functor.curry.obj B).flip.obj M.obj ⋙
        DerivedCategory.Qh :=
      ((CategoryTheory.flipFunctor _ _ _).mapIso
        (Functor.curryObjProdComp P.ι P.ι (B ⋙ DerivedCategory.Qh))).app M
    exact ⟨Functor.additive_of_iso i.symm, Functor.linear_of_iso A i.symm⟩
  exact wfBothTransfer L U b.tensor
    (tau ≪≫ (Functor.currying.counitIso.app
      ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh)).symm)
    hu hu' (wfTransferLocalization L V)
end AlgebraicGeometry.Scheme
