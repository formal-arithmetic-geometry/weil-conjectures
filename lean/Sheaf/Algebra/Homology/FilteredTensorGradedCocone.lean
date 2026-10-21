/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Algebra.Homology.FilteredTensorLocalizationSetup
import all Sheaf.Algebra.Homology.FilteredQuasiIsoTwoOutOfThree

/-! # Descent of the convolution graded comparison

Source: Stacks Project, More on Algebra, Tag 0H7Y, and Derived Categories, Tags 05S2--05S3.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor

namespace CochainComplex

variable {R : Type u} [CommRing R]

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

private noncomputable def cofanIsColimitOfIso
    {C : Type*} [Category* C] {I : Type*} {A B : I → C} {X Y : C}
    (a : ∀ i, A i ≅ B i) (p : X ≅ Y)
    (f : ∀ i, A i ⟶ X) (g : ∀ i, B i ⟶ Y)
    (h : ∀ i, f i ≫ p.hom = (a i).hom ≫ g i)
    (ht : IsColimit (Cofan.mk Y g)) : IsColimit (Cofan.mk X f) := by
  refine Cofan.IsColimit.mk _
    (fun t ↦ p.hom ≫ ht.desc (Cofan.mk t.pt (fun i ↦ (a i).inv ≫ t.inj i))) ?_ ?_
  · intro t i
    change f i ≫ p.hom ≫ _ = _
    rw [← Category.assoc, h i]
    simp only [Category.assoc]
    erw [ht.fac (Cofan.mk t.pt (fun i ↦ (a i).inv ≫ t.inj i)) (Discrete.mk i)]
    exact Iso.hom_inv_id_assoc (a i) (t.inj i)
  · intro t m hm
    change ∀ i, f i ≫ m = t.inj i at hm
    apply (cancel_epi p.inv).1
    simp only [Iso.inv_hom_id_assoc]
    apply ht.hom_ext
    intro i
    change g i.as ≫ p.inv ≫ m = _
    have hi : g i.as ≫ p.inv = (a i.as).inv ≫ f i.as := by
      apply (cancel_epi (a i.as).hom).1
      simp only [Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ← h i.as, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hi, Category.assoc, hm i.as]
    rw [ht.fac (Cofan.mk t.pt (fun i ↦ (a i).inv ≫ t.inj i)) i]
    rfl

private abbrev comparisonHomObj (P : GoodFiniteFilteredModuleHomotopy R) :
    KunnethFilteredComplex R := ⟨P.obj.as.obj, P.property⟩

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
private theorem comparisonGoodMap_surjective
    {P P' : GoodFiniteFilteredModuleHomotopy R} (f : P ⟶ P') :
    ∃ f' : comparisonHomObj P ⟶ comparisonHomObj P',
      kunnethGoodRepresentativeMap f' = f := by
  let q := CategoryTheory.Quotient.functor (finiteFilteredModuleHomotopyRel R)
  refine ⟨ObjectProperty.homMk (q.preimage f.hom).hom, ?_⟩
  apply ObjectProperty.hom_ext
  exact q.map_preimage f.hom

private theorem kunneth_representative_lift_natural
    (E : (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (eE : (goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ≅
      goodFiniteFilteredModuleInclusion R ⋙ (finiteFilteredModuleQuasiIso R).Q)
    (H : (finiteFilteredModuleQuasiIso R).Localization ⥤ DerivedCategory (ModuleCat.{u} R))
    (FH : FiniteFilteredModuleHomotopy R ⥤ DerivedCategory (ModuleCat.{u} R))
    (hH : Localization.Lifting (finiteFilteredModuleQuasiIso R).Q
      (finiteFilteredModuleQuasiIso R) FH H)
    (T : FiniteFilteredModuleComplex R ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    (hobj : ∀ K : FiniteFilteredModuleHomotopy R, FH.obj K =
      HomologicalComplexUpToQuasiIso.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj (T.obj K.as)))
    (hmap : ∀ (K L : FiniteFilteredModuleHomotopy R) (f : K.as ⟶ L.as),
      FH.map ((finiteFilteredModuleHomotopyQuotient R).map f) =
        eqToHom (hobj ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
          HomologicalComplexUpToQuasiIso.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map (T.map f)) ≫
          eqToHom (hobj ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm)
    (P P' : KunnethFilteredComplex R) (f : P ⟶ P') :
    H.map (E.functor.map ((goodFiniteFilteredModuleQuasiIso R).Q.map
        (kunnethGoodRepresentativeMap f))) ≫
      (kunnethRepresentativeLiftIso E eE H FH hH (fun K ↦ T.obj K.as) hobj P').hom =
    (kunnethRepresentativeLiftIso E eE H FH hH (fun K ↦ T.obj K.as) hobj P).hom ≫
      DerivedCategory.Q.map (T.map (kunnethRepresentativeMap f)) := by
  let := hH
  have hn := eE.hom.naturality (kunnethGoodRepresentativeMap f)
  have hln := (Localization.Lifting.iso (finiteFilteredModuleQuasiIso R).Q
    (finiteFilteredModuleQuasiIso R) FH H).hom.naturality
      ((goodFiniteFilteredModuleInclusion R).map (kunnethGoodRepresentativeMap f))
  have hqn := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality
    (T.map (kunnethRepresentativeMap f))
  dsimp [kunnethRepresentativeLiftIso]
  dsimp only [Functor.comp_map] at hn hln hqn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hln]
  change _ = _
  have hm := hmap
    ((goodFiniteFilteredModuleInclusion R).obj (kunnethGoodRepresentative P))
    ((goodFiniteFilteredModuleInclusion R).obj (kunnethGoodRepresentative P'))
    (kunnethRepresentativeMap f)
  change FH.map ((goodFiniteFilteredModuleInclusion R).map
    (kunnethGoodRepresentativeMap f)) = _ at hm
  rw [hm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [hqn]
  rfl

private theorem filteredHom_ext {C : Type*} [Category* C] [Abelian C]
    {P Q : FilteredObject C} (f g : P ⟶ Q) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem kunneth_fixed_graded_cocone_data :
    ∃ cgr : ∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        kunnethDerivedGraded P.obj Q.obj a i ≅
          DerivedCategory.Q.obj (kunnethTensorGraded P.obj Q.obj a i),
      (∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        (cgr P Q a i).hom = Functor.LaxMonoidal.μ DerivedCategory.Q
          (P.obj.filtration.gradedPiece i) (Q.obj.filtration.gradedPiece (a - i))) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a : ℤ),
        Nonempty (IsColimit (Cofan.mk
          (DerivedCategory.Q.obj (∐ kunnethTensorGraded P.obj Q.obj a))
          (fun i ↦ (cgr P Q a i).hom ≫ DerivedCategory.Q.map
            (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i))))) := by
  classical
  let data := filteredTensor_graded_comparison.{u, w} (R := R)
  let spec := data.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  exact ⟨data.choose_spec.choose_spec.choose_spec.choose_spec.choose,
    spec.2.2.2.2.2.2.2.2.1, spec.2.2.2.2.2.2.2.2.2.1⟩

private theorem kunneth_fixed_comparison_eq :
    (fun (P Q : KunnethFilteredComplex R) (a : ℤ) ↦
      kunnethRepresentativeGradedComparison.{u, w} P Q a) =
      (filteredTensor_graded_comparison.{u, w} (R := R)).choose_spec.choose_spec.choose := by
  rfl

private theorem kunneth_native_graded_naturality :
    ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ),
        CategoryTheory.Limits.Sigma.map
          (f := kunnethTensorGraded P.obj Q.obj a)
          (g := kunnethTensorGraded P'.obj Q'.obj a)
          (fun i ↦ FilteredObject.gradedMapSteps f.hom i ⊗ₘ
            FilteredObject.gradedMapSteps g.hom (a - i)) ≫
          (kunnethRepresentativeGradedComparison.{u, w} P' Q' a).hom =
        (kunnethRepresentativeGradedComparison.{u, w} P Q a).hom ≫
          FilteredObject.gradedMapSteps ((filteredTensor_graded_comparison.{u, w} (R := R)).choose
            P P' Q Q' f g) a := by
  let data := filteredTensor_graded_comparison.{u, w} (R := R)
  let e₀ := data.choose_spec.choose_spec.choose
  let N (e : ∀ (P Q : KunnethFilteredComplex R) (a : ℤ),
      (∐ kunnethTensorGraded P.obj Q.obj a) ≅
        (kunnethConvolution P.obj Q.obj).gradedPiece a) : Prop :=
    ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ),
      CategoryTheory.Limits.Sigma.map
        (f := kunnethTensorGraded P.obj Q.obj a)
        (g := kunnethTensorGraded P'.obj Q'.obj a)
        (fun i ↦ FilteredObject.gradedMapSteps f.hom i ⊗ₘ
          FilteredObject.gradedMapSteps g.hom (a - i)) ≫ (e P' Q' a).hom =
      (e P Q a).hom ≫ FilteredObject.gradedMapSteps (data.choose P P' Q Q' f g) a
  have he : (fun (P Q : KunnethFilteredComplex R) (a : ℤ) ↦
      kunnethRepresentativeGradedComparison.{u, w} P Q a) = e₀ :=
    kunneth_fixed_comparison_eq
  have hN : N e₀ :=
    data.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.1
  change N (fun P Q a ↦ kunnethRepresentativeGradedComparison.{u, w} P Q a)
  exact Eq.mp (congrArg N he.symm) hN

private theorem kunneth_fixed_graded_naturality
    (m : ∀ (P P' Q Q' : KunnethFilteredComplex R) (_f : P ⟶ P') (_g : Q ⟶ Q'),
      kunnethConvolutionObject P.obj Q.obj ⟶ kunnethConvolutionObject P'.obj Q'.obj)
    (hm : ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
      (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom) :
    ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ),
        CategoryTheory.Limits.Sigma.map
          (f := kunnethTensorGraded P.obj Q.obj a)
          (g := kunnethTensorGraded P'.obj Q'.obj a)
          (fun i ↦ FilteredObject.gradedMapSteps f.hom i ⊗ₘ
            FilteredObject.gradedMapSteps g.hom (a - i)) ≫
          (kunnethRepresentativeGradedComparison.{u, w} P' Q' a).hom =
        (kunnethRepresentativeGradedComparison.{u, w} P Q a).hom ≫
          FilteredObject.gradedMapSteps (m P P' Q Q' f g) a := by
  let data := filteredTensor_graded_comparison.{u, w} (R := R)
  intro P P' Q Q' f g a
  have hm₀ := data.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
  have hm_eq : m P P' Q Q' f g = data.choose P P' Q Q' f g :=
    filteredHom_ext _ _ ((hm P P' Q Q' f g).trans (hm₀ P P' Q Q' f g).symm)
  rw [hm_eq]
  exact kunneth_native_graded_naturality P P' Q Q' f g a

private theorem kunneth_fixed_graded_data
    (m : ∀ (P P' Q Q' : KunnethFilteredComplex R) (_f : P ⟶ P') (_g : Q ⟶ Q'),
      kunnethConvolutionObject P.obj Q.obj ⟶ kunnethConvolutionObject P'.obj Q'.obj)
    (hm : ∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q'),
      (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom) :
    ∃ cgr : ∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        kunnethDerivedGraded P.obj Q.obj a i ≅
          DerivedCategory.Q.obj (kunnethTensorGraded P.obj Q.obj a i),
      (∀ (P Q : KunnethFilteredComplex R) (a i : ℤ),
        (cgr P Q a i).hom = Functor.LaxMonoidal.μ DerivedCategory.Q
          (P.obj.filtration.gradedPiece i) (Q.obj.filtration.gradedPiece (a - i))) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a : ℤ),
        Nonempty (IsColimit (Cofan.mk
          (DerivedCategory.Q.obj (∐ kunnethTensorGraded P.obj Q.obj a))
          (fun i ↦ (cgr P Q a i).hom ≫ DerivedCategory.Q.map
            (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i))))) ∧
      (∀ (P P' Q Q' : KunnethFilteredComplex R) (f : P ⟶ P') (g : Q ⟶ Q') (a : ℤ),
        CategoryTheory.Limits.Sigma.map
          (f := kunnethTensorGraded P.obj Q.obj a)
          (g := kunnethTensorGraded P'.obj Q'.obj a)
          (fun i ↦ FilteredObject.gradedMapSteps f.hom i ⊗ₘ
            FilteredObject.gradedMapSteps g.hom (a - i)) ≫
          (kunnethRepresentativeGradedComparison.{u, w} P' Q' a).hom =
        (kunnethRepresentativeGradedComparison.{u, w} P Q a).hom ≫
          FilteredObject.gradedMapSteps (m P P' Q Q' f g) a) := by
  obtain ⟨cgr, hcgr, hcolim⟩ := kunneth_fixed_graded_cocone_data (R := R)
  exact ⟨cgr, hcgr, hcolim, kunneth_fixed_graded_naturality m hm⟩

private theorem normalized_leg {C : Type*} [Category* C]
    {A B X Y Z D : C} (v : A ≅ B) (t : X ≅ Y) (z : Z ≅ D)
    (l : A ⟶ Y) (b : Y ⟶ Z) (d₀ : B ⟶ Z) (d : B ⟶ D) (ι : B ⟶ X)
    (hi : ι = v.inv ≫ l ≫ t.inv) (hn : v.hom ≫ d₀ = l ≫ b)
    (hd : d₀ = d ≫ z.inv) : ι ≫ t.hom ≫ b ≫ z.hom = d := by
  rw [hi]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% hn, Iso.inv_hom_id_assoc, hd]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem kunneth_raw_graded_cocone
    (E :
    (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (eE :
    (goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ≅
      goodFiniteFilteredModuleInclusion R ⋙ (finiteFilteredModuleQuasiIso R).Q)
    (F :
    GoodFiniteFilteredModuleHomotopy R ⥤
      GoodFiniteFilteredModuleHomotopy R ⥤
        (goodFiniteFilteredModuleQuasiIso R).Localization)
    (hconv : ∀ P Q : KunnethFilteredComplex R,
    HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    (hrep : ∀ P Q : KunnethFilteredComplex R,
    (F.obj (kunnethGoodRepresentative P)).obj (kunnethGoodRepresentative Q) =
      (goodFiniteFilteredModuleQuasiIso R).Q.obj
        (kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv P Q)))
    (m : ∀ (P P' Q Q' : KunnethFilteredComplex R)
      (_f : P ⟶ P') (_g : Q ⟶ Q'),
    kunnethConvolutionObject P.obj Q.obj ⟶
      kunnethConvolutionObject P'.obj Q'.obj)
    (hm : ∀ (P P' Q Q' : KunnethFilteredComplex R)
      (f : P ⟶ P') (g : Q ⟶ Q'),
    (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom)
    (hFmap : ∀ (P P' Q Q' : KunnethFilteredComplex R)
      (f : P ⟶ P') (g : Q ⟶ Q'),
    (F.map (kunnethGoodRepresentativeMap f)).app
          (kunnethGoodRepresentative Q) ≫
        (F.obj (kunnethGoodRepresentative P')).map
          (kunnethGoodRepresentativeMap g) =
      eqToHom (hrep P Q) ≫
        (goodFiniteFilteredModuleQuasiIso R).Q.map
          (kunnethGoodRepresentativeMap
            (kunnethConvolutionRepresentativeMap hconv
              (m P P' Q Q' f g))) ≫
        eqToHom (hrep P' Q').symm)
    (gr : ℤ →
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      DerivedCategory (ModuleCat.{u} R))
    (Fgr : ∀ _a : ℤ, FiniteFilteredModuleHomotopy R ⥤
    DerivedCategory (ModuleCat.{u} R))
    (hgr : ∀ a : ℤ, Localization.Lifting
    (finiteFilteredModuleQuasiIso R).Q
    (finiteFilteredModuleQuasiIso R)
    (Fgr a) (gr a))
    (hgro : ∀ (a : ℤ) (K : FiniteFilteredModuleHomotopy R),
    (Fgr a).obj K =
      HomologicalComplexUpToQuasiIso.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
          (K.as.obj.filtration.gradedPiece a)))
    (hgrmap : ∀ (a : ℤ) (K L : FiniteFilteredModuleHomotopy R)
      (f : K.as ⟶ L.as),
    (Fgr a).map ((finiteFilteredModuleHomotopyQuotient R).map f) =
      eqToHom
        (hgro a ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
        HomologicalComplexUpToQuasiIso.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
            (FilteredObject.gradedMapSteps f.hom a)) ≫
        eqToHom
          (hgro a
            ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm
        ) :
    ∃ (γ : ∀ (a i : ℤ) (P Q : GoodFiniteFilteredModuleHomotopy R),
        ((gr i).obj (kunnethLocalizedRepresentative E (comparisonHomObj P))) ⊗
          ((gr (a - i)).obj (kunnethLocalizedRepresentative E (comparisonHomObj Q))) ⟶
        (E.functor ⋙ gr a).obj ((F.obj P).obj Q)),
      (∀ (a i : ℤ) (P P' Q Q' : GoodFiniteFilteredModuleHomotopy R)
          (f : P ⟶ P') (g : Q ⟶ Q'),
        ((E.functor ⋙ gr i).map ((goodFiniteFilteredModuleQuasiIso R).Q.map f) ⊗ₘ
          (E.functor ⋙ gr (a - i)).map ((goodFiniteFilteredModuleQuasiIso R).Q.map g)) ≫
            γ a i P' Q' = γ a i P Q ≫ (E.functor ⋙ gr a).map
              ((F.map f).app Q ≫ (F.obj P').map g)) ∧
      (∀ (a : ℤ) (P Q : GoodFiniteFilteredModuleHomotopy R),
        Nonempty (IsColimit (Cofan.mk ((E.functor ⋙ gr a).obj ((F.obj P).obj Q))
          (fun i ↦ γ a i P Q)))) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a : ℤ),
        ∃ (cgr : ∀ i : ℤ, kunnethDerivedGraded P.obj Q.obj a i ≅
          DerivedCategory.Q.obj (kunnethTensorGraded P.obj Q.obj a i)),
        (∀ i : ℤ, (cgr i).hom = Functor.LaxMonoidal.μ DerivedCategory.Q
          (P.obj.filtration.gradedPiece i) (Q.obj.filtration.gradedPiece (a - i))) ∧
        ∀ i : ℤ,
          γ a i (kunnethGoodRepresentative P) (kunnethGoodRepresentative Q) ≫
            (E.functor ⋙ gr a).map (eqToHom (hrep P Q)) ≫
            (kunnethRepresentativeLiftIso E eE (gr a) (Fgr a) (hgr a)
              (fun K ↦ K.as.obj.filtration.gradedPiece a) (hgro a)
              (kunnethConvolutionRepresentative hconv P Q)).hom ≫
            (DerivedCategory.Q.mapIso (kunnethRepresentativeGradedComparison.{u, w} P Q a)).inv =
          ((kunnethRepresentativeLiftIso E eE (gr i) (Fgr i) (hgr i)
              (fun K ↦ K.as.obj.filtration.gradedPiece i) (hgro i) P).hom ⊗ₘ
            (kunnethRepresentativeLiftIso E eE (gr (a - i)) (Fgr (a - i)) (hgr (a - i))
              (fun K ↦ K.as.obj.filtration.gradedPiece (a - i)) (hgro (a - i)) Q).hom) ≫
            (cgr i).hom ≫ DerivedCategory.Q.map
              (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i)) := by
  classical
  obtain ⟨cgr, hcgr, hcolim, hn₀⟩ := kunneth_fixed_graded_data m hm
  let α (a : ℤ) (P : KunnethFilteredComplex R) :
      (gr a).obj (kunnethLocalizedRepresentative E P) ≅
        DerivedCategory.Q.obj (P.obj.filtration.gradedPiece a) :=
    kunnethRepresentativeLiftIso E eE (gr a) (Fgr a) (hgr a)
      (fun K ↦ K.as.obj.filtration.gradedPiece a) (hgro a) P
  let β (a : ℤ) (P Q : GoodFiniteFilteredModuleHomotopy R) :
      (E.functor ⋙ gr a).obj ((F.obj P).obj Q) ≅
        DerivedCategory.Q.obj ((kunnethConvolutionObject
          (comparisonHomObj P).obj (comparisonHomObj Q).obj).filtration.gradedPiece a) :=
    (E.functor ⋙ gr a).mapIso
      (eqToIso (hrep (comparisonHomObj P) (comparisonHomObj Q))) ≪≫
      α a (kunnethConvolutionRepresentative hconv (comparisonHomObj P) (comparisonHomObj Q))
  let γ (a i : ℤ) (P Q : GoodFiniteFilteredModuleHomotopy R) :=
    ((α i (comparisonHomObj P)).hom ⊗ₘ (α (a - i) (comparisonHomObj Q)).hom) ≫
      (cgr (comparisonHomObj P) (comparisonHomObj Q) a i).hom ≫
      DerivedCategory.Q.map (Sigma.ι
        (kunnethTensorGraded (comparisonHomObj P).obj (comparisonHomObj Q).obj a) i) ≫
      (DerivedCategory.Q.mapIso
        (kunnethRepresentativeGradedComparison.{u, w}
          (comparisonHomObj P) (comparisonHomObj Q) a)).hom ≫
      (β a P Q).inv
  have hα (a : ℤ) {P P' : KunnethFilteredComplex R} (f : P ⟶ P') :
      (E.functor ⋙ gr a).map ((goodFiniteFilteredModuleQuasiIso R).Q.map
        (kunnethGoodRepresentativeMap f)) ≫ (α a P').hom =
        (α a P).hom ≫ DerivedCategory.Q.map (FilteredObject.gradedMapSteps f.hom a) := by
    exact kunneth_representative_lift_natural E eE (gr a) (Fgr a) (hgr a)
      (gradedFunctor R a) (hgro a) (hgrmap a) P P' f
  have hβ (a : ℤ) {P P' Q Q' : GoodFiniteFilteredModuleHomotopy R}
      (f : comparisonHomObj P ⟶ comparisonHomObj P')
      (g : comparisonHomObj Q ⟶ comparisonHomObj Q') :
      (E.functor ⋙ gr a).map ((F.map (kunnethGoodRepresentativeMap f)).app Q ≫
        (F.obj P').map (kunnethGoodRepresentativeMap g)) ≫ (β a P' Q').hom =
        (β a P Q).hom ≫ DerivedCategory.Q.map (FilteredObject.gradedMapSteps
          (m _ _ _ _ f g) a) := by
    dsimp only [β, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
    have he := hFmap (comparisonHomObj P) (comparisonHomObj P')
      (comparisonHomObj Q) (comparisonHomObj Q') f g
    erw [he]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    erw [hα a (kunnethConvolutionRepresentativeMap hconv (m _ _ _ _ f g))]
    rfl
  have hγnorm (a : ℤ) (P Q : GoodFiniteFilteredModuleHomotopy R) (i : ℤ) :
      γ a i P Q ≫ (β a P Q).hom ≫
        (DerivedCategory.Q.mapIso
          (kunnethRepresentativeGradedComparison.{u, w}
          (comparisonHomObj P) (comparisonHomObj Q) a)).inv =
      ((α i (comparisonHomObj P)).hom ⊗ₘ (α (a - i) (comparisonHomObj Q)).hom) ≫
        (cgr (comparisonHomObj P) (comparisonHomObj Q) a i).hom ≫
        DerivedCategory.Q.map (Sigma.ι
          (kunnethTensorGraded (comparisonHomObj P).obj (comparisonHomObj Q).obj a) i) := by
    dsimp only [γ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro a i P P' Q Q' f g
    obtain ⟨f, rfl⟩ := comparisonGoodMap_surjective f
    obtain ⟨g, rfl⟩ := comparisonGoodMap_surjective g
    apply (cancel_mono (β a P' Q').hom).1
    simp only [Category.assoc]
    rw [hβ a f g]
    dsimp only [γ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, tensorHom_comp_tensorHom, hα i f, hα (a - i) g,
      ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    have hn := congrArg DerivedCategory.Q.map
      (hn₀ (comparisonHomObj P) (comparisonHomObj P')
        (comparisonHomObj Q) (comparisonHomObj Q') f g a)
    simp only [Functor.map_comp] at hn
    have hμ := Functor.LaxMonoidal.μ_natural DerivedCategory.Q
      (FilteredObject.gradedMapSteps f.hom i)
      (FilteredObject.gradedMapSteps g.hom (a - i))
    rw [← hcgr (comparisonHomObj P) (comparisonHomObj Q) a i,
      ← hcgr (comparisonHomObj P') (comparisonHomObj Q') a i] at hμ
    rw [reassoc_of% hμ]
    have hi := congrArg DerivedCategory.Q.map
      (CategoryTheory.Limits.Sigma.ι_map
        (f := kunnethTensorGraded (comparisonHomObj P).obj (comparisonHomObj Q).obj a)
        (g := kunnethTensorGraded (comparisonHomObj P').obj (comparisonHomObj Q').obj a)
        (fun j ↦ FilteredObject.gradedMapSteps f.hom j ⊗ₘ
          FilteredObject.gradedMapSteps g.hom (a - j)) i)
    simp only [Functor.map_comp] at hi
    erw [← reassoc_of% hi]
    simp only [Iso.inv_hom_id, Category.comp_id, Functor.mapIso_hom]
    exact congrArg
      (((α i (comparisonHomObj P)).hom ⊗ₘ (α (a - i) (comparisonHomObj Q)).hom) ≫
        (cgr (comparisonHomObj P) (comparisonHomObj Q) a i).hom ≫
          DerivedCategory.Q.map (Sigma.ι
            (kunnethTensorGraded (comparisonHomObj P).obj (comparisonHomObj Q).obj a) i) ≫ ·) hn
  · intro a P Q
    refine ⟨cofanIsColimitOfIso
      (fun i ↦ tensorIso (α i (comparisonHomObj P)) (α (a - i) (comparisonHomObj Q)))
      (β a P Q ≪≫ (DerivedCategory.Q.mapIso
        (kunnethRepresentativeGradedComparison.{u, w}
          (comparisonHomObj P) (comparisonHomObj Q) a)).symm)
      (fun i ↦ γ a i P Q) _ (fun i ↦ hγnorm a P Q i) ?_⟩
    exact (hcolim (comparisonHomObj P) (comparisonHomObj Q) a).some
  · intro P Q a
    refine ⟨cgr P Q a, hcgr P Q a, ?_⟩
    intro i
    have hh := hγnorm a (kunnethGoodRepresentative P) (kunnethGoodRepresentative Q) i
    simp only [β, α, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Category.assoc] at hh
    exact hh

private theorem kunneth_transport_bifunctor_leg
    (E :
    (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (F :
    GoodFiniteFilteredModuleHomotopy R ⥤
      GoodFiniteFilteredModuleHomotopy R ⥤
        (goodFiniteFilteredModuleQuasiIso R).Localization)
    (B :
    (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
      (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
        (goodFiniteFilteredModuleQuasiIso R).Localization)
    (hB : Localization.Lifting₂
    (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R)
    (goodFiniteFilteredModuleQuasiIso R) F B)
    (star :
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      (finiteFilteredModuleQuasiIso R).Localization ⥤
        (finiteFilteredModuleQuasiIso R).Localization)
    (τ : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
    (star.obj U).obj V ≅
      E.functor.obj ((B.obj (E.inverse.obj U)).obj (E.inverse.obj V)))
    (hτ : ∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
      (f : U ⟶ U') (g : V ⟶ V'),
    (τ U V).hom ≫
        E.functor.map ((B.map (E.inverse.map f)).app (E.inverse.obj V) ≫
          (B.obj (E.inverse.obj U')).map (E.inverse.map g)) =
      (star.map f).app V ≫ (star.obj U').map g ≫ (τ U' V').hom)
    (omega :
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      DerivedCategory (ModuleCat.{u} R))
    (omega₁ omega₂ : (finiteFilteredModuleQuasiIso R).Localization ⥤
      DerivedCategory (ModuleCat.{u} R))
    (d : ((whiskeringLeft₂ _).obj
        ((goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ⋙ omega₁) |>.obj
        ((goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ⋙ omega₂)).obj
          (curriedTensor (DerivedCategory (ModuleCat.{u} R))) ⟶
      F ⋙ (whiskeringRight _ _ _).obj (E.functor ⋙ omega)) :
    ∃ ι : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
      omega₁.obj U ⊗ omega₂.obj V ⟶ omega.obj ((star.obj U).obj V),
      (∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
          (f : U ⟶ U') (g : V ⟶ V'),
        (omega₁.map f ⊗ₘ omega₂.map g) ≫ ι U' V' =
          ι U V ≫ omega.map ((star.map f).app V ≫ (star.obj U').map g)) ∧
      ∀ P Q : GoodFiniteFilteredModuleHomotopy R,
        let qP := (goodFiniteFilteredModuleQuasiIso R).Q.obj P
        let qQ := (goodFiniteFilteredModuleQuasiIso R).Q.obj Q
        ι (E.functor.obj qP) (E.functor.obj qQ) ≫
          omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).hom ≫
          (E.functor ⋙ omega).map
            ((B.map (E.unitIso.symm.app qP).hom).app
                (E.inverse.obj (E.functor.obj qQ)) ≫
              (B.obj qP).map (E.unitIso.symm.app qQ).hom) ≫
          (E.functor ⋙ omega).map
            (((Localization.Lifting₂.iso (goodFiniteFilteredModuleQuasiIso R).Q
              (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
              (goodFiniteFilteredModuleQuasiIso R) F B).app P).app Q).hom =
          (d.app P).app Q := by
  classical
  let W := E.functor ⋙ omega
  let W₁ := E.functor ⋙ omega₁
  let W₂ := E.functor ⋙ omega₂
  let O₁ := (goodFiniteFilteredModuleQuasiIso R).Q ⋙ W₁
  let O₂ := (goodFiniteFilteredModuleQuasiIso R).Q ⋙ W₂
  let A := F ⋙ (whiskeringRight _ _ _).obj W
  let T := ((whiskeringLeft₂ _).obj O₁ |>.obj O₂).obj
    (curriedTensor (DerivedCategory (ModuleCat.{u} R)))
  let BL := B ⋙ (whiskeringRight _ _ _).obj W
  let TL := ((whiskeringLeft₂ _).obj W₁ |>.obj W₂).obj
    (curriedTensor (DerivedCategory (ModuleCat.{u} R)))
  let := hB
  let : (goodFiniteFilteredModuleQuasiIso R).ContainsIdentities :=
    { id_mem := fun P ↦ finiteFilteredModuleQuasiIso_id R P.obj }
  let : Localization.Lifting₂ (goodFiniteFilteredModuleQuasiIso R).Q
      (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
      (goodFiniteFilteredModuleQuasiIso R) A BL := inferInstance
  let : Localization.Lifting₂ (goodFiniteFilteredModuleQuasiIso R).Q
      (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
      (goodFiniteFilteredModuleQuasiIso R) T TL := ⟨Iso.refl _⟩
  let dL := Localization.lift₂NatTrans (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
    (goodFiniteFilteredModuleQuasiIso R) T A TL BL d
  have hdL {U U' V V' : (goodFiniteFilteredModuleQuasiIso R).Localization}
      (f : U ⟶ U') (g : V ⟶ V') :
      (W₁.map f ⊗ₘ W₂.map g) ≫ (dL.app U').app V' =
        (dL.app U).app V ≫ W.map ((B.map f).app V ≫ (B.obj U').map g) := by
    have hf := NatTrans.congr_app (dL.naturality f) V
    have hg := (dL.app U').naturality g
    dsimp only [NatTrans.comp_app] at hf
    change (W₁.map f ▷ W₂.obj V) ≫ (dL.app U').app V =
      (dL.app U).app V ≫ W.map ((B.map f).app V) at hf
    change (W₁.obj U' ◁ W₂.map g) ≫ (dL.app U').app V' =
      (dL.app U').app V ≫ W.map ((B.obj U').map g) at hg
    rw [tensorHom_def, Category.assoc, hg, ← Category.assoc, hf]
    simp only [Category.assoc, ← Functor.map_comp]
  let ι (U V : (finiteFilteredModuleQuasiIso R).Localization) :=
    (omega₁.map (E.counitIso.app U).inv ⊗ₘ omega₂.map (E.counitIso.app V).inv) ≫
      (dL.app (E.inverse.obj U)).app (E.inverse.obj V) ≫ omega.map (τ U V).inv
  refine ⟨ι, ?_, ?_⟩
  · intro U U' V V' f g
    have hcf := congrArg omega₁.map (E.counitIso.inv.naturality f)
    have hcg := congrArg omega₂.map (E.counitIso.inv.naturality g)
    dsimp only [Functor.comp_map, Functor.id_map] at hcf hcg
    simp only [Functor.map_comp] at hcf hcg
    have hct :
        (omega₁.map f ⊗ₘ omega₂.map g) ≫
          (omega₁.map (E.counitIso.app U').inv ⊗ₘ omega₂.map (E.counitIso.app V').inv) =
        (omega₁.map (E.counitIso.app U).inv ⊗ₘ omega₂.map (E.counitIso.app V).inv) ≫
          (W₁.map (E.inverse.map f) ⊗ₘ W₂.map (E.inverse.map g)) := by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      erw [hcf, hcg]
      rfl
    have hτinv : E.functor.map ((B.map (E.inverse.map f)).app (E.inverse.obj V) ≫
        (B.obj (E.inverse.obj U')).map (E.inverse.map g)) ≫ (τ U' V').inv =
        (τ U V).inv ≫ ((star.map f).app V ≫ (star.obj U').map g) := by
      apply (cancel_epi (τ U V).hom).1
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [hτ U U' V V' f g]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hτm := congrArg omega.map hτinv
    rw [omega.map_comp, omega.map_comp] at hτm
    dsimp only [ι]
    simp only [Category.assoc]
    rw [← Category.assoc, ← Category.assoc, hct]
    simp only [Category.assoc]
    rw [reassoc_of% hdL (E.inverse.map f) (E.inverse.map g)]
    exact congrArg
      ((omega₁.map (E.counitIso.app U).inv ⊗ₘ omega₂.map (E.counitIso.app V).inv) ≫
        (dL.app (E.inverse.obj U)).app (E.inverse.obj V) ≫ ·) hτm
  · intro P Q
    let qP := (goodFiniteFilteredModuleQuasiIso R).Q.obj P
    let qQ := (goodFiniteFilteredModuleQuasiIso R).Q.obj Q
    let uP := E.unitIso.symm.app qP
    let uQ := E.unitIso.symm.app qQ
    let v := tensorIso (W₁.mapIso uP) (W₂.mapIso uQ)
    let b := W.map ((B.map uP.hom).app (E.inverse.obj (E.functor.obj qQ)) ≫
      (B.obj qP).map uQ.hom)
    let z := W.mapIso (((Localization.Lifting₂.iso (goodFiniteFilteredModuleQuasiIso R).Q
      (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
      (goodFiniteFilteredModuleQuasiIso R) F B).app P).app Q)
    have hdrep : (dL.app qP).app qQ = (d.app P).app Q ≫ z.inv := by
      erw [Localization.lift₂NatTrans_app_app]
      change (𝟙 _) ≫ _ ≫ _ = _
      rw [Category.id_comp]
      rfl
    have hct : (omega₁.map (E.counitIso.app (E.functor.obj qP)).inv ⊗ₘ
        omega₂.map (E.counitIso.app (E.functor.obj qQ)).inv) = v.inv := by
      have hp := congrArg omega₁.map (E.counitInv_app_functor qP)
      have hq := congrArg omega₂.map (E.counitInv_app_functor qQ)
      exact congrArg₂ (fun f g ↦ f ⊗ₘ g) hp hq
    have hh : ι (E.functor.obj qP) (E.functor.obj qQ) =
        v.inv ≫ (dL.app (E.inverse.obj (E.functor.obj qP))).app
          (E.inverse.obj (E.functor.obj qQ)) ≫
          omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).inv :=
      congrArg (fun t ↦ t ≫ (dL.app (E.inverse.obj (E.functor.obj qP))).app
        (E.inverse.obj (E.functor.obj qQ)) ≫
          omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).inv) hct
    have hn : v.hom ≫ (dL.app qP).app qQ =
        (dL.app (E.inverse.obj (E.functor.obj qP))).app
          (E.inverse.obj (E.functor.obj qQ)) ≫ b := hdL uP.hom uQ.hom
    change ι (E.functor.obj qP) (E.functor.obj qQ) ≫
      omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).hom ≫ b ≫ z.hom = _
    exact normalized_leg v (omega.mapIso (τ (E.functor.obj qP) (E.functor.obj qQ))) z
      ((dL.app (E.inverse.obj (E.functor.obj qP))).app
        (E.inverse.obj (E.functor.obj qQ))) b ((dL.app qP).app qQ) ((d.app P).app Q)
      (ι (E.functor.obj qP) (E.functor.obj qQ)) hh hn hdrep

private theorem kunneth_star_hom_decomposition
    (E :
    (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (F :
    GoodFiniteFilteredModuleHomotopy R ⥤
      GoodFiniteFilteredModuleHomotopy R ⥤
        (goodFiniteFilteredModuleQuasiIso R).Localization)
    (B :
    (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
      (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
        (goodFiniteFilteredModuleQuasiIso R).Localization)
    (hB : Localization.Lifting₂
    (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R)
    (goodFiniteFilteredModuleQuasiIso R) F B)
    (hconv : ∀ P Q : KunnethFilteredComplex R,
    HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    (hrep : ∀ P Q : KunnethFilteredComplex R,
    (F.obj (kunnethGoodRepresentative P)).obj (kunnethGoodRepresentative Q) =
      (goodFiniteFilteredModuleQuasiIso R).Q.obj
        (kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv P Q)))
    (star :
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      (finiteFilteredModuleQuasiIso R).Localization ⥤
        (finiteFilteredModuleQuasiIso R).Localization)
    (τ : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
    (star.obj U).obj V ≅
      E.functor.obj ((B.obj (E.inverse.obj U)).obj (E.inverse.obj V)))
    (omega : (finiteFilteredModuleQuasiIso R).Localization ⥤
      DerivedCategory (ModuleCat.{u} R)) (P Q : KunnethFilteredComplex R) :
    omega.map (kunnethStarRepresentativeIso E F B hB hconv hrep star τ P Q).hom =
      omega.map (τ (kunnethLocalizedRepresentative E P)
        (kunnethLocalizedRepresentative E Q)).hom ≫
      (E.functor ⋙ omega).map
        ((B.map (E.unitIso.symm.app ((goodFiniteFilteredModuleQuasiIso R).Q.obj
          (kunnethGoodRepresentative P))).hom).app
            (E.inverse.obj (kunnethLocalizedRepresentative E Q)) ≫
          (B.obj ((goodFiniteFilteredModuleQuasiIso R).Q.obj
            (kunnethGoodRepresentative P))).map
              (E.unitIso.symm.app ((goodFiniteFilteredModuleQuasiIso R).Q.obj
                (kunnethGoodRepresentative Q))).hom) ≫
      (E.functor ⋙ omega).map
        (((@Localization.Lifting₂.iso _ _ _ _ _ _ _ _ _ _
          (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R).Q
          (goodFiniteFilteredModuleQuasiIso R) (goodFiniteFilteredModuleQuasiIso R) F B hB).app
            (kunnethGoodRepresentative P)).app (kunnethGoodRepresentative Q)).hom ≫
      (E.functor ⋙ omega).map (eqToHom (hrep P Q)) := by
  dsimp only [kunnethStarRepresentativeIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, eqToIso.hom,
    Functor.comp_map, Functor.map_comp, Category.assoc]

private def kunnethNatTrans₂OfComponents
    {C D A : Type*} [Category* C] [Category* D] [Category* A]
    {F G : C ⥤ D ⥤ A} (e : ∀ P Q, (F.obj P).obj Q ⟶ (G.obj P).obj Q)
    (he : ∀ {P P' : C} {Q Q' : D} (f : P ⟶ P') (g : Q ⟶ Q'),
      ((F.map f).app Q ≫ (F.obj P').map g) ≫ e P' Q' =
        e P Q ≫ ((G.map f).app Q ≫ (G.obj P').map g)) : F ⟶ G where
  app P :=
    { app := e P
      naturality := by
        intro Q Q' g
        simpa using he (𝟙 P) g }
  naturality := by
    intro P P' f
    exact NatTrans.ext (funext (fun Q ↦ by simpa using he f (𝟙 Q)))

private noncomputable def cofanIsColimitToIso
    {C : Type*} [Category* C] {I : Type*} {A B : I → C} {X Y : C}
    (a : ∀ i, A i ≅ B i) (p : X ≅ Y)
    (f : ∀ i, A i ⟶ X) (g : ∀ i, B i ⟶ Y)
    (h : ∀ i, f i ≫ p.hom = (a i).hom ≫ g i)
    (ht : IsColimit (Cofan.mk X f)) : IsColimit (Cofan.mk Y g) := by
  refine cofanIsColimitOfIso (fun i ↦ (a i).symm) p.symm g f ?_ ht
  intro i
  apply (cancel_epi (a i).hom).1
  simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h i, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The normalized derived graded coproduct cocone descends to the localized
convolution tensor, naturally in the two variables.
Source: Stacks Project, More on Algebra, convolution comparison before Tag 0H7W
and Tag 0H7Y; Derived Categories, Tags 05S2--05S3.
(blueprint: lem-kun-filtered-tensor-graded-cocone).

Proof. Choose the particular comparison and coproduct cocone selected in
kunnethRepresentativeGradedComparison. Their legs on good representatives are
cgr.hom followed by Q of the complex coprojection, Q of the residue-class
comparison, and the inverses of the fixed representative lift isomorphisms.
Naturality of the quotient lax monoidal comparison and naturality of the
residue-class comparison show that each leg is natural in both filtered maps.
The equation hm uniquely fixes the underlying filtered tensor map, so this
naturality uses the supplied m. The formula hFmap and the single-variable
formulas hgrmap give the same squares on good filtered homotopy classes.

Localize these natural transformations in both variables with
Localization.lift₂NatTrans. The tensor functor on each pair of localized graded
pieces is already a lift of its restriction. Transport along E.inverse in both
variables, along the equivalence counit on the two graded factors, and along the
inverse of tau on the target. This gives the displayed legs for star. Naturality
holds for all localized maps by the product localization universal property.

The original representative cocone is colimiting, and all the representative lift
maps, residue-class comparisons, and equivalence comparisons are isomorphisms.
Transport of a colimit cocone by these isomorphisms proves that the resulting
cocone is colimiting on representatives. Every localized object is isomorphic to
the image of a good representative, by essential surjectivity of the quotient and
the replacement equivalence. Naturality transports the colimit assertion to all
pairs of objects. The lift-two component formula and the equivalence triangle
identities cancel the inverse replacement maps on a representative; composing
with the displayed star and graded lift isomorphisms gives exactly the stated
leg equation. No finite support is chosen in this result. -/
theorem filteredTensor_localized_graded_cocone
    (E :
    (goodFiniteFilteredModuleQuasiIso R).Localization ≌
      (finiteFilteredModuleQuasiIso R).Localization)
    (eE :
    (goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ≅
      goodFiniteFilteredModuleInclusion R ⋙ (finiteFilteredModuleQuasiIso R).Q)
    (F :
    GoodFiniteFilteredModuleHomotopy R ⥤
      GoodFiniteFilteredModuleHomotopy R ⥤
        (goodFiniteFilteredModuleQuasiIso R).Localization)
    (B :
    (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
      (goodFiniteFilteredModuleQuasiIso R).Localization ⥤
        (goodFiniteFilteredModuleQuasiIso R).Localization)
    (hB : Localization.Lifting₂
    (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R)
    (goodFiniteFilteredModuleQuasiIso R) F B)
    (hconv : ∀ P Q : KunnethFilteredComplex R,
    HasKunnethFiltration (kunnethConvolutionObject P.obj Q.obj))
    (hrep : ∀ P Q : KunnethFilteredComplex R,
    (F.obj (kunnethGoodRepresentative P)).obj (kunnethGoodRepresentative Q) =
      (goodFiniteFilteredModuleQuasiIso R).Q.obj
        (kunnethGoodRepresentative (kunnethConvolutionRepresentative hconv P Q)))
    (m : ∀ (P P' Q Q' : KunnethFilteredComplex R)
      (_f : P ⟶ P') (_g : Q ⟶ Q'),
    kunnethConvolutionObject P.obj Q.obj ⟶
      kunnethConvolutionObject P'.obj Q'.obj)
    (hm : ∀ (P P' Q Q' : KunnethFilteredComplex R)
      (f : P ⟶ P') (g : Q ⟶ Q'),
    (m P P' Q Q' f g).hom = f.hom.hom ⊗ₘ g.hom.hom)
    (hFmap : ∀ (P P' Q Q' : KunnethFilteredComplex R)
      (f : P ⟶ P') (g : Q ⟶ Q'),
    (F.map (kunnethGoodRepresentativeMap f)).app
          (kunnethGoodRepresentative Q) ≫
        (F.obj (kunnethGoodRepresentative P')).map
          (kunnethGoodRepresentativeMap g) =
      eqToHom (hrep P Q) ≫
        (goodFiniteFilteredModuleQuasiIso R).Q.map
          (kunnethGoodRepresentativeMap
            (kunnethConvolutionRepresentativeMap hconv
              (m P P' Q Q' f g))) ≫
        eqToHom (hrep P' Q').symm)
    (star :
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      (finiteFilteredModuleQuasiIso R).Localization ⥤
        (finiteFilteredModuleQuasiIso R).Localization)
    (τ : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
    (star.obj U).obj V ≅
      E.functor.obj ((B.obj (E.inverse.obj U)).obj (E.inverse.obj V)))
    (hτ : ∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
      (f : U ⟶ U') (g : V ⟶ V'),
    (τ U V).hom ≫
        E.functor.map ((B.map (E.inverse.map f)).app (E.inverse.obj V) ≫
          (B.obj (E.inverse.obj U')).map (E.inverse.map g)) =
      (star.map f).app V ≫ (star.obj U').map g ≫ (τ U' V').hom)
    (gr : ℤ →
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      DerivedCategory (ModuleCat.{u} R))
    (Fgr : ∀ _a : ℤ, FiniteFilteredModuleHomotopy R ⥤
    DerivedCategory (ModuleCat.{u} R))
    (hgr : ∀ a : ℤ, Localization.Lifting
    (finiteFilteredModuleQuasiIso R).Q
    (finiteFilteredModuleQuasiIso R)
    (Fgr a) (gr a))
    (hgro : ∀ (a : ℤ) (K : FiniteFilteredModuleHomotopy R),
    (Fgr a).obj K =
      HomologicalComplexUpToQuasiIso.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
          (K.as.obj.filtration.gradedPiece a)))
    (hgrmap : ∀ (a : ℤ) (K L : FiniteFilteredModuleHomotopy R)
      (f : K.as ⟶ L.as),
    (Fgr a).map ((finiteFilteredModuleHomotopyQuotient R).map f) =
      eqToHom
        (hgro a ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
        HomologicalComplexUpToQuasiIso.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
            (FilteredObject.gradedMapSteps f.hom a)) ≫
        eqToHom
          (hgro a
            ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm
        ) :
    ∃ (ι : ∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization) (i : ℤ),
        ((gr i).obj U) ⊗ ((gr (a - i)).obj V) ⟶
          (gr a).obj ((star.obj U).obj V)),
      (∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization),
        Nonempty (IsColimit (Cofan.mk ((gr a).obj ((star.obj U).obj V)) (ι a U V)))) ∧
      (∀ (a i : ℤ) (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
          (f : U ⟶ U') (g : V ⟶ V'),
        ((gr i).map f ⊗ₘ (gr (a - i)).map g) ≫ ι a U' V' i =
          ι a U V i ≫ (gr a).map ((star.map f).app V ≫ (star.obj U').map g)) ∧
      (∀ (P Q : KunnethFilteredComplex R) (a : ℤ),
        ∃ (cgr : ∀ i : ℤ,
          kunnethDerivedGraded P.obj Q.obj a i ≅
            DerivedCategory.Q.obj (kunnethTensorGraded P.obj Q.obj a i)),
          (∀ i : ℤ, (cgr i).hom = Functor.LaxMonoidal.μ DerivedCategory.Q
            (P.obj.filtration.gradedPiece i)
            (Q.obj.filtration.gradedPiece (a - i))) ∧
          ∀ i : ℤ,
            ι a (kunnethLocalizedRepresentative E P) (kunnethLocalizedRepresentative E Q) i ≫
              (gr a).map (kunnethStarRepresentativeIso E F B hB hconv hrep star τ P Q).hom ≫
              (kunnethRepresentativeLiftIso E eE (gr a) (Fgr a) (hgr a)
                (fun K ↦ K.as.obj.filtration.gradedPiece a) (hgro a)
                (kunnethConvolutionRepresentative hconv P Q)).hom ≫
              (DerivedCategory.Q.mapIso (kunnethRepresentativeGradedComparison.{u, w} P Q a)).inv =
            ((kunnethRepresentativeLiftIso E eE (gr i) (Fgr i) (hgr i)
                (fun K ↦ K.as.obj.filtration.gradedPiece i) (hgro i) P).hom ⊗ₘ
              (kunnethRepresentativeLiftIso E eE (gr (a - i)) (Fgr (a - i)) (hgr (a - i))
                (fun K ↦ K.as.obj.filtration.gradedPiece (a - i)) (hgro (a - i)) Q).hom) ≫
              (cgr i).hom ≫ DerivedCategory.Q.map
                (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i)) := by
  classical
  obtain ⟨γ, hγ, hγcolim, hγpin⟩ := kunneth_raw_graded_cocone
    E eE F hconv hrep m hm hFmap gr Fgr hgr hgro hgrmap
  let O (i : ℤ) := (goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ⋙ gr i
  let A (a : ℤ) := F ⋙ (whiskeringRight _ _ _).obj (E.functor ⋙ gr a)
  let T (a i : ℤ) := ((whiskeringLeft₂ _).obj (O i) |>.obj (O (a - i))).obj
    (curriedTensor (DerivedCategory (ModuleCat.{u} R)))
  let d (a i : ℤ) : T a i ⟶ A a := kunnethNatTrans₂OfComponents (γ a i) (by
    intro P P' Q Q' f g
    have h := hγ a i P P' Q Q' f g
    change ((O i).map f ▷ (O (a - i)).obj Q ≫
        ((O i).obj P' ◁ (O (a - i)).map g)) ≫ γ a i P' Q' =
      γ a i P Q ≫ ((E.functor ⋙ gr a).map ((F.map f).app Q) ≫
        (E.functor ⋙ gr a).map ((F.obj P').map g))
    rw [← tensorHom_def, ← Functor.map_comp]
    exact h)
  have hl (a i : ℤ) := kunneth_transport_bifunctor_leg
    E F B hB star τ hτ (gr a) (gr i) (gr (a - i)) (d a i)
  choose ρ hρ hn using hl
  let := hB
  have hstar (a i : ℤ) (P Q : KunnethFilteredComplex R) :
      ρ a i (kunnethLocalizedRepresentative E P) (kunnethLocalizedRepresentative E Q) ≫
        (gr a).map (kunnethStarRepresentativeIso E F B hB hconv hrep star τ P Q).hom =
      γ a i (kunnethGoodRepresentative P) (kunnethGoodRepresentative Q) ≫
        (E.functor ⋙ gr a).map (eqToHom (hrep P Q)) := by
    rw [kunneth_star_hom_decomposition]
    simpa only [Category.assoc, d, kunnethNatTrans₂OfComponents] using congrArg
      (· ≫ (E.functor ⋙ gr a).map (eqToHom (hrep P Q)))
        (hn a i (kunnethGoodRepresentative P) (kunnethGoodRepresentative Q))
  let N (a : ℤ) (P Q : GoodFiniteFilteredModuleHomotopy R) :=
    (gr a).mapIso (kunnethStarRepresentativeIso E F B hB hconv hrep star τ
      (comparisonHomObj P) (comparisonHomObj Q)) ≪≫
    ((E.functor ⋙ gr a).mapIso
      (eqToIso (hrep (comparisonHomObj P) (comparisonHomObj Q)))).symm
  have hN (a : ℤ) (P Q : GoodFiniteFilteredModuleHomotopy R) (i : ℤ) :
      ρ a i (kunnethLocalizedRepresentative E (comparisonHomObj P))
        (kunnethLocalizedRepresentative E (comparisonHomObj Q)) ≫ (N a P Q).hom =
          γ a i P Q := by
    dsimp only [N, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← Category.assoc, hstar]
    let r := (E.functor ⋙ gr a).mapIso
      (eqToIso (hrep (comparisonHomObj P) (comparisonHomObj Q)))
    change (γ a i (kunnethGoodRepresentative (comparisonHomObj P))
      (kunnethGoodRepresentative (comparisonHomObj Q)) ≫ r.hom) ≫ r.inv = γ a i P Q
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have hcolimrep (a : ℤ) (P Q : GoodFiniteFilteredModuleHomotopy R) :
      Nonempty (IsColimit (Cofan.mk
        ((gr a).obj ((star.obj (kunnethLocalizedRepresentative E (comparisonHomObj P))).obj
          (kunnethLocalizedRepresentative E (comparisonHomObj Q))))
        (fun i ↦ ρ a i (kunnethLocalizedRepresentative E (comparisonHomObj P))
          (kunnethLocalizedRepresentative E (comparisonHomObj Q))))) := by
    exact ⟨cofanIsColimitOfIso (fun _ ↦ Iso.refl _) (N a P Q) _ _
      (fun i ↦ by simpa only [Iso.refl_hom, Category.id_comp] using hN a P Q i)
        (hγcolim a P Q).some⟩
  refine ⟨fun a U V i ↦ ρ a i U V, ?_, hρ, ?_⟩
  · intro a U V
    let L := (goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor
    let P := L.objPreimage U
    let Q := L.objPreimage V
    let eU := L.objObjPreimageIso U
    let eV := L.objObjPreimageIso V
    let p := (gr a).mapIso (((star.mapIso eU).app (L.obj Q)) ≪≫
      (star.obj U).mapIso eV)
    refine ⟨cofanIsColimitToIso
      (fun i ↦ tensorIso ((gr i).mapIso eU) ((gr (a - i)).mapIso eV)) p _ _
      (fun i ↦ ?_) (hcolimrep a P Q).some⟩
    exact (hρ a i (L.obj P) U (L.obj Q) V eU.hom eV.hom).symm
  · intro P Q a
    obtain ⟨cgr, hcgr, hp⟩ := hγpin P Q a
    refine ⟨cgr, hcgr, ?_⟩
    intro i
    have h := congrArg
      (· ≫ (kunnethRepresentativeLiftIso E eE (gr a) (Fgr a) (hgr a)
        (fun K ↦ K.as.obj.filtration.gradedPiece a) (hgro a)
        (kunnethConvolutionRepresentative hconv P Q)).hom ≫
          (DerivedCategory.Q.mapIso (kunnethRepresentativeGradedComparison.{u, w} P Q a)).inv)
      (hstar a i P Q)
    simp only [Category.assoc] at h
    exact h.trans (hp i)


end CochainComplex
