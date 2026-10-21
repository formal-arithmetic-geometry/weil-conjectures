/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Algebra.Homology.FilteredTensorLocalizationSetup
import Sheaf.Algebra.Homology.FilteredTensorGradedDescent
import Sheaf.Algebra.Homology.FilteredQuasiIsoTwoOutOfThree

/-! # Descent of the convolution tensor comparisons

Source: Stacks Project, More on Algebra, Tag 0H7Y, and Derived Categories, Tags 05S2--05S3.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor

namespace CochainComplex

variable {R : Type u} [CommRing R]

private def kunnethIso₂OfComponents
    {C D A : Type*} [Category* C] [Category* D] [Category* A]
    {F G : C ⥤ D ⥤ A} (e : ∀ P Q, (F.obj P).obj Q ≅ (G.obj P).obj Q)
    (he : ∀ {P P' : C} {Q Q' : D} (f : P ⟶ P') (g : Q ⟶ Q'),
      (e P Q).hom ≫ ((G.map f).app Q ≫ (G.obj P').map g) =
        ((F.map f).app Q ≫ (F.obj P').map g) ≫ (e P' Q').hom) : F ≅ G :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents (e P) (fun g ↦ by
    simpa using (he (𝟙 P) g).symm)) (fun f ↦ NatTrans.ext (funext (fun Q ↦ by
      simpa using (he f (𝟙 Q)).symm)))

private theorem comparisonIsoPair_natural
    {C D A : Type*} [Category* C] [Category* D] [Category* A]
    {F G : C ⥤ D ⥤ A} (e : F ≅ G) {P P' : C} {Q Q' : D}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    ((e.app P).app Q).hom ≫ ((G.map f).app Q ≫ (G.obj P').map g) =
      ((F.map f).app Q ≫ (F.obj P').map g) ≫ ((e.app P').app Q').hom := by
  have hf := NatTrans.congr_app (e.hom.naturality f) Q
  have hg := (e.hom.app P').naturality g
  dsimp only [NatTrans.comp_app] at hf
  simp only [Category.assoc]
  erw [← reassoc_of% hf, ← hg]
  rfl

private abbrev comparisonHomObj (P : GoodFiniteFilteredModuleHomotopy R) :
    KunnethFilteredComplex R := ⟨P.obj.as.obj, P.property⟩

private theorem comparisonGoodMap_surjective
    {P P' : GoodFiniteFilteredModuleHomotopy R} (f : P ⟶ P') :
    ∃ f' : comparisonHomObj P ⟶ comparisonHomObj P',
      kunnethGoodRepresentativeMap f' = f := by
  let q := CategoryTheory.Quotient.functor (finiteFilteredModuleHomotopyRel R)
  refine ⟨ObjectProperty.homMk (q.preimage f.hom).hom, ?_⟩
  apply ObjectProperty.hom_ext
  exact q.map_preimage f.hom

private noncomputable def comparisonForget :
    FiniteFilteredModuleComplex R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj K := K.obj.obj
  map f := f.hom.hom

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

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

private theorem kunneth_transport_bifunctor_comparison
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
    (d : F ⋙ (whiskeringRight _ _ _).obj (E.functor ⋙ omega) ≅
      ((whiskeringLeft₂ _).obj
        ((goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ⋙ omega) |>.obj
        ((goodFiniteFilteredModuleQuasiIso R).Q ⋙ E.functor ⋙ omega)).obj
          (curriedTensor (DerivedCategory (ModuleCat.{u} R)))) :
    ∃ η : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
      omega.obj ((star.obj U).obj V) ≅ omega.obj U ⊗ omega.obj V,
      (∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
          (f : U ⟶ U') (g : V ⟶ V'),
        (η U V).hom ≫ (omega.map f ⊗ₘ omega.map g) =
          omega.map ((star.map f).app V ≫ (star.obj U').map g) ≫ (η U' V').hom) ∧
      ∀ P Q : GoodFiniteFilteredModuleHomotopy R,
        let qP := (goodFiniteFilteredModuleQuasiIso R).Q.obj P
        let qQ := (goodFiniteFilteredModuleQuasiIso R).Q.obj Q
        (η (E.functor.obj qP) (E.functor.obj qQ)).hom =
          omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).hom ≫
          (E.functor ⋙ omega).map
            ((B.map (E.unitIso.symm.app qP).hom).app
                (E.inverse.obj (E.functor.obj qQ)) ≫
              (B.obj qP).map (E.unitIso.symm.app qQ).hom) ≫
          (E.functor ⋙ omega).map
            (((Localization.Lifting₂.iso (goodFiniteFilteredModuleQuasiIso R).Q
              (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
              (goodFiniteFilteredModuleQuasiIso R) F B).app P).app Q).hom ≫
          ((d.app P).app Q).hom := by
  classical
  let W := E.functor ⋙ omega
  let O := (goodFiniteFilteredModuleQuasiIso R).Q ⋙ W
  let A := F ⋙ (whiskeringRight _ _ _).obj W
  let T := ((whiskeringLeft₂ _).obj O |>.obj O).obj
    (curriedTensor (DerivedCategory (ModuleCat.{u} R)))
  let := hB
  let : (goodFiniteFilteredModuleQuasiIso R).ContainsIdentities :=
    { id_mem := fun P ↦ finiteFilteredModuleQuasiIso_id R P.obj }
  let BL := B ⋙ (whiskeringRight _ _ _).obj W
  let TL := ((whiskeringLeft₂ _).obj W |>.obj W).obj
    (curriedTensor (DerivedCategory (ModuleCat.{u} R)))
  let : Localization.Lifting₂ (goodFiniteFilteredModuleQuasiIso R).Q
      (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
      (goodFiniteFilteredModuleQuasiIso R) A BL := inferInstance
  let : Localization.Lifting₂ (goodFiniteFilteredModuleQuasiIso R).Q
      (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
      (goodFiniteFilteredModuleQuasiIso R) T TL := ⟨Iso.refl _⟩
  let dL := Localization.lift₂NatIso (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
    (goodFiniteFilteredModuleQuasiIso R) A T BL TL d
  have hdL {U U' V V' : (goodFiniteFilteredModuleQuasiIso R).Localization}
      (f : U ⟶ U') (g : V ⟶ V') :
      ((dL.app U).app V).hom ≫ (W.map f ⊗ₘ W.map g) =
        W.map ((B.map f).app V ≫ (B.obj U').map g) ≫ ((dL.app U').app V').hom := by
    have hn := comparisonIsoPair_natural dL f g
    change ((dL.app U).app V).hom ≫ (W.map f ▷ W.obj V ≫ W.obj U' ◁ W.map g) =
      (W.map ((B.map f).app V) ≫ W.map ((B.obj U').map g)) ≫ _ at hn
    rw [← tensorHom_def, ← Functor.map_comp] at hn
    exact hn
  let η (U V : (finiteFilteredModuleQuasiIso R).Localization) :
      omega.obj ((star.obj U).obj V) ≅ omega.obj U ⊗ omega.obj V :=
    omega.mapIso (τ U V) ≪≫ (dL.app (E.inverse.obj U)).app (E.inverse.obj V) ≪≫
      tensorIso (omega.mapIso (E.counitIso.app U)) (omega.mapIso (E.counitIso.app V))
  refine ⟨η, ?_, ?_⟩
  · intro U U' V V' f g
    have hcf := congrArg omega.map (E.counitIso.hom.naturality f)
    have hcg := congrArg omega.map (E.counitIso.hom.naturality g)
    dsimp only [Functor.comp_map, Functor.id_map] at hcf hcg
    simp only [Functor.map_comp] at hcf hcg
    have hct :
        (omega.map (E.counitIso.app U).hom ⊗ₘ omega.map (E.counitIso.app V).hom) ≫
          (omega.map f ⊗ₘ omega.map g) =
        (W.map (E.inverse.map f) ⊗ₘ W.map (E.inverse.map g)) ≫
          (omega.map (E.counitIso.app U').hom ⊗ₘ omega.map (E.counitIso.app V').hom) := by
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
      erw [← hcf, ← hcg]
      rfl
    have hτm := congrArg omega.map (hτ U U' V V' f g)
    rw [omega.map_comp, omega.map_comp] at hτm
    dsimp only [η, Iso.trans_hom, Functor.mapIso_hom]
    simp only [tensorIso_hom, Functor.mapIso_hom, Category.assoc]
    rw [hct]
    rw [reassoc_of% hdL (E.inverse.map f) (E.inverse.map g)]
    erw [reassoc_of% hτm]
    simp only [omega.map_comp, Category.assoc]
  · intro P Q
    let qP := (goodFiniteFilteredModuleQuasiIso R).Q.obj P
    let qQ := (goodFiniteFilteredModuleQuasiIso R).Q.obj Q
    let uP := E.unitIso.symm.app qP
    let uQ := E.unitIso.symm.app qQ
    have hdrep : ((dL.app qP).app qQ).hom =
        W.map (((Localization.Lifting₂.iso (goodFiniteFilteredModuleQuasiIso R).Q
          (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
          (goodFiniteFilteredModuleQuasiIso R) F B).app
            P).app Q).hom ≫
          ((d.app P).app Q).hom := by
      change ((Localization.lift₂NatTrans (goodFiniteFilteredModuleQuasiIso R).Q
        (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
        (goodFiniteFilteredModuleQuasiIso R) A T BL TL d.hom).app qP).app qQ = _
      erw [Localization.lift₂NatTrans_app_app]
      change _ ≫ _ ≫ (𝟙 _) = _
      rw [Category.comp_id]
      rfl
    have hcp : (E.counitIso.app (E.functor.obj qP)).hom = E.functor.map uP.hom :=
      E.counit_app_functor qP
    have hcq : (E.counitIso.app (E.functor.obj qQ)).hom = E.functor.map uQ.hom :=
      E.counit_app_functor qQ
    have htc : (omega.map (E.counitIso.app (E.functor.obj qP)).hom ⊗ₘ
        omega.map (E.counitIso.app (E.functor.obj qQ)).hom) =
        (W.map uP.hom ⊗ₘ W.map uQ.hom) := by
      exact congrArg₂ (fun f g ↦ omega.map f ⊗ₘ omega.map g) hcp hcq
    have hηraw : (η (E.functor.obj qP) (E.functor.obj qQ)).hom =
        omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).hom ≫
          ((dL.app (E.inverse.obj (E.functor.obj qP))).app
            (E.inverse.obj (E.functor.obj qQ))).hom ≫ (W.map uP.hom ⊗ₘ W.map uQ.hom) := by
      exact congrArg (fun t ↦ omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).hom ≫
        ((dL.app (E.inverse.obj (E.functor.obj qP))).app
          (E.inverse.obj (E.functor.obj qQ))).hom ≫ t) htc
    have hηloc : (η (E.functor.obj qP) (E.functor.obj qQ)).hom =
        omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).hom ≫
          W.map ((B.map uP.hom).app (E.inverse.obj (E.functor.obj qQ)) ≫
            (B.obj qP).map uQ.hom) ≫ ((dL.app qP).app qQ).hom := by
      exact hηraw.trans (congrArg
        (omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).hom ≫ ·) (hdL uP.hom uQ.hom))
    exact hηloc.trans (congrArg
      (fun z ↦ omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).hom ≫
        W.map ((B.map uP.hom).app (E.inverse.obj (E.functor.obj qQ)) ≫
          (B.obj qP).map uQ.hom) ≫ z) hdrep)

private theorem kunneth_underlying_comparison_descent
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
    (omega :
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      DerivedCategory (ModuleCat.{u} R))
    (Fω : FiniteFilteredModuleHomotopy R ⥤
    DerivedCategory (ModuleCat.{u} R))
    (hω : Localization.Lifting
    (finiteFilteredModuleQuasiIso R).Q
    (finiteFilteredModuleQuasiIso R)
    Fω omega)
    (hωobj : ∀ K : FiniteFilteredModuleHomotopy R,
    Fω.obj K =
      HomologicalComplexUpToQuasiIso.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
          K.as.obj.obj))
    (hωmap : ∀ (K L : FiniteFilteredModuleHomotopy R)
      (f : K.as ⟶ L.as),
    Fω.map ((finiteFilteredModuleHomotopyQuotient R).map f) =
      eqToHom (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
        HomologicalComplexUpToQuasiIso.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
            f.hom.hom) ≫
        eqToHom
          (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm
          ) :
    (∃ η : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
      omega.obj ((star.obj U).obj V) ≅
        (omega.obj U) ⊗ (omega.obj V),
      (∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
          (f : U ⟶ U') (g : V ⟶ V'),
        (η U V).hom ≫ (omega.map f ⊗ₘ omega.map g) =
          omega.map ((star.map f).app V ≫
            (star.obj U').map g) ≫ (η U' V').hom) ∧
      ∃ (cη : ∀ P Q : KunnethFilteredComplex R,
        DerivedCategory.Q.obj P.obj.obj ⊗
            DerivedCategory.Q.obj Q.obj.obj ≅
          DerivedCategory.Q.obj (P.obj.obj ⊗ Q.obj.obj)),
        (∀ P Q : KunnethFilteredComplex R,
          (cη P Q).hom = Functor.LaxMonoidal.μ
            DerivedCategory.Q P.obj.obj Q.obj.obj) ∧
        (∀ P Q : KunnethFilteredComplex R,
          (η (kunnethLocalizedRepresentative E P)
            (kunnethLocalizedRepresentative E Q)).hom ≫
            ((kunnethRepresentativeLiftIso E eE omega Fω hω
              (fun K ↦ K.as.obj.obj) hωobj P).hom ⊗ₘ
            (kunnethRepresentativeLiftIso E eE omega Fω hω
              (fun K ↦ K.as.obj.obj) hωobj Q).hom) =
          omega.map
            (kunnethStarRepresentativeIso E F B hB hconv hrep
              star τ P Q).hom ≫
            (kunnethRepresentativeLiftIso E eE omega Fω hω
              (fun K ↦ K.as.obj.obj) hωobj
              (kunnethConvolutionRepresentative hconv P Q)).hom ≫
            (cη P Q).inv)) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ∀ P Q : KunnethFilteredComplex R,
      DerivedCategory.Q.obj P.obj.obj ⊗ DerivedCategory.Q.obj Q.obj.obj ≅
        DerivedCategory.Q.obj (P.obj.obj ⊗ Q.obj.obj),
      ∀ P Q, (c P Q).hom = Functor.LaxMonoidal.μ DerivedCategory.Q P.obj.obj Q.obj.obj := by
    obtain ⟨_, _, _, c, _, _, _, _, _, _, _, _, hc, _⟩ :=
      filteredTensor_graded_comparison (R := R)
    exact ⟨c, hc⟩
  let W := E.functor ⋙ omega
  let O := (goodFiniteFilteredModuleQuasiIso R).Q ⋙ W
  let A := F ⋙ (whiskeringRight _ _ _).obj W
  let T := ((whiskeringLeft₂ _).obj O |>.obj O).obj
    (curriedTensor (DerivedCategory (ModuleCat.{u} R)))
  let α (P : KunnethFilteredComplex R) :=
    kunnethRepresentativeLiftIso E eE omega Fω hω (fun K ↦ K.as.obj.obj) hωobj P
  let β (P Q : GoodFiniteFilteredModuleHomotopy R) :=
    W.mapIso (eqToIso (hrep (comparisonHomObj P) (comparisonHomObj Q))) ≪≫
      α (kunnethConvolutionRepresentative hconv (comparisonHomObj P) (comparisonHomObj Q))
  let δ (P Q : GoodFiniteFilteredModuleHomotopy R) :
      (A.obj P).obj Q ≅ (T.obj P).obj Q :=
    β P Q ≪≫ (c (comparisonHomObj P) (comparisonHomObj Q)).symm ≪≫
      tensorIso (α (comparisonHomObj P)).symm (α (comparisonHomObj Q)).symm
  have hα {P P' : KunnethFilteredComplex R} (f : P ⟶ P') :
      O.map (kunnethGoodRepresentativeMap f) ≫ (α P').hom =
        (α P).hom ≫ DerivedCategory.Q.map f.hom.hom := by
    exact kunneth_representative_lift_natural E eE omega Fω hω
      comparisonForget hωobj hωmap P P' f
  have hδ {P P' Q Q' : GoodFiniteFilteredModuleHomotopy R}
      (f : P ⟶ P') (g : Q ⟶ Q') :
      (δ P Q).hom ≫ ((T.map f).app Q ≫ (T.obj P').map g) =
        ((A.map f).app Q ≫ (A.obj P').map g) ≫ (δ P' Q').hom := by
    obtain ⟨f, rfl⟩ := comparisonGoodMap_surjective f
    obtain ⟨g, rfl⟩ := comparisonGoodMap_surjective g
    have hμ : (c (comparisonHomObj P) (comparisonHomObj Q)).inv ≫
        (DerivedCategory.Q.map f.hom.hom ⊗ₘ DerivedCategory.Q.map g.hom.hom) =
        DerivedCategory.Q.map (m _ _ _ _ f g).hom ≫
          (c (comparisonHomObj P') (comparisonHomObj Q')).inv := by
      apply (cancel_epi (c (comparisonHomObj P) (comparisonHomObj Q)).hom).1
      apply (cancel_mono (c (comparisonHomObj P') (comparisonHomObj Q')).hom).1
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
        Category.comp_id]
      rw [hc, hc, hm]
      exact Functor.LaxMonoidal.μ_natural _ _ _
    have hβ : W.map ((F.map (kunnethGoodRepresentativeMap f)).app Q ≫
        (F.obj P').map (kunnethGoodRepresentativeMap g)) ≫ (β P' Q').hom =
        (β P Q).hom ≫ DerivedCategory.Q.map (m _ _ _ _ f g).hom := by
      dsimp only [β, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
      have he := hFmap (comparisonHomObj P) (comparisonHomObj P')
        (comparisonHomObj Q) (comparisonHomObj Q') f g
      erw [he]
      simp only [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      erw [hα (kunnethConvolutionRepresentativeMap hconv (m _ _ _ _ f g))]
      rfl
    change (δ P Q).hom ≫ (O.map (kunnethGoodRepresentativeMap f) ▷ O.obj Q) ≫
      (O.obj P' ◁ O.map (kunnethGoodRepresentativeMap g)) =
        (W.map ((F.map (kunnethGoodRepresentativeMap f)).app Q) ≫
          W.map ((F.obj P').map (kunnethGoodRepresentativeMap g))) ≫ (δ P' Q').hom
    erw [← tensorHom_def (O.map (kunnethGoodRepresentativeMap f))
      (O.map (kunnethGoodRepresentativeMap g)), ← Functor.map_comp]
    apply (cancel_mono ((α (comparisonHomObj P')).hom ⊗ₘ
      (α (comparisonHomObj Q')).hom)).1
    dsimp only [δ, Iso.trans_hom, Iso.symm_hom]
    simp only [tensorIso_hom, Iso.symm_hom]
    simp only [Category.assoc, tensorHom_comp_tensorHom,
      hα, Iso.inv_hom_id_assoc, Iso.inv_hom_id, id_tensorHom_id, Category.comp_id]
    rw [hμ]
    have hh := congrArg (· ≫ (c (comparisonHomObj P') (comparisonHomObj Q')).inv) hβ
    simp only [Category.assoc] at hh
    exact hh.symm
  let d : A ≅ T := kunnethIso₂OfComponents δ (fun f g ↦ hδ f g)
  obtain ⟨η, hη, hηrep⟩ := kunneth_transport_bifunctor_comparison
    E F B hB star τ hτ omega d
  refine ⟨η, hη, c, hc, ?_⟩
  intro P Q
  let qP := (goodFiniteFilteredModuleQuasiIso R).Q.obj (kunnethGoodRepresentative P)
  let qQ := (goodFiniteFilteredModuleQuasiIso R).Q.obj (kunnethGoodRepresentative Q)
  let uP := E.unitIso.symm.app qP
  let uQ := E.unitIso.symm.app qQ
  let t := omega.map (τ (E.functor.obj qP) (E.functor.obj qQ)).hom
  let b := W.map ((B.map uP.hom).app (E.inverse.obj (E.functor.obj qQ)) ≫
    (B.obj qP).map uQ.hom)
  let z := W.map (((Localization.Lifting₂.iso (goodFiniteFilteredModuleQuasiIso R).Q
    (goodFiniteFilteredModuleQuasiIso R).Q (goodFiniteFilteredModuleQuasiIso R)
    (goodFiniteFilteredModuleQuasiIso R) F B).app
      (kunnethGoodRepresentative P)).app (kunnethGoodRepresentative Q)).hom
  let r := W.map (eqToHom (hrep P Q))
  let a := (α (kunnethConvolutionRepresentative hconv P Q)).hom
  let v := (α P).hom ⊗ₘ (α Q).hom
  have hδnorm : (δ (kunnethGoodRepresentative P) (kunnethGoodRepresentative Q)).hom ≫
      v = r ≫ a ≫ (c P Q).inv := by
    dsimp only [δ, β, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
    simp only [tensorIso_hom, Iso.symm_hom, Category.assoc]
    change r ≫ a ≫ (c P Q).inv ≫ ((α P).inv ⊗ₘ (α Q).inv) ≫
      ((α P).hom ⊗ₘ (α Q).hom) = _
    simp only [tensorHom_comp_tensorHom, Iso.inv_hom_id,
      id_tensorHom_id, Category.comp_id]
  have hstar : omega.map (kunnethStarRepresentativeIso E F B hB hconv hrep
      star τ P Q).hom = t ≫ b ≫ z ≫ r := by
    dsimp only [t, b, z, r, kunnethStarRepresentativeIso]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, eqToIso.hom,
      W, Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl
  change (η (E.functor.obj qP) (E.functor.obj qQ)).hom ≫ v = _
  calc
    _ = (t ≫ b ≫ z ≫ (δ (kunnethGoodRepresentative P)
        (kunnethGoodRepresentative Q)).hom) ≫ v :=
      congrArg (· ≫ v) (hηrep (kunnethGoodRepresentative P) (kunnethGoodRepresentative Q))
    _ = t ≫ b ≫ z ≫ r ≫ a ≫ (c P Q).inv := by
      simpa only [Category.assoc] using congrArg (t ≫ b ≫ z ≫ ·) hδnorm
    _ = _ := by
      simpa only [Category.assoc] using
        (congrArg (· ≫ a ≫ (c P Q).inv) hstar).symm

/-- The underlying and graded representative comparisons descend through both
localizations and transport along the replacement equivalence.
Source: Stacks Project, More on Algebra, convolution comparison before Tag 0H7W
and Tag 0H7Y; Derived Categories, Tags 05S2 and 05S3.
(blueprint: lem-kun-filtered-tensor-comparison-descent).

Proof. On good representatives the underlying comparison is the inverse of the
lax monoidal comparison of the ordinary derived quotient. Goodness makes that map
an isomorphism, by the identity K-flat resolution. Naturality of the lax monoidal
comparison and hm identify the map of a pair with the tensor of its two underlying
maps. The given homotopy-quotient functor and its map formula make these squares
natural on the good homotopy category. Localize this natural isomorphism using
Localization.lift₂NatIso. Its component formula is the fixed Lifting₂ composite.
Transport through E.inverse in both variables and E.functor, then use eE, the
single-variable lifting comparisons and τ. Naturality of the equivalence unit
simplifies the representative component to exactly the displayed pin.

For the graded comparison use the canonical e in filteredTensor_graded_comparison.
Its derived coproduct legs are the lax monoidal comparison followed by the localized
complex coprojections. Finite filtrations make all but finitely many graded tensor
summands zero. The universal property of this coproduct identifies it with the
biproduct on any finite support. On a common support, its canonical map is the
biproduct of the graded tensor maps. Enlarging support inserts only zero summands,
so the comparison commutes with the specified inclusion of biproducts. Localize
this natural comparison in both variables as above. Natural squares for a denominator
also give natural squares for its inverse, by multiplying by its two invertible
images. Hence the comparisons are natural for all localized maps. Their values on
good representatives are unchanged, giving the final normalization equation.
The empty support is valid when every tensor summand is zero. No cochain-degree
bound, global common support, or functorial resolution is used. -/
theorem filteredTensor_localized_comparisons
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
    (omega :
    (finiteFilteredModuleQuasiIso R).Localization ⥤
      DerivedCategory (ModuleCat.{u} R))
    (Fω : FiniteFilteredModuleHomotopy R ⥤
    DerivedCategory (ModuleCat.{u} R))
    (hω : Localization.Lifting
    (finiteFilteredModuleQuasiIso R).Q
    (finiteFilteredModuleQuasiIso R)
    Fω omega)
    (hωobj : ∀ K : FiniteFilteredModuleHomotopy R,
    Fω.obj K =
      HomologicalComplexUpToQuasiIso.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
          K.as.obj.obj))
    (hωmap : ∀ (K L : FiniteFilteredModuleHomotopy R)
      (f : K.as ⟶ L.as),
    Fω.map ((finiteFilteredModuleHomotopyQuotient R).map f) =
      eqToHom (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj K.as)) ≫
        HomologicalComplexUpToQuasiIso.Qh.map
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
            f.hom.hom) ≫
        eqToHom
          (hωobj ((finiteFilteredModuleHomotopyQuotient R).obj L.as)).symm
          )
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
    (∃ η : ∀ U V : (finiteFilteredModuleQuasiIso R).Localization,
      omega.obj ((star.obj U).obj V) ≅
        (omega.obj U) ⊗ (omega.obj V),
      (∀ (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
          (f : U ⟶ U') (g : V ⟶ V'),
        (η U V).hom ≫ (omega.map f ⊗ₘ omega.map g) =
          omega.map ((star.map f).app V ≫
            (star.obj U').map g) ≫ (η U' V').hom) ∧
      ∃ (cη : ∀ P Q : KunnethFilteredComplex R,
        DerivedCategory.Q.obj P.obj.obj ⊗
            DerivedCategory.Q.obj Q.obj.obj ≅
          DerivedCategory.Q.obj (P.obj.obj ⊗ Q.obj.obj)),
        (∀ P Q : KunnethFilteredComplex R,
          (cη P Q).hom = Functor.LaxMonoidal.μ
            DerivedCategory.Q P.obj.obj Q.obj.obj) ∧
        (∀ P Q : KunnethFilteredComplex R,
          (η (kunnethLocalizedRepresentative E P)
            (kunnethLocalizedRepresentative E Q)).hom ≫
            ((kunnethRepresentativeLiftIso E eE omega Fω hω
              (fun K ↦ K.as.obj.obj) hωobj P).hom ⊗ₘ
            (kunnethRepresentativeLiftIso E eE omega Fω hω
              (fun K ↦ K.as.obj.obj) hωobj Q).hom) =
          omega.map
            (kunnethStarRepresentativeIso E F B hB hconv hrep
              star τ P Q).hom ≫
            (kunnethRepresentativeLiftIso E eE omega Fω hω
              (fun K ↦ K.as.obj.obj) hωobj
              (kunnethConvolutionRepresentative hconv P Q)).hom ≫
            (cη P Q).inv)) ∧
    ∃ (e : ∀ (a : ℤ)
        (U V : (finiteFilteredModuleQuasiIso R).Localization)
        (s : Finset ℤ),
        (∀ i : ℤ, i ∉ s →
          IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))) →
        ((gr a).obj ((star.obj U).obj V) ≅
          (⨁ fun i : ↥s =>
            ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V)))),
      (∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization),
        ∃ s : Finset ℤ,
          (∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))) ∧
      (∀ (a : ℤ)
          (U U' V V' : (finiteFilteredModuleQuasiIso R).Localization)
          (f : U ⟶ U') (g : V ⟶ V') (s : Finset ℤ)
          (hs : ∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))
          (hs' : ∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj U') ⊗ ((gr (a - i)).obj V'))),
        (e a U V s hs).hom ≫ biproduct.map (fun i : ↥s =>
          (gr i.1).map f ⊗ₘ (gr (a - i.1)).map g) =
          (gr a).map ((star.map f).app V ≫
            (star.obj U').map g) ≫ (e a U' V' s hs').hom)
      ∧ (∀ (a : ℤ) (U V : (finiteFilteredModuleQuasiIso R).Localization)
          (s t : Finset ℤ) (hst : s ⊆ t)
          (hs : ∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V)))
          (ht : ∀ i : ℤ, i ∉ t →
            IsZero (((gr i).obj U) ⊗ ((gr (a - i)).obj V))),
        ∃ (ι :
            (⨁ fun i : ↥s =>
              ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V)) ⟶
            (⨁ fun i : ↥t =>
              ((gr i.1).obj U) ⊗ ((gr (a - i.1)).obj V))),
          (∀ i : ↥s,
            biproduct.ι (fun j : ↥s =>
              ((gr j.1).obj U) ⊗ ((gr (a - j.1)).obj V)) i ≫ ι =
            biproduct.ι (fun j : ↥t =>
              ((gr j.1).obj U) ⊗ ((gr (a - j.1)).obj V))
              ⟨i.1, hst i.2⟩) ∧
          (e a U V s hs).hom ≫ ι =
            (e a U V t ht).hom)
      ∧ (∀ (P Q : KunnethFilteredComplex R) (a : ℤ)
          (s : Finset ℤ)
          (hs : ∀ i : ℤ, i ∉ s →
            IsZero (((gr i).obj (kunnethLocalizedRepresentative E P)) ⊗
              ((gr (a - i)).obj (kunnethLocalizedRepresentative E Q)))),
        ∃ (cgr : ∀ i : ℤ,
          kunnethDerivedGraded P.obj Q.obj a i ≅
            DerivedCategory.Q.obj
              (kunnethTensorGraded P.obj Q.obj a i)),
        (∀ i : ℤ, (cgr i).hom =
          Functor.LaxMonoidal.μ DerivedCategory.Q
            (P.obj.filtration.gradedPiece i)
            (Q.obj.filtration.gradedPiece (a - i))) ∧
        (e a (kunnethLocalizedRepresentative E P)
            (kunnethLocalizedRepresentative E Q) s hs).hom ≫
          biproduct.desc (fun i : ↥s ↦
            ((kunnethRepresentativeLiftIso E eE (gr i.1) (Fgr i.1)
              (hgr i.1) (fun K ↦ K.as.obj.filtration.gradedPiece i.1)
              (hgro i.1) P).hom ⊗ₘ
            (kunnethRepresentativeLiftIso E eE (gr (a - i.1))
              (Fgr (a - i.1)) (hgr (a - i.1))
              (fun K ↦ K.as.obj.filtration.gradedPiece (a - i.1))
              (hgro (a - i.1)) Q).hom) ≫
            (cgr i.1).hom ≫ DerivedCategory.Q.map
              (Sigma.ι (kunnethTensorGraded P.obj Q.obj a) i.1)) =
          (gr a).map
            (kunnethStarRepresentativeIso E F B hB hconv hrep
              star τ P Q).hom ≫
          (kunnethRepresentativeLiftIso E eE (gr a) (Fgr a) (hgr a)
            (fun K ↦ K.as.obj.filtration.gradedPiece a) (hgro a)
            (kunnethConvolutionRepresentative hconv P Q)).hom ≫
          (DerivedCategory.Q.mapIso
            (kunnethRepresentativeGradedComparison P Q a)).inv) := by
  exact ⟨kunneth_underlying_comparison_descent E eE F B hB hconv hrep m hm hFmap
    star τ hτ omega Fω hω hωobj hωmap,
    filteredTensor_localized_graded_comparison E eE F B hB hconv hrep m hm hFmap
      star τ hτ gr Fgr hgr hgro hgrmap⟩

end CochainComplex
