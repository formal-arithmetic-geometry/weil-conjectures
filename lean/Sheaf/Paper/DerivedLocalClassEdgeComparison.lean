/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso

/-!
# Derived local-class edges and site comparison

Source: Stacks Project, sites-cohomology.tex, Tags 0BKV and 0D6I, and the comparison
unit of sk-prop-sf-comparison (blueprint: lem-pur-derived-local-class-edge-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u vC vD uC uD wC wD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

namespace CategoryTheory

/-- The canonical cohomology edge of an exact-left-adjoint adjunction: transpose the
cohomology of its derived counit, using the exact-functor cohomology identification.
For sheafification this is the local-class presheaf map; for the constant sheaf
adjunction it is the global local-class edge. Source: Stacks 0BKV, cycle quotient
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedLocalClassMate
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasKInjectiveResolutions D] {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (V : DerivedCategory D) (r : ℤ) :
    (DerivedCategory.homologyFunctor C r).obj (R.rightDerivedFunctor.obj V) ⟶
      R.obj ((DerivedCategory.homologyFunctor D r).obj V) :=
  adj.homEquiv _ _
    ((L.mapDerivedCategoryHomologyFunctorIso r).hom.app (R.rightDerivedFunctor.obj V) ≫
      (DerivedCategory.homologyFunctor D r).map
        (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app V))

set_option backward.isDefEq.respectTransparency false in
private theorem derivedLocalClassMate_naturality
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasKInjectiveResolutions D] {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) {V V' : DerivedCategory D} (f : V ⟶ V') (r : ℤ) :
    (DerivedCategory.homologyFunctor C r).map (R.rightDerivedFunctor.map f) ≫
        derivedLocalClassMate adj V' r =
      derivedLocalClassMate adj V r ≫ R.map ((DerivedCategory.homologyFunctor D r).map f) := by
  unfold derivedLocalClassMate
  apply adj.homEquiv_naturality_left_square
  rw [← Category.assoc]
  erw [(L.mapDerivedCategoryHomologyFunctorIso r).hom.naturality]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp,
    dsimp% adj.mapDerivedCategoryRightDerivedAdjunction.counit.naturality f]
  simp only [Functor.map_comp, Category.assoc]

section ExactAdjunction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [L.PreservesHomology] [R.PreservesHomology]

private theorem shortComplex_homology_adjunct (adj : L ⊣ R)
    (S : ShortComplex C) (T : ShortComplex D)
    (ψ : S.map L ⟶ T) (τ : S ⟶ T.map R)
    (h₁ : τ.τ₁ = adj.homEquiv _ _ ψ.τ₁)
    (h₂ : τ.τ₂ = adj.homEquiv _ _ ψ.τ₂)
    (_h₃ : τ.τ₃ = adj.homEquiv _ _ ψ.τ₃) :
    adj.homEquiv _ _ ((S.mapHomologyIso L).inv ≫ ShortComplex.homologyMap ψ) =
      ShortComplex.homologyMap τ ≫ (T.mapHomologyIso R).hom := by
  let h := S.homologyData.left
  let k := T.homologyData.left
  let γ : ShortComplex.LeftHomologyMapData ψ (h.map L) k := default
  let δ : ShortComplex.LeftHomologyMapData τ h (k.map R) :=
    { φK := (adj.homEquiv _ _) γ.φK
      φH := (adj.homEquiv _ _) γ.φH
      commi := by
        change (adj.homEquiv _ _) γ.φK ≫ R.map k.i = h.i ≫ τ.τ₂
        rw [h₂, ← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
        exact congrArg (adj.homEquiv _ _) γ.commi
      commf' := by
        rw [ShortComplex.LeftHomologyData.map_f']
        change h.f' ≫ (adj.homEquiv _ _) γ.φK = τ.τ₁ ≫ R.map k.f'
        rw [h₁, ← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
        apply congrArg (adj.homEquiv _ _)
        simpa only [ShortComplex.LeftHomologyData.map_f'] using γ.commf'
      commπ := by
        change h.π ≫ (adj.homEquiv _ _) γ.φH =
          (adj.homEquiv _ _) γ.φK ≫ R.map k.π
        rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
        exact congrArg (adj.homEquiv _ _) γ.commπ }
  have heq : ShortComplex.homologyMap τ ≫ (T.mapHomologyIso R).hom =
      adj.homEquiv _ _ (L.map h.homologyIso.hom ≫ γ.φH ≫ k.homologyIso.inv) := by
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
      δ.homologyMap_eq, k.mapHomologyIso_eq R]
    simp only [δ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
  rw [heq]
  apply congrArg (adj.homEquiv _ _)
  rw [γ.homologyMap_eq, h.mapHomologyIso_eq L]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_assoc]

private theorem complex_homology_counit (adj : L ⊣ R) (K : CochainComplex D ℤ) (r : ℤ) :
    adj.homEquiv _ _
        ((L.mapHomologicalComplexHomologyIso (.up ℤ) r).inv.app
            ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
          HomologicalComplex.homologyMap ((adj.mapHomologicalComplex (.up ℤ)).counit.app K)
            r) =
      (R.mapHomologicalComplexHomologyIso (.up ℤ) r).hom.app K := by
  have h := shortComplex_homology_adjunct adj
    (((R.mapHomologicalComplex (.up ℤ)).obj K).sc r) (K.sc r)
    ((HomologicalComplex.shortComplexFunctor _ _ r).map
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app K)) (𝟙 _)
    (by simp [Adjunction.homEquiv_unit]) (by simp [Adjunction.homEquiv_unit])
    (by simp [Adjunction.homEquiv_unit])
  have hL : (L.mapHomologicalComplexHomologyIso (.up ℤ) r).app
      ((R.mapHomologicalComplex (.up ℤ)).obj K) =
      ((((R.mapHomologicalComplex (.up ℤ)).obj K).sc r).mapHomologyIso L) :=
    Iso.ext (Functor.mapHomologicalComplexHomologyIso_hom_app_eq _ _ _ _)
  change adj.homEquiv _ _
    (((L.mapHomologicalComplexHomologyIso (.up ℤ) r).app
      ((R.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫ _) = _
  erw [hL, Functor.mapHomologicalComplexHomologyIso_hom_app_eq]
  simpa only [ShortComplex.homologyMap_id, Category.id_comp,
    HomologicalComplex.homologyMap, HomologicalComplex.homologyFunctor,
    HomologicalComplex.homology, Functor.id_obj] using h

end ExactAdjunction

section ExactMate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private theorem derivedLocalClassMate_exact_Q (adj : L ⊣ R)
    (K : CochainComplex D ℤ) (r : ℤ) :
    (DerivedCategory.homologyFunctor C r).map
        (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (.up ℤ)).obj K)) ≫
        derivedLocalClassMate adj (DerivedCategory.Q.obj K) r =
      (DerivedCategory.homologyFunctorFactors C r).hom.app
          ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (R.mapHomologicalComplexHomologyIso (.up ℤ) r).hom.app K ≫
          R.map ((DerivedCategory.homologyFunctorFactors D r).inv.app K) := by
  unfold derivedLocalClassMate
  erw [← adj.homEquiv_naturality_left]
  rw [← Category.assoc]
  erw [(L.mapDerivedCategoryHomologyFunctorIso r).hom.naturality]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp]
  erw [(adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit]
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
  have hf : L.mapDerivedCategoryFactorsh.hom.app
      ((R.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient D (.up ℤ)).obj K)) =
      L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    erw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      Functor.comp_obj]
    erw [L.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
    simp only [Category.id_comp, Category.comp_id]
    erw [Category.comp_id]
    rfl
  erw [hf, Functor.map_comp]
  change adj.homEquiv _ _
    ((L.mapDerivedCategoryHomologyFunctorIso r).hom.app
      (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫ _) = _
  rw [Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id]
  simp only [Category.id_comp]
  have hn := (DerivedCategory.homologyFunctorFactors D r).inv.naturality
    ((adj.mapHomologicalComplex (.up ℤ)).counit.app K)
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  rw [adj.homEquiv_naturality_left]
  simp only [← Category.assoc]
  erw [adj.homEquiv_naturality_right, complex_homology_counit]
  simp only [Category.assoc, Functor.id_obj]

private theorem derivedLocalClassMate_exact (adj : L ⊣ R)
    (V : DerivedCategory D) (r : ℤ) :
    derivedLocalClassMate adj V r =
      (DerivedCategory.homologyFunctor C r).map
          (R.rightDerivedFunctorIsoMapDerivedCategory.hom.app V) ≫
        (R.mapDerivedCategoryHomologyFunctorIso r).inv.app V := by
  let δ : R.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor C r ⟶
      DerivedCategory.homologyFunctor D r ⋙ R :=
    { app := fun X ↦ derivedLocalClassMate adj X r
      naturality := fun _ _ f ↦ derivedLocalClassMate_naturality adj f r }
  let γ : R.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor C r ⟶
      DerivedCategory.homologyFunctor D r ⋙ R :=
    Functor.whiskerRight R.rightDerivedFunctorIsoMapDerivedCategory.hom
      (DerivedCategory.homologyFunctor C r) ≫
        (R.mapDerivedCategoryHomologyFunctorIso r).inv
  have h : δ = γ := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso D (.up ℤ))
    intro K
    apply (cancel_epi ((DerivedCategory.homologyFunctor C r).map
      (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (.up ℤ)).obj K)))).1
    change _ ≫ derivedLocalClassMate adj (DerivedCategory.Q.obj K) r = _
    rw [derivedLocalClassMate_exact_Q adj]
    dsimp only [γ, NatTrans.comp_app, Functor.whiskerRight_app]
    rw [← Functor.map_comp_assoc]
    have hf := NatTrans.congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((HomotopyCategory.quotient D (.up ℤ)).obj K)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [hf]
    apply (cancel_mono ((R.mapDerivedCategoryHomologyFunctorIso r).hom.app
      (DerivedCategory.Q.obj K))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [← R.map_comp_assoc, Iso.inv_hom_id_app,
      R.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
    have hR : R.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient D (.up ℤ)).obj K) =
        R.mapDerivedCategoryFactors.inv.app K := by
      have hi : R.mapDerivedCategoryFactorsh.app
          ((HomotopyCategory.quotient D (.up ℤ)).obj K) =
          R.mapDerivedCategoryFactors.app K := by
        apply Iso.ext
        change R.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient D (.up ℤ)).obj K) = _
        erw [Functor.mapDerivedCategoryFactorsh_hom_app]
        simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
          Functor.comp_obj]
        erw [R.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
        simp only [Category.id_comp, Category.comp_id]
        erw [Category.comp_id]
        rfl
      exact congrArg Iso.inv hi
    erw [hR, Category.comp_id]
  exact NatTrans.congr_app h V

end ExactMate

section Composition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private lemma mapHomologyIso_comp (S : ShortComplex C) :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq (S.homologyData.left.map F) G]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  change ((S.homologyData.left.map F).map G).homologyIso.hom ≫
    G.map (S.mapHomologyIso F).inv ≫ G.map (S.mapHomologyIso F).hom = _
  simp only [← G.map_comp, Iso.inv_hom_id, G.map_id]
  change ((S.homologyData.left.map F).map G).homologyIso.hom ≫ 𝟙 _ = _
  rw [Category.comp_id]
  change ((S.homologyData.left.map F).map G).homologyIso.hom =
    (S.homologyData.left.map (F ⋙ G)).homologyIso.hom
  let γ : ShortComplex.LeftHomologyMapData (𝟙 (S.map (F ⋙ G)))
      ((S.homologyData.left.map F).map G) (S.homologyData.left.map (F ⋙ G)) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp
      commf' := by simp
      commπ := by simp }
  have hγ := γ.homologyMap_comm
  simpa [γ] using hγ.symm

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private lemma complex_homology_comp (n : ℤ) (L : CochainComplex C ℤ) :
    (G.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
      G.map ((F.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L) =
    ((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L := by
  simp only [Functor.mapHomologicalComplexHomologyIso_hom_app_eq]
  convert mapHomologyIso_comp F G (L.sc n) using 1 <;> rfl

private lemma homology_comp (n : ℤ) (K : DerivedCategory C) :
    G.map ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (F.mapDerivedCategory.obj K) =
    ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom.app K ≫
      (DerivedCategory.homologyFunctor E n).map
        ((Functor.mapDerivedCategoryCompIso F G).hom.app K) := by
  have h : Functor.whiskerRight (F.mapDerivedCategoryHomologyFunctorIso n).hom G ≫
      Functor.whiskerLeft F.mapDerivedCategory
        (G.mapDerivedCategoryHomologyFunctorIso n).hom =
      ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F G).hom
          (DerivedCategory.homologyFunctor E n) := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro L
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [F.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality
      (F.mapDerivedCategoryFactors.inv.app L)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    simp only [hn]
    rw [G.mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
      (F ⋙ G).mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
    simp only [Category.assoc]
    simp only [← G.map_comp_assoc, Iso.inv_hom_id_app]
    simp only [G.map_comp]
    have hc := complex_homology_comp F G n L
    have hci : G.map ((F.mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app L) ≫
        (G.mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj L) =
        ((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app L := by
      apply (cancel_mono
        (((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app L)).1
      rw [← hc]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
        Iso.inv_hom_id_app]
      erw [G.map_id]
      rw [hc, Iso.inv_hom_id_app]
      rfl
    have hi : (F ⋙ G).mapDerivedCategoryFactors.inv.app L ≫
        (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj L) =
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app L) := by
      simp only [comp_obj, mapDerivedCategoryCompIso, Localization.liftNatIso,
        Iso.refl_hom, Iso.refl_inv, Localization.liftNatTrans_app, NatTrans.id_app,
        Iso.trans_inv, isoWhiskerRight_inv, Iso.symm_inv, isoWhiskerLeft_inv,
        Category.assoc, NatTrans.comp_app, whiskerRight_app, associator_hom_app,
        whiskerLeft_app, associator_inv_app, Category.comp_id, Category.id_comp]
      change _ ≫ (F ⋙ G).mapDerivedCategoryFactors.hom.app L ≫ _ = _
      rw [Iso.inv_hom_id_app_assoc]
      have hId : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
          (.up ℤ)).inv.app L = 𝟙 _ := rfl
      rw [hId]
      erw [DerivedCategory.Q.map_id]
      rw [Category.id_comp]
    have him := congrArg (DerivedCategory.homologyFunctor E n).map hi
    simp only [Functor.map_comp] at him
    rw [him]
    dsimp only [Functor.comp_map, Functor.comp_obj] at *
    erw [G.map_id]
    simp only [Category.comp_id, Category.assoc]
    congr 1
    rw [← Category.assoc, hci]
    rfl
  exact NatTrans.congr_app h K

end Composition

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedLocalClassMate_unit
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasKInjectiveResolutions D] {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (V : DerivedCategory C) (r : ℤ) :
    (DerivedCategory.homologyFunctor C r).map
        (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app V) ≫
        derivedLocalClassMate adj (L.mapDerivedCategory.obj V) r =
      adj.unit.app ((DerivedCategory.homologyFunctor C r).obj V) ≫
        R.map ((L.mapDerivedCategoryHomologyFunctorIso r).hom.app V) := by
  unfold derivedLocalClassMate
  erw [← adj.homEquiv_naturality_left]
  erw [← adj.homEquiv_unit]
  congr 1
  rw [← Category.assoc]
  erw [(L.mapDerivedCategoryHomologyFunctorIso r).hom.naturality]
  dsimp only [Functor.comp_map]
  erw [Category.assoc, ← Functor.map_comp,
    adj.mapDerivedCategoryRightDerivedAdjunction.left_triangle_components,
    Functor.map_id, Category.comp_id]
  rfl

section MateComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category.{vC} C] [Category.{vC} D] [Category.{vC} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesKInjectiveComplexes]
  {L₁ : D ⥤ C} {L₂ : E ⥤ D} {L : E ⥤ C} [L₁.Additive] [L₂.Additive] [L.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj₁ : L₁ ⊣ F) (adj₂ : L₂ ⊣ G) (adj : L ⊣ H)

omit [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  [F.Additive] [G.Additive] [H.Additive] [F.PreservesKInjectiveComplexes]
  [L₁.Additive] [L₂.Additive] [L.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
private theorem homEquiv_conjugate (e : F ⋙ G ≅ H) (eL : L ≅ L₂ ⋙ L₁)
    (he : e.hom = conjugateEquiv (adj₂.comp adj₁) adj eL.hom)
    {A : E} {B : C} (f : L₁.obj (L₂.obj A) ⟶ B) :
    (adj₂.comp adj₁).homEquiv A B f ≫ e.hom.app B =
      adj.homEquiv A B (eL.hom.app A ≫ f) := by
  simp only [Adjunction.homEquiv_unit]
  rw [Category.assoc, e.hom.naturality, ← Category.assoc]
  rw [he, unit_conjugateEquiv]
  simp only [Functor.map_comp, Category.assoc]

private theorem derivedLocalClassMate_comp (e : F ⋙ G ≅ H) (eL : L ≅ L₂ ⋙ L₁)
    (he : e.hom = conjugateEquiv (adj₂.comp adj₁) adj eL.hom)
    (V : DerivedCategory C) (r : ℤ) :
    (DerivedCategory.homologyFunctor E r).map
        ((Functor.rightDerivedFunctorCompIso' F G e).hom.app V) ≫
        derivedLocalClassMate adj V r =
      derivedLocalClassMate adj₂ (F.rightDerivedFunctor.obj V) r ≫
        G.map (derivedLocalClassMate adj₁ V r) ≫
          e.hom.app ((DerivedCategory.homologyFunctor C r).obj V) := by
  have hc := conjugateEquiv_counit
    (adj₂.mapDerivedCategoryRightDerivedAdjunction.comp
      adj₁.mapDerivedCategoryRightDerivedAdjunction)
    adj.mapDerivedCategoryRightDerivedAdjunction
    (Functor.mapDerivedCategoryNatIso eL ≪≫ Functor.mapDerivedCategoryCompIso _ _).hom V
  rw [← Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    adj₁ adj₂ adj e eL he] at hc
  unfold derivedLocalClassMate
  rw [← Category.assoc]
  erw [← adj₂.homEquiv_naturality_right]
  erw [← adj₁.homEquiv_naturality_left]
  have ht := homEquiv_conjugate adj₁ adj₂ adj e eL he
    (L₁.map ((L₂.mapDerivedCategoryHomologyFunctorIso r).hom.app
        (G.rightDerivedFunctor.obj (F.rightDerivedFunctor.obj V)) ≫
      (DerivedCategory.homologyFunctor D r).map
        (adj₂.mapDerivedCategoryRightDerivedAdjunction.counit.app
          (F.rightDerivedFunctor.obj V))) ≫
      (L₁.mapDerivedCategoryHomologyFunctorIso r).hom.app (F.rightDerivedFunctor.obj V) ≫
        (DerivedCategory.homologyFunctor C r).map
          (adj₁.mapDerivedCategoryRightDerivedAdjunction.counit.app V))
  rw [Adjunction.comp_homEquiv] at ht
  dsimp only [Equiv.trans_apply] at ht
  erw [ht]
  erw [← adj.homEquiv_naturality_left]
  apply (adj.homEquiv _ _).congr_arg
  rw [← Category.assoc]
  erw [(L.mapDerivedCategoryHomologyFunctorIso r).hom.naturality]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp, hc]
  simp only [Iso.trans_hom, NatTrans.comp_app, Adjunction.comp_counit_app,
    Functor.map_comp, Category.assoc]
  erw [← reassoc_of% (Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality
    eL r (G.rightDerivedFunctor.obj (F.rightDerivedFunctor.obj V))) ]
  erw [← reassoc_of% (homology_comp L₂ L₁ r
    (G.rightDerivedFunctor.obj (F.rightDerivedFunctor.obj V)))]
  erw [← (L₁.mapDerivedCategoryHomologyFunctorIso r).hom.naturality_assoc]
  rfl

private theorem derivedLocalClassMate_pullback (e : F ⋙ G ≅ H) (eL : L ≅ L₂ ⋙ L₁)
    (he : e.hom = conjugateEquiv (adj₂.comp adj₁) adj eL.hom)
    (V : DerivedCategory D) (r : ℤ) :
    (DerivedCategory.homologyFunctor E r).map
        (G.rightDerivedFunctor.map
            (adj₁.mapDerivedCategoryRightDerivedAdjunction.unit.app V) ≫
          (Functor.rightDerivedFunctorCompIso' F G e).hom.app
            (L₁.mapDerivedCategory.obj V)) ≫
        derivedLocalClassMate adj (L₁.mapDerivedCategory.obj V) r =
      derivedLocalClassMate adj₂ V r ≫
        G.map (adj₁.unit.app ((DerivedCategory.homologyFunctor D r).obj V)) ≫
          e.hom.app (L₁.obj ((DerivedCategory.homologyFunctor D r).obj V)) ≫
            H.map ((L₁.mapDerivedCategoryHomologyFunctorIso r).hom.app V) := by
  rw [Functor.map_comp, Category.assoc, derivedLocalClassMate_comp adj₁ adj₂ adj e eL he]
  rw [← Category.assoc, ← Category.assoc,
    dsimp% derivedLocalClassMate_naturality adj₂
      (adj₁.mapDerivedCategoryRightDerivedAdjunction.unit.app V) r]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, derivedLocalClassMate_unit adj₁, G.map_comp]
  simp only [Category.assoc]
  erw [e.hom.naturality]

end MateComposition

section PlusUnit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  [HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private lemma plus_comparison_unit (F : D ⥤ C) [F.Additive]
    (K : HomotopyCategory.Plus D) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
      F.rightDerivedFunctorUnit.app K.obj := by
  simpa only [Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.rightDerivedFunctorPlusCompatibility,
    Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.id_app,
    Iso.refl_hom, Category.id_comp] using
    (Functor.rightDerivedNatTrans_app
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
      F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
      (HomotopyCategory.Plus.quasiIso D) (𝟙 _) K)

private lemma derived_unit_comparison (adj : L ⊣ R)
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map (adj.derivedPlus.unit.app K) ≫
      R.rightDerivedFunctorPlusCompatibility.hom.app (L.mapDerivedCategoryPlus.obj K) =
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app K.obj := by
  let η : DerivedCategory.Plus.ι ⟶
      L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ R.rightDerivedFunctor :=
    Functor.whiskerRight adj.derivedPlus.unit DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus R.rightDerivedFunctorPlusCompatibility.hom
  let ε : DerivedCategory.Plus.ι ⟶
      L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ R.rightDerivedFunctor :=
    Functor.whiskerLeft DerivedCategory.Plus.ι
      adj.mapDerivedCategoryRightDerivedAdjunction.unit
  have he : η = ε := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)
    intro N
    dsimp only [η, ε, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app]
    apply (cancel_mono (R.rightDerivedFunctor.map
      (L.mapDerivedCategoryFactorsh.hom.app N.obj))).1
    have hn := R.rightDerivedFunctorPlusCompatibility.hom.naturality
      (L.mapDerivedCategoryPlusFactorsh.hom.app N)
    dsimp only [Functor.comp_map] at hn
    have hf : L.mapDerivedCategoryFactorsh.hom.app N.obj =
        DerivedCategory.Plus.ι.map (L.mapDerivedCategoryPlusFactorsh.hom.app N) :=
      (L.ι_map_mapDerivedCategoryPlusFactorsh_hom_app N).symm
    erw [hf]
    erw [Category.assoc, ← hn, ← Functor.map_comp_assoc,
      adj.derivedPlus_unit_app_fac, Functor.map_comp, Category.assoc, plus_comparison_unit]
    have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit N.obj
    change adj.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫ _ = _ at h
    erw [← hf, h]
    change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C).map
      (adj.mapHomotopyCategoryPlus.unit.app N)) ≫ _ = _
    rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
    rfl
  exact NatTrans.congr_app he K

end PlusUnit

end CategoryTheory

namespace CategoryTheory

/-- The standard localization for module-valued presheaves. Its larger morphism universe
is allowed: it does not identify the object and morphism universes of the site.
Source: Stacks 0BKV, its presheaf construction
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable instance localClassPresheavesHasDerivedCategory
    {C : Type (u + 1)} [Category.{u} C] (Λ : Type (u + 1)) [CommRing Λ] :
    HasDerivedCategory.{u + 2} (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :=
  HasDerivedCategory.standard _

section Site

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (Λ : Type (u + 1)) [CommRing Λ]

/-- Derived sections as a presheaf, by deriving the underlying-presheaf functor.
Evaluation is exact, so its degree-r cohomology at W is H^r(W,V).
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedLocalCohomologyPresheaf
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  (DerivedCategory.homologyFunctor (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) r).obj
    ((sheafToPresheaf J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V)

/-- The canonical sheafification-to-cohomology map, given by the derived counit.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedLocalClassSheafification
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    (presheafToSheaf J (ModuleCat.{u + 1} Λ)).obj
        (derivedLocalCohomologyPresheaf J Λ V r) ⟶
      (DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V :=
  ((presheafToSheaf J (ModuleCat.{u + 1} Λ)).mapDerivedCategoryHomologyFunctorIso r).hom.app
      ((sheafToPresheaf J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V) ≫
    (DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).map
      ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (sheafificationAdjunction J (ModuleCat.{u + 1} Λ))).counit.app V)

/-- The local-class presheaf morphism is the sheafification unit followed by the
canonical cohomology identification. Source: Stacks 0BKV
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedLocalClassPresheafMap
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    derivedLocalCohomologyPresheaf J Λ V r ⟶
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V).obj :=
  toSheafify J (derivedLocalCohomologyPresheaf J Λ V r) ≫
    (derivedLocalClassSheafification J Λ V r).hom

/-- Global local-class edge, the transpose of the derived constant-sheaf counit.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def derivedGlobalLocalClassEdge [HasGlobalSectionsFunctor J (ModuleCat.{u + 1} Λ)]
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).obj
        ((Sheaf.Γ J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V) ⟶
      (Sheaf.Γ J (ModuleCat.{u + 1} Λ)).obj
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V) :=
  derivedLocalClassMate (constantSheafΓAdj J (ModuleCat.{u + 1} Λ)) V r

end Site

end CategoryTheory

namespace CategoryTheory

/-- Canonical degree-r cohomology identification after a cochain shift by one.
Source: Stacks 0BKV, signed cochain shift
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassCohomologyShift
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    (V : DerivedCategory C) (r : ℤ) :
    (DerivedCategory.homologyFunctor D r).obj (F.obj (V⟦(1 : ℤ)⟧)) ≅
      (DerivedCategory.homologyFunctor D (r + 1)).obj (F.obj V) :=
  (DerivedCategory.homologyFunctor D r).mapIso ((F.commShiftIso (1 : ℤ)).app V) ≪≫
    ((DerivedCategory.homologyFunctor D 0).shiftIso 1 r (r + 1) (add_comm 1 r)).app
      (F.obj V)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedLocalClassMate_shift
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [HasKInjectiveResolutions D] {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (V : DerivedCategory D) (r : ℤ) :
    derivedLocalClassMate adj (V⟦(1 : ℤ)⟧) r ≫
        R.map (((DerivedCategory.homologyFunctor D 0).shiftIso
          1 r (r + 1) (add_comm 1 r)).hom.app V) =
      (localClassCohomologyShift R.rightDerivedFunctor V r).hom ≫
        derivedLocalClassMate adj V (r + 1) := by
  have := canonicalRightDerivedAdjunctionShift adj
  symm
  unfold derivedLocalClassMate
  apply adj.homEquiv_naturality_left_square
  simp only [localClassCohomologyShift, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (L.mapDerivedCategoryHomologyFunctorIso_hom_app_shiftIso 1 r (r + 1)
    (add_comm 1 r) (R.rightDerivedFunctor.obj V))]
  rw [← Category.assoc, ← Category.assoc]
  erw [(L.mapDerivedCategoryHomologyFunctorIso r).hom.naturality]
  dsimp only [Functor.comp_map]
  simp only [Category.assoc]
  erw [← (DerivedCategory.homologyFunctor D 0).shiftIso_hom_naturality
    1 r (r + 1) (add_comm 1 r)
    (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app V)]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rw [← Functor.commShiftIso_comp_hom_app,
    adj.mapDerivedCategoryRightDerivedAdjunction.commShiftIso_hom_app_counit_app_shift]
  rfl

/-- The same shift comparison on a bounded-below object, including the canonical
shift comparison for the full-subcategory inclusion into the ambient derived category.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassPlusCohomologyShift
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    (V : DerivedCategory.Plus C) (r : ℤ) :
    (DerivedCategory.homologyFunctor D r).obj (F.obj ((V⟦(1 : ℤ)⟧).obj)) ≅
      (DerivedCategory.homologyFunctor D (r + 1)).obj (F.obj V.obj) :=
  (DerivedCategory.homologyFunctor D r).mapIso
      (F.mapIso ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).app V)) ≪≫
    localClassCohomologyShift F V.obj r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localClassPlusCohomologyShift_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : DerivedCategory C ⥤ DerivedCategory D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] (V : DerivedCategory.Plus C) (r : ℤ) :
    (DerivedCategory.homologyFunctor D r).map (τ.app (V⟦(1 : ℤ)⟧).obj) ≫
        (localClassPlusCohomologyShift G V r).hom =
      (localClassPlusCohomologyShift F V r).hom ≫
        (DerivedCategory.homologyFunctor D (r + 1)).map (τ.app V.obj) := by
  simp only [localClassPlusCohomologyShift, localClassCohomologyShift, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc]
  erw [← (DerivedCategory.homologyFunctor D 0).shiftIso_hom_naturality
    1 r (r + 1) (add_comm 1 r) (τ.app V.obj)]
  simp only [DerivedCategory.shift_homologyFunctor, ← Functor.map_comp_assoc]
  apply congrArg (fun f ↦ (DerivedCategory.homologyFunctor D r).map f ≫
    ((DerivedCategory.homologyFunctor D 0).shiftIso 1 r (r + 1)
      (add_comm 1 r)).hom.app (G.obj V.obj))
  rw [← Category.assoc, ← τ.naturality, Category.assoc]
  erw [← NatTrans.shift_app_comm]
  rfl

section SiteLaws

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (Λ : Type (u + 1)) [CommRing Λ] [HasTerminal C]

omit [HasTerminal C] in
private theorem derivedLocalClassSheafification_isIso
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    IsIso (derivedLocalClassSheafification J Λ V r) := by
  let adj := sheafificationAdjunction J (ModuleCat.{u + 1} Λ)
  have := adj.preservesKInjectiveComplexes
  have h := adj.fullyFaithfulROfIsIsoCounit
  have := h.full
  have := h.faithful
  have := adj.mapDerivedCategoryRightDerivedAdjunction.counit_isIso_of_R_fully_faithful
  unfold derivedLocalClassSheafification
  infer_instance

/-- At any site object, the presheaf value is canonically the cohomology of derived
literal evaluation; exact evaluation commutes with right derivation and cohomology.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassObjectCohomologyIso (W : C)
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    (derivedLocalCohomologyPresheaf J Λ V r).obj (op W) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).obj
        ((sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
          (evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W)).rightDerivedFunctor.obj V) :=
  (Functor.mapDerivedCategoryHomologyFunctorIso
      ((evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W)) r).app
        ((sheafToPresheaf J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).mapIso
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (sheafToPresheaf J (ModuleCat.{u + 1} Λ))
        ((evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W))).symm.app V)

/-- Derived global sections evaluated at a terminal site object, using the canonical
right-derived comparison for composition with exact evaluation.
Source: Stacks 0BKV, final-object evaluation
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassTerminalCohomologyIso (W : C) (hW : IsTerminal W)
    (V : DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).obj
        ((Sheaf.Γ J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V) ≅
      (derivedLocalCohomologyPresheaf J Λ V r).obj (op W) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).mapIso
      ((Functor.rightDerivedFunctorNatIso
          (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{u + 1} Λ) hW ≪≫
            sheafSectionsNatIsoEvaluation J (ModuleCat.{u + 1} Λ))).app V ≪≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
          (sheafToPresheaf J (ModuleCat.{u + 1} Λ))
          ((evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W))).app V) ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso
      ((evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W)) r).symm.app
        ((sheafToPresheaf J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj V)

/-- The four local-class assertions on one site: sheafification, evaluation at the final
object, naturality for all derived morphisms, and compatibility with the cochain shift.
Only cohomological boundedness below is imposed on the objects.
Source: Stacks 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
def DerivedLocalClassEdgeLaws : Prop :=
  (∀ (V : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ),
    IsIso (derivedLocalClassSheafification J Λ V.obj r)) ∧
  (∀ (V : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ)
      (W : C) (hW : IsTerminal W),
    derivedGlobalLocalClassEdge J Λ V.obj r ≫
        (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{u + 1} Λ) hW).hom.app
          ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V.obj) =
      (localClassTerminalCohomologyIso J Λ W hW V.obj r).hom ≫
        (derivedLocalClassPresheafMap J Λ V.obj r).app (op W)) ∧
  (∀ (V V' : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} Λ)))
      (f : V ⟶ V') (r : ℤ),
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).map
        ((Sheaf.Γ J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.map f.hom) ≫
          derivedGlobalLocalClassEdge J Λ V'.obj r =
      derivedGlobalLocalClassEdge J Λ V.obj r ≫
        (Sheaf.Γ J (ModuleCat.{u + 1} Λ)).map
          ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).map f.hom)) ∧
  (∀ (V : DerivedCategory.Plus (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ),
    derivedGlobalLocalClassEdge J Λ (V.obj⟦(1 : ℤ)⟧) r ≫
        (Sheaf.Γ J (ModuleCat.{u + 1} Λ)).map
          ((Functor.shiftIso
            (DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) 0)
            1 r (r + 1) (add_comm 1 r)).hom.app V.obj) =
      (localClassCohomologyShift
        (Sheaf.Γ J (ModuleCat.{u + 1} Λ)).rightDerivedFunctor V.obj r).hom ≫
          derivedGlobalLocalClassEdge J Λ V.obj (r + 1))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedLocalClass_terminal (V : DerivedCategory
    (Sheaf J (ModuleCat.{u + 1} Λ))) (r : ℤ) (W : C) (hW : IsTerminal W) :
    derivedGlobalLocalClassEdge J Λ V r ≫
        (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{u + 1} Λ) hW).hom.app
          ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V) =
      (localClassTerminalCohomologyIso J Λ W hW V r).hom ≫
        (derivedLocalClassPresheafMap J Λ V r).app (op W) := by
  let : HasKInjectiveResolutions (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) := by
    let : IsGrothendieckAbelian.{u + 1} (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :=
      IsGrothendieckAbelian.of_equivalence (sheafBotEquivalence (ModuleCat.{u + 1} Λ))
    infer_instance
  let a := sheafificationAdjunction J (ModuleCat.{u + 1} Λ)
  let b := constantPresheafAdj (ModuleCat.{u + 1} Λ) hW
  let c := constantSheafΓAdj J (ModuleCat.{u + 1} Λ)
  let F := sheafToPresheaf J (ModuleCat.{u + 1} Λ)
  let G := (evaluation Cᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op W)
  let e : F ⋙ G ≅ Sheaf.Γ J (ModuleCat.{u + 1} Λ) :=
    (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{u + 1} Λ) hW ≪≫
      sheafSectionsNatIsoEvaluation J (ModuleCat.{u + 1} Λ)).symm
  let eL := (conjugateIsoEquiv (b.comp a) c).symm e
  have he : e.hom = conjugateEquiv (b.comp a) c eL.hom :=
    (congrArg Iso.hom ((conjugateIsoEquiv (b.comp a) c).apply_symm_apply e)).symm
  have := a.preservesKInjectiveComplexes
  have h := derivedLocalClassMate_comp a b c e eL he V r
  let k := Functor.rightDerivedFunctorCompIso' F G e
  have hk : (localClassTerminalCohomologyIso J Λ W hW V r).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).map (k.inv.app V) ≫
        derivedLocalClassMate b (F.rightDerivedFunctor.obj V) r := by
    rw [derivedLocalClassMate_exact]
    simp only [localClassTerminalCohomologyIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.symm_hom]
    rw [← Functor.map_comp_assoc]
    congr 1
    have hcomp : Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived F G =
        Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G := by
      apply Iso.ext
      apply (F ⋙ G).rightDerivedFunctor.rightDerived_ext
        (F ⋙ G).rightDerivedFunctorUnit
        (HomotopyCategory.quasiIso (Sheaf J (ModuleCat.{u + 1} Λ)) (.up ℤ))
      ext K
      have hf := NatTrans.congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
        ((F.mapHomotopyCategory (.up ℤ)).obj K)
      dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
      have ht := congrArg (fun f ↦
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K) ≫
          f ≫ G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K)) hf
      simpa [Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived,
        Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
        Functor.rightDerivedFunctorCompUnit,
        Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, Category.assoc] using ht
    erw [← hcomp]
    simp only [k, Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso,
      Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived,
      Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    simp only [e, Iso.symm_inv, Iso.trans_hom, Category.assoc]
    rfl
  rw [hk]
  apply (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) r).map
    (k.hom.app V))).1
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp]
  have hh := congrArg (fun f ↦ f ≫ e.inv.app
    ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{u + 1} Λ)) r).obj V)) h
  simp only [Category.assoc, Iso.hom_inv_id_app] at hh
  erw [Category.comp_id] at hh
  have heinv : e.inv =
      (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{u + 1} Λ) hW).hom := by
    simp only [e, Iso.symm_inv, Iso.trans_hom, sheafSectionsNatIsoEvaluation,
      Iso.refl_hom, Category.comp_id]
  rw [heinv] at hh
  have hm : derivedLocalClassMate a V r = derivedLocalClassPresheafMap J Λ V r := rfl
  rw [hm] at hh
  have heval : G.map (derivedLocalClassPresheafMap J Λ V r) =
      (derivedLocalClassPresheafMap J Λ V r).app (op W) := rfl
  rw [heval] at hh
  simpa only [derivedGlobalLocalClassEdge, F, c, k, Category.assoc] using hh

private theorem localClassEdgeLaws : DerivedLocalClassEdgeLaws J Λ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V r
    exact derivedLocalClassSheafification_isIso J Λ V.obj r
  · intro V r W hW
    exact derivedLocalClass_terminal J Λ V.obj r W hW
  · intro V V' f r
    exact derivedLocalClassMate_naturality
      (constantSheafΓAdj J (ModuleCat.{u + 1} Λ)) f.hom r
  · intro V r
    exact derivedLocalClassMate_shift (constantSheafΓAdj J (ModuleCat.{u + 1} Λ)) V.obj r

end SiteLaws

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The cohomology comparison specified by the derived comparison unit, with the
canonical Leray identification; this is exactly the map of sk-prop-sf-comparison.
Source: Stacks 099V and 099W (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassSiteComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (V : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (r : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).obj
        ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} P.Coefficient) T).obj V.obj) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} P.Coefficient) T).obj
          ((Functor.mapDerivedCategory
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)).obj V.obj)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).map
    ((boundedBelowComparisonGlobalSections T P.Coefficient).app V)

/-- Pullback of a section of the cohomology sheaf: apply the ordinary comparison unit,
identify final-object sections, and use the canonical exact-inverse-image cohomology iso.
Source: Stacks 07A6 and 0BKV (blueprint: lem-pur-derived-local-class-edge-comparison). -/
noncomputable def localClassSectionPullback (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u})
    (V : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (r : ℤ) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).obj
        ((DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) r).obj V.obj) ⟶
      (Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)).obj
        ((DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) r).obj
            ((Functor.mapDerivedCategory
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)).obj V.obj)) :=
  (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).map
      ((comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).unit.app
        ((DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) r).obj V.obj)) ≫
    (comparisonLowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} P.Coefficient) T).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj
        ((DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) r).obj V.obj)) ≫
    (Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)).map
      ((Functor.mapDerivedCategoryHomologyFunctorIso
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T) r).hom.app V.obj)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def localClassComparisonTransformation
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).rightDerivedFunctor ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory ⋙
        (Sheaf.Γ (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} P.Coefficient)).rightDerivedFunctor :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T)).unit
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (comparisonLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} P.Coefficient) T).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem boundedBelowComparisonGlobalSections_app_eq
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (V : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    (boundedBelowComparisonGlobalSections T P.Coefficient).app V =
      (localClassComparisonTransformation P T).app V.obj := by
  simp only [boundedBelowComparisonGlobalSections, localClassComparisonTransformation,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  dsimp only [Functor.comp_map]
  erw [← Functor.map_comp_assoc, CategoryTheory.derived_unit_comparison]
  rfl

private theorem localClassComparisonTransformation_commShift
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    NatTrans.CommShift (localClassComparisonTransformation P T) ℤ := by
  have := canonicalRightDerivedAdjunctionShift
    (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T)
  have := canonicalRightDerivedAdjunctionShift
    (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
  have := canonicalRightDerivedAdjunctionShift
    (constantSheafΓAdj (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
  have := Adjunction.commShift_rightDerivedFunctorUnit
    (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T)
  have := Adjunction.commShift_rightDerivedFunctorUnit
    (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
  have := Adjunction.commShift_rightDerivedFunctorUnit
    (constantSheafΓAdj (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))
  have := (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T).preservesKInjectiveComplexes
  have := Functor.commShift_rightDerivedFunctorCompIso'_hom
    (comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) T)
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (comparisonLowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} P.Coefficient) T)
  unfold localClassComparisonTransformation comparisonLowerStarCompRightDerivedGlobalSectionsIso
  infer_instance

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- The comparison square, its derived-morphism naturality, and its shift compatibility.
All arrows are the previously constructed canonical arrows, rather than arbitrary maps.
Source: Stacks 0BKV and the unit of sk-prop-sf-comparison
(blueprint: lem-pur-derived-local-class-edge-comparison). -/
def DerivedLocalClassSiteLaws (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) : Prop :=
  (∀ (V : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (r : ℤ),
    IsIso (localClassSiteComparison P T V r) ∧
    localClassSiteComparison P T V r ≫
        derivedGlobalLocalClassEdge (Scheme.ProEt.topology T) P.Coefficient
          ((Functor.mapDerivedCategory
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)).obj V.obj) r =
      derivedGlobalLocalClassEdge T.smallEtaleTopology P.Coefficient V.obj r ≫
        localClassSectionPullback P T V r) ∧
  (∀ (V V' : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (f : V ⟶ V') (r : ℤ),
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).map
        ((Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} P.Coefficient) T).map f.hom) ≫
          localClassSiteComparison P T V' r =
      localClassSiteComparison P T V r ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).map
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} P.Coefficient) T).map
            ((Functor.mapDerivedCategory
              (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T)).map f.hom))) ∧
  (∀ (V : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (r : ℤ),
    localClassSiteComparison P T (V⟦(1 : ℤ)⟧) r ≫
        (localClassPlusCohomologyShift
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory ⋙
            (Sheaf.Γ (Scheme.ProEt.topology T)
              (ModuleCat.{u + 1} P.Coefficient)).rightDerivedFunctor) V r).hom =
      (localClassPlusCohomologyShift
        (Sheaf.Γ T.smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient)).rightDerivedFunctor V r).hom ≫
          localClassSiteComparison P T V (r + 1))

/-- On either small site, sheafified derived section cohomology is the cohomology
sheaf. The canonical local-class edges are natural for arbitrary derived maps, commute
with cochain shifts, and commute with the specified etale/pro-etale comparison.
Source: Stacks, sites-cohomology.tex, 0BKV and 0D6I; sk-prop-sf-comparison
(blueprint: lem-pur-derived-local-class-edge-comparison).

Proof:
1. The ringed-site category is Grothendieck abelian
(lem-pur-ringed-site-grothendieck-abelian), hence has enough injectives
(lem-sp-grothendieck-enough-injectives). Represent each D+ object by a bounded-below
complex I of injective sheaves (lem-weil-pbc-dplus-injective-representative).
The slice-section model (lem-pe-injective-complex-slice-section-model) identifies
H^r(W,V) with the cohomology of I(W), with literal restriction maps.
2. Objectwise cohomology and exact sheafification
(lem-weil-pbc-site-module-presheaf-sheafification-exact) identify the sheafified
presheaf with H^r(I). The derived sheafification counit gives this identification:
its transpose is the sheafification unit followed by the cycle quotient. At the
terminal object the constant-sheaf adjunction gives the same cycle quotient.
3. Represent every derived map between injective models by a chain map, uniquely
up to homotopy (lem-weil-pbc-kinjective-hom-derived). The edge sends a cycle to its
cohomology-sheaf class; both naturality composites send z to the class of f(z).
A homotopy changes the value by a boundary, proving independence of the model.
4. For I[1], the differential is -d_I (def-weil-abstract-derived-category).
Its kernels and images are unchanged, so the same quotient gives the shift law.
5. Exact inverse image commutes with cohomology and cycle quotients
(lem-weil-pbc-exact-functor-complex-cohomology). Resolve its image LI by an
injective complex J and a quasi-isomorphism a:LI -> J.
6. The bounded-below derived adjunction unit is represented by eta_I followed by
R(a) (lem-trf-bounded-below-derived-adjunction and
lem-weil-pbc-right-derived-plus-injective). Direct image preserves injectives
(lem-sp-right-adjoint-preserves-injectives), and sections of RJ at the final
object are sections of J. The canonical Leray isomorphism
(lem-weil-pbc-derived-sections-pushforward) therefore identifies the specified
comparison with z -> a(Lz). It is invertible by sk-prop-sf-comparison.
7. Both sides of the site square send a cycle z to the quotient class of a(Lz),
using the exact-inverse-image cohomology identification from step 5.
8. For derived maps, chain representatives of the two comparison composites are
homotopic, so their cohomology maps agree. For shifts use I[1], J[1], a[1];
additivity of inverse image and the kernel/image calculation of step 4 give
the comparison shift equation. The edge naturality and shift equations then
make the site square compatible with these operations. No concentration or
constructibility was used. -/
theorem derivedLocalClassEdgeComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) :
    DerivedLocalClassEdgeLaws T.smallEtaleTopology P.Coefficient ∧
      DerivedLocalClassEdgeLaws (Scheme.ProEt.topology T) P.Coefficient ∧
      DerivedLocalClassSiteLaws P T := by
  refine ⟨localClassEdgeLaws _ _, localClassEdgeLaws _ _, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro V r
    have := (boundedBelowComparison T P.Coefficient).2.2
    refine ⟨?_, ?_⟩
    · unfold localClassSiteComparison
      infer_instance
    · let a := comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) T
      let b := constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
      let c := constantSheafΓAdj (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} P.Coefficient)
      let e := comparisonLowerStarCompGlobalSectionsIso
        (ModuleCat.{u + 1} P.Coefficient) T
      let eL := (conjugateIsoEquiv (b.comp a) c).symm e
      have he : e.hom = conjugateEquiv (b.comp a) c eL.hom := by
        exact (congrArg Iso.hom ((conjugateIsoEquiv (b.comp a) c).apply_symm_apply e)).symm
      have := a.preservesKInjectiveComplexes
      simpa only [localClassSiteComparison, boundedBelowComparisonGlobalSections_app_eq,
        localClassComparisonTransformation, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
        Category.id_comp, Category.comp_id, derivedGlobalLocalClassEdge,
        localClassSectionPullback, comparisonLowerStarCompRightDerivedGlobalSectionsIso,
        Category.assoc] using
        CategoryTheory.derivedLocalClassMate_pullback a b c e eL he V.obj r
  · intro V V' f r
    unfold localClassSiteComparison
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) r).map
      ((boundedBelowComparisonGlobalSections T P.Coefficient).naturality f)
  · intro V r
    have := localClassComparisonTransformation_commShift P T
    simpa only [localClassSiteComparison, boundedBelowComparisonGlobalSections_app_eq] using
      CategoryTheory.localClassPlusCohomologyShift_naturality
        (localClassComparisonTransformation P T) V r

end AlgebraicGeometry.ProEtale
