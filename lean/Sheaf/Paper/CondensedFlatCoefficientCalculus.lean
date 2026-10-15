/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module
public import Sheaf.Paper.CondensedCoefficientComparisons
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-! # Exact condensed coefficient changes and their derived tensor calculus

Source: archived master ModuleObject/Colimit/Compatibility.lean, A0.2 and Flat;
ModuleObject/Colimit/TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).

All modules below are the master internal module objects. The constructible categories
are `PadicSubfieldConstructible` and `PadicAlgClConstructible`, with no completeness
condition. The adjunctions are on the ambient unbounded derived categories.
-/

@[expose] public section

universe u wC wD wE vC vD vE uC uD uE

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

-- Keep canonical resolution comparisons opaque to implicit instance matching.
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

section CoherenceTools

set_option maxRecDepth 2048

namespace CategoryTheory
section
variable {C D : Type*} [Category C] [Category D]
  {F F' : C ⥤ D} {G G' : D ⥤ C}
private lemma uniq_eq_conjugate (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) =
      (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]
end
end CategoryTheory

namespace CategoryTheory
section Scalar
variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S U : C} [MonObj R] [MonObj S] [MonObj U]
  [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ U) [IsMonHom ψ]
  (χ : R ⟶ U) [IsMonHom χ] (h : φ ≫ ψ = χ)
private noncomputable abbrev scalarComp :=
  (Mod.extendScalarsComp φ ψ).symm ≪≫ Mod.extendScalarsIsoOfEq h

private lemma scalarComp_eq :
    (Mod.extendScalarsComp φ ψ).symm ≪≫ Mod.extendScalarsIsoOfEq h =
      Adjunction.leftAdjointCompIso (Mod.extendRestrictAdjunction φ)
        (Mod.extendRestrictAdjunction ψ) (Mod.extendRestrictAdjunction χ)
        ((Mod.comapComp φ ψ).symm ≪≫ Mod.comapCongr h) := by
  rw [Mod.extendScalarsComp, Mod.extendScalarsIsoOfEq, uniq_eq_conjugate,
    uniq_eq_conjugate]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    conjugateIsoEquiv_symm_apply_hom, conjugateIsoEquiv_symm_apply_inv,
    Adjunction.leftAdjointCompIso, Iso.trans_inv]
  exact congr_app (conjugateEquiv_symm_comp
    (Mod.extendRestrictAdjunction χ) (Mod.extendRestrictAdjunction (φ ≫ ψ))
    ((Mod.extendRestrictAdjunction φ).comp (Mod.extendRestrictAdjunction ψ))
    (Mod.comapCongr h).inv (Mod.comapComp φ ψ).hom) X
end Scalar
end CategoryTheory

namespace CategoryTheory
section ScalarCoherence
variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S U V : C} [MonObj R] [MonObj S] [MonObj U] [MonObj V]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj U]
  (f : R ⟶ S) [IsMonHom f] (g : S ⟶ U) [IsMonHom g] (j : U ⟶ V) [IsMonHom j]
  (fg : R ⟶ U) [IsMonHom fg] (gj : S ⟶ V) [IsMonHom gj]
  (fgj : R ⟶ V) [IsMonHom fgj]
  (hfg : f ≫ g = fg) (hgj : g ≫ j = gj) (hfgj : f ≫ gj = fgj) (hfgj' : fg ≫ j = fgj)
private lemma scalarComp_assoc :
    Functor.isoWhiskerRight (scalarComp f g fg hfg) (Mod.extendScalars j) ≪≫
        scalarComp fg j fgj hfgj' =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (Mod.extendScalars f) (scalarComp g j gj hgj) ≪≫
          scalarComp f gj fgj hfgj := by
  simp only [scalarComp, scalarComp_eq]
  have he : Functor.isoWhiskerLeft (Mod.comap j)
      ((Mod.comapComp f g).symm ≪≫ Mod.comapCongr hfg) ≪≫
        ((Mod.comapComp fg j).symm ≪≫ Mod.comapCongr hfgj') =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((Mod.comapComp g j).symm ≪≫ Mod.comapCongr hgj)
          (Mod.comap f) ≪≫
        ((Mod.comapComp f gj).symm ≪≫ Mod.comapCongr hfgj) := by
    ext M
    simp only [Functor.comp_obj, Functor.isoWhiskerLeft_trans, Iso.trans_assoc, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Mod.comp_hom', Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom,
      Functor.isoWhiskerRight_trans, Functor.isoWhiskerRight_hom,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp, Mod.comap_map_hom]
    change (𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X) =
      (𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X)
    simp
  rw [Adjunction.leftAdjointCompIso_assoc
    (Mod.extendRestrictAdjunction f) (Mod.extendRestrictAdjunction g)
    (Mod.extendRestrictAdjunction j) (Mod.extendRestrictAdjunction fg)
    (Mod.extendRestrictAdjunction gj) (Mod.extendRestrictAdjunction fgj) _ _ _ _ he]
  simp
end ScalarCoherence
end CategoryTheory

namespace CategoryTheory
section ScalarUnit
variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
private noncomputable abbrev scalarUnit (a : R ⟶ R) [IsMonHom a] (ha : a = 𝟙 R) :=
  Mod.extendScalarsIsoOfEq ha ≪≫ Mod.extendScalarsId

private lemma scalarUnit_eq (a : R ⟶ R) [IsMonHom a] (ha : a = 𝟙 R) :
    scalarUnit a ha = Adjunction.leftAdjointIdIso (Mod.extendRestrictAdjunction a)
      (Mod.comapCongr ha ≪≫ Mod.comapId R) := by
  unfold scalarUnit Mod.extendScalarsIsoOfEq Mod.extendScalarsId
  rw [uniq_eq_conjugate, uniq_eq_conjugate]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Iso.trans_hom, NatTrans.comp_app, conjugateIsoEquiv_symm_apply_hom,
    Adjunction.leftAdjointIdIso, Iso.symm_hom, Iso.trans_inv]
  exact congr_app (conjugateEquiv_symm_comp Adjunction.id
    (Mod.extendRestrictAdjunction (𝟙 R)) (Mod.extendRestrictAdjunction a)
    (Mod.comapId R).inv (Mod.comapCongr ha).inv) X

omit [IsCommMonObj S] in
private lemma scalarComp_id_comp (a : R ⟶ R) [IsMonHom a] (ha : a = 𝟙 R)
    (f : R ⟶ S) [IsMonHom f] (h : a ≫ f = f) :
    scalarComp a f f h =
      Functor.isoWhiskerRight (scalarUnit a ha) (Mod.extendScalars f) ≪≫
        Functor.leftUnitor (Mod.extendScalars f) := by
  simp only [scalarComp, scalarComp_eq, scalarUnit_eq]
  apply Adjunction.leftAdjointCompIso_id_comp
  ext M
  simp only [Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom',
    Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom, Functor.isoWhiskerLeft_trans,
    Iso.trans_assoc, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.id_obj,
    Functor.rightUnitor_hom_app, Category.comp_id, Mod.comapId_hom_app_hom]
  change (𝟙 M.X ≫ 𝟙 M.X) = (𝟙 M.X ≫ 𝟙 M.X)
  simp

private lemma scalarComp_comp_id (a : S ⟶ S) [IsMonHom a] (ha : a = 𝟙 S)
    (f : R ⟶ S) [IsMonHom f] (h : f ≫ a = f) :
    scalarComp f a f h =
      Functor.isoWhiskerLeft (Mod.extendScalars f) (scalarUnit a ha) ≪≫
        Functor.rightUnitor (Mod.extendScalars f) := by
  simp only [scalarComp, scalarComp_eq, scalarUnit_eq]
  apply Adjunction.leftAdjointCompIso_comp_id
  ext M
  simp
end ScalarUnit
end CategoryTheory

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section DerivedComposition
variable {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
  [Abelian C] [Abelian D] [Abelian E] [Abelian V]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory V]
  {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ V} {FG : C ⥤ E} {GH : D ⥤ V} {FGH : C ⥤ V}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [GH.Additive] [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
  [FGH.Additive] [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]

private noncomputable abbrev derivedComp (e : F ⋙ G ≅ FG) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ FG.mapDerivedCategory :=
  (mapDerivedCategoryCompIso F G).symm ≪≫ mapDerivedCategoryNatIso e

private lemma derivedComp_assoc (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ FGH)
    (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ FGH)
    (h : isoWhiskerRight a H ≪≫ b = isoWhiskerLeft F c ≪≫ d) :
    isoWhiskerRight (derivedComp a) H.mapDerivedCategory ≪≫ derivedComp b =
      isoWhiskerLeft F.mapDerivedCategory (derivedComp c) ≪≫ derivedComp d := by
  have hm : (mapDerivedCategoryNatIso (isoWhiskerRight a H)).hom ≫
      (mapDerivedCategoryNatIso b).hom =
      (mapDerivedCategoryNatIso (isoWhiskerLeft F c)).hom ≫
        (mapDerivedCategoryNatIso d).hom := by
    rw [← mapDerivedCategoryNatIso_trans, ← mapDerivedCategoryNatIso_trans, h]
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have ha := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight a H) K
  have hc := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft F c) K
  have hassoc := congr_app (mapDerivedCategoryCompIso_assoc F G H) K
  have hm' := congr_app hm K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at ha hc hassoc hm'
  simp only [derivedComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← cancel_epi (H.mapDerivedCategory.map ((mapDerivedCategoryCompIso F G).hom.app K))]
  simp only [← map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [← cancel_epi ((mapDerivedCategoryCompIso (F ⋙ G) H).hom.app K)]
  rw [← reassoc_of% ha, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hassoc]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hc, Iso.hom_inv_id_app_assoc]
  exact hm'
end DerivedComposition
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section Transport
variable {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
  {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : E ⥤ V}
  {FG FG' : C ⥤ E} {GH GH' : D ⥤ V} {FGH FGH' : C ⥤ V}
private lemma associator_trans_eq (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ V)
    {K : C ⥤ V} (e : F ⋙ G ⋙ H ≅ K) : associator F G H ≪≫ e = e := by
  ext X
  simp

private noncomputable abbrev transportComp (a : F ≅ F') (b : G ≅ G') (c : FG ≅ FG')
    (e : F' ⋙ G' ≅ FG') : F ⋙ G ≅ FG :=
  isoWhiskerLeft F b ≪≫ isoWhiskerRight a G' ≪≫ e ≪≫ c.symm

private lemma transportComp_assoc (aF : F ≅ F') (aG : G ≅ G') (aH : H ≅ H')
    (aFG : FG ≅ FG') (aGH : GH ≅ GH') (aFGH : FGH ≅ FGH')
    (a : F' ⋙ G' ≅ FG') (b : FG' ⋙ H' ≅ FGH')
    (c : G' ⋙ H' ≅ GH') (d : F' ⋙ GH' ≅ FGH')
    (h : isoWhiskerRight a H' ≪≫ b = isoWhiskerLeft F' c ≪≫ d) :
    isoWhiskerRight (transportComp aF aG aFG a) H ≪≫ transportComp aFG aH aFGH b =
      isoWhiskerLeft F (transportComp aG aH aGH c) ≪≫ transportComp aF aGH aFGH d := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have hh := congr_app (congr_arg Iso.hom h) X
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app] at hh
  simp only [transportComp, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (aH.hom.naturality (aFG.hom.app X))]
  rw [← H.map_comp_assoc (aFG.inv.app X) (aFG.hom.app X),
    Iso.inv_hom_id_app, H.map_id, Category.id_comp]
  rw [reassoc_of% (aH.hom.naturality (a.hom.app X))]
  rw [reassoc_of% (aH.hom.naturality (G'.map (aF.hom.app X)))]
  rw [reassoc_of% (aH.hom.naturality (aG.hom.app (F.obj X)))]
  rw [reassoc_of% hh, reassoc_of% (c.hom.naturality (aF.hom.app X))]
  simp only [Iso.inv_hom_id_app_assoc]

end Transport
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section DerivedUnit
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {A : C ⥤ C} {B : D ⥤ D} {F : C ⥤ D}
  [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private noncomputable abbrev derivedUnit (e : A ≅ 𝟭 C) : A.mapDerivedCategory ≅ 𝟭 _ :=
  mapDerivedCategoryNatIso e ≪≫ mapDerivedCategoryIdIso C

private lemma derivedComp_id_comp (e : A ≅ 𝟭 C) (a : A ⋙ F ≅ F)
    (h : a = isoWhiskerRight e F ≪≫ leftUnitor F) :
    derivedComp a = isoWhiskerRight (derivedUnit e) F.mapDerivedCategory ≪≫
      leftUnitor F.mapDerivedCategory := by
  rw [h]
  have he : (mapDerivedCategoryNatIso (leftUnitor F)).hom = 𝟙 _ :=
    mapDerivedCategoryNatIso_refl
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hn := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight e F) K
  have hu := congr_app (mapDerivedCategoryCompIso_id_comp F) K
  simp only [NatTrans.comp_app, whiskerRight_app, NatTrans.id_app] at hn hu
  simp only [derivedComp, derivedUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, map_comp, leftUnitor_hom_app,
    mapDerivedCategoryNatIso_trans, he, Category.comp_id, Category.assoc]
  rw [← cancel_epi ((mapDerivedCategoryCompIso A F).hom.app K),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% hn, reassoc_of% hu, Category.comp_id]
  exact (Category.comp_id _).symm

private lemma derivedComp_comp_id (e : B ≅ 𝟭 D) (a : F ⋙ B ≅ F)
    (h : a = isoWhiskerLeft F e ≪≫ rightUnitor F) :
    derivedComp a = isoWhiskerLeft F.mapDerivedCategory (derivedUnit e) ≪≫
      rightUnitor F.mapDerivedCategory := by
  rw [h]
  have he : (mapDerivedCategoryNatIso (rightUnitor F)).hom = 𝟙 _ :=
    mapDerivedCategoryNatIso_refl
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hn := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft F e) K
  have hu := congr_app (mapDerivedCategoryCompIso_comp_id F) K
  simp only [NatTrans.comp_app, whiskerLeft_app, NatTrans.id_app] at hn hu
  simp only [derivedComp, derivedUnit, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, rightUnitor_hom_app,
    mapDerivedCategoryNatIso_trans, he, Category.comp_id, Category.assoc]
  rw [← cancel_epi ((mapDerivedCategoryCompIso F B).hom.app K),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% hn, reassoc_of% hu, Category.comp_id]
  exact (Category.comp_id _).symm
end DerivedUnit
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section TransportUnit
variable {C D : Type*} [Category C] [Category D]
  {A A' : C ⥤ C} {B B' : D ⥤ D} {F F' : C ⥤ D}

private lemma transportComp_id_comp (aA : A ≅ A') (aF : F ≅ F')
    (e : A' ≅ 𝟭 C) (c : A' ⋙ F' ≅ F')
    (h : c = isoWhiskerRight e F' ≪≫ leftUnitor F') :
    transportComp aA aF aF c =
      isoWhiskerRight (aA ≪≫ e) F ≪≫ leftUnitor F := by
  rw [h]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [transportComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, isoWhiskerRight_hom, whiskerRight_app,
    leftUnitor_hom_app, map_comp, Category.assoc]
  rw [← reassoc_of% (aF.hom.naturality (aA.hom.app X))]
  rw [← reassoc_of% (aF.hom.naturality (e.hom.app X))]
  simp only [Functor.id_obj]
  simp

private lemma transportComp_comp_id (aB : B ≅ B') (aF : F ≅ F')
    (e : B' ≅ 𝟭 D) (c : F' ⋙ B' ≅ F')
    (h : c = isoWhiskerLeft F' e ≪≫ rightUnitor F') :
    transportComp aF aB aF c =
      isoWhiskerLeft F (aB ≪≫ e) ≪≫ rightUnitor F := by
  rw [h]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [transportComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, isoWhiskerRight_hom, whiskerRight_app,
    rightUnitor_hom_app, Category.assoc]
  rw [reassoc_of% (e.hom.naturality (aF.hom.app X))]
  simp
end TransportUnit
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section LeftTransport
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]


private lemma leftComp_transport (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    (F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso e =
      transportComp F.leftDerivedFunctorIsoMapDerivedCategory
        G.leftDerivedFunctorIsoMapDerivedCategory FG.leftDerivedFunctorIsoMapDerivedCategory
        (derivedComp e) := by
  simp [leftDerivedFunctorCompIso, leftDerivedFunctorNatIso, transportComp, derivedComp,
    Iso.trans_assoc, ← isoWhiskerLeft_symm, ← isoWhiskerRight_symm]

variable [MonoidalCategory E] [MonoidalPreadditive E]
  [HasCountableCoproducts E]
  [HasColimitsOfShape ℤ E] [HasExactColimitsOfShape ℤ E]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : E), PreservesColimitsOfShape ℤ ((curriedTensor E).obj X)]
  [∀ (X : E), PreservesColimitsOfShape ℤ ((curriedTensor E).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution E]
  {V : Type*} [Category V] [Abelian V] [HasDerivedCategory V]

private lemma leftComp_assoc
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : E ⥤ V) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    {GH : D ⥤ V} [GH.Additive] [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    {FGH : C ⥤ V} [FGH.Additive] [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ FGH) (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ FGH)
    (h : isoWhiskerRight a H ≪≫ b = associator F G H ≪≫ isoWhiskerLeft F c ≪≫ d) :
    isoWhiskerRight
        ((F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso a)
        H.leftDerivedFunctor ≪≫
      (FG.leftDerivedFunctorCompIso H).symm ≪≫ (FG ⋙ H).leftDerivedFunctorNatIso b =
    associator F.leftDerivedFunctor G.leftDerivedFunctor H.leftDerivedFunctor ≪≫
      isoWhiskerLeft F.leftDerivedFunctor
        ((G.leftDerivedFunctorCompIso H).symm ≪≫ (G ⋙ H).leftDerivedFunctorNatIso c) ≪≫
      (F.leftDerivedFunctorCompIso GH).symm ≪≫ (F ⋙ GH).leftDerivedFunctorNatIso d := by
  simp only [leftComp_transport, associator_trans_eq]
  apply transportComp_assoc
  apply derivedComp_assoc
  simpa only [associator_trans_eq] using h

end LeftTransport
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section IdentityShift
variable (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]

omit [HasDerivedCategory C] in
private lemma complexId_shift :
    NatTrans.CommShift (mapHomologicalComplexIdIso C (.up ℤ)).hom ℤ where
  shift_comm n := by
    ext K i
    dsimp
    simp

omit [HasDerivedCategory C] in
private lemma homotopyId_shift :
    NatTrans.CommShift (mapHomotopyCategoryIdIso C (.up ℤ)).hom ℤ := by
  have := complexId_shift C
  have he : whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (mapHomotopyCategoryIdIso C (.up ℤ)).hom =
      ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        whiskerRight (mapHomologicalComplexIdIso C (.up ℤ)).hom
          (HomotopyCategory.quotient C (.up ℤ)) ≫
        (HomotopyCategory.quotient C (.up ℤ)).leftUnitor.hom ≫
        (HomotopyCategory.quotient C (.up ℤ)).rightUnitor.inv := by
    ext K
    simp only [comp_obj, id_obj, whiskerLeft_app, mapHomotopyCategoryIdIso_hom_app,
      NatTrans.comp_app, whiskerRight_app, leftUnitor_hom_app, rightUnitor_inv_app,
      Category.comp_id]
    exact (Category.id_comp _).symm
  have : NatTrans.CommShift (whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (mapHomotopyCategoryIdIso C (.up ℤ)).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
    (fun X ↦ by
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      exact ⟨K, 𝟙 _, inferInstance⟩)

private lemma derivedId_shift :
    NatTrans.CommShift (mapDerivedCategoryIdIso C).hom ℤ := by
  have := homotopyId_shift C
  have he : whiskerLeft DerivedCategory.Qh (mapDerivedCategoryIdIso C).hom =
      (𝟭 C).mapDerivedCategoryFactorsh.hom ≫
        whiskerRight (mapHomotopyCategoryIdIso C (.up ℤ)).hom DerivedCategory.Qh ≫
        DerivedCategory.Qh.leftUnitor.hom ≫ DerivedCategory.Qh.rightUnitor.inv := by
    have h := congr_arg Iso.hom (mapDerivedCategoryIdIso_factorsh C)
    rw [← cancel_mono DerivedCategory.Qh.rightUnitor.hom]
    simpa only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using h
  have : NatTrans.CommShift (whiskerLeft DerivedCategory.Qh
      (mapDerivedCategoryIdIso C).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)
end IdentityShift
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section LeftShift
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]



private lemma leftComp_shift (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {FG : C ⥤ E} [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    (e : F ⋙ G ≅ FG) :
    let := CommShift.ofIso F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    let := CommShift.ofIso FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    NatTrans.CommShift ((F.leftDerivedFunctorCompIso G).symm ≪≫
      (F ⋙ G).leftDerivedFunctorNatIso e).hom ℤ := by
  let := CommShift.ofIso F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  let := CommShift.ofIso G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  let := CommShift.ofIso FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift F.leftDerivedFunctorIsoMapDerivedCategory.symm.hom ℤ :=
    CommShift.ofIso_compatibility F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift F.leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    NatTrans.CommShift.of_iso_inv F.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift G.leftDerivedFunctorIsoMapDerivedCategory.symm.hom ℤ :=
    CommShift.ofIso_compatibility G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift G.leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    NatTrans.CommShift.of_iso_inv G.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift FG.leftDerivedFunctorIsoMapDerivedCategory.inv ℤ :=
    CommShift.ofIso_compatibility FG.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  rw [leftComp_transport]
  dsimp only [transportComp, derivedComp, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]
  infer_instance

private lemma leftUnit_shift (A : C ⥤ C) [A.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A] (e : A ≅ 𝟭 C) :
    let := CommShift.ofIso A.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
    NatTrans.CommShift (A.leftDerivedFunctorNatIso e ≪≫
      (𝟭 C).leftDerivedFunctorIsoMapDerivedCategory ≪≫ mapDerivedCategoryIdIso C).hom ℤ := by
  let := CommShift.ofIso A.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift A.leftDerivedFunctorIsoMapDerivedCategory.symm.hom ℤ :=
    CommShift.ofIso_compatibility A.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have : NatTrans.CommShift A.leftDerivedFunctorIsoMapDerivedCategory.hom ℤ :=
    NatTrans.CommShift.of_iso_inv A.leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  have := derivedId_shift C
  simp only [leftDerivedFunctorNatIso, Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.trans_hom]
  infer_instance
end LeftShift
end CategoryTheory.Functor

end CoherenceTools

namespace AlgebraicGeometry.ProEtale

open Scheme
open CategoryTheory.MonObj CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor

section FiniteFree

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

private noncomputable abbrev fieldPresheaf (E : Type) [TopologicalSpace E] [Ring E]
    [IsTopologicalRing E] : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  Profinite.continuousMapRingPresheaf E ⋙ forget₂ RingCat Ab

private noncomputable def postcompLinear {E F G : Type} [Field E] [Field F] [Field G]
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [IsTopologicalRing E] [IsTopologicalRing F] [IsTopologicalRing G]
    [Algebra E F] [Algebra E G]
    (f : F →L[E] G) : fieldPresheaf F ⟶ fieldPresheaf G where
  app S := AddCommGrpCat.ofHom
    { toFun x := ULift.up ((⟨f, f.continuous⟩ : ContinuousMap F G).comp x.down)
      map_zero' := by apply ULift.ext; ext; exact f.map_zero
      map_add' x y := by apply ULift.ext; ext; exact f.map_add _ _ }
  naturality _ _ _ := rfl


private noncomputable def presheafCoordinate {E F : Type} [Field E] [Field F]
    [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalRing E] [IsTopologicalRing F] [Algebra E F]
    (ha : Continuous (algebraMap E F)) (f : F →L[E] E) :
    (Mod.comap (Functor.whiskerRight
      (Profinite.continuousMapRingPresheafMap (algebraMap E F) ha)
      (forget₂ RingCat Ab))).obj (Mod.regular (fieldPresheaf F)) ⟶
      Mod.regular (fieldPresheaf E) :=
  Mod.homMk (postcompLinear f) (by
    ext S : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    apply ULift.ext
    ext x
    change f (algebraMap E F (a.down x) * b.down x) = a.down x * f (b.down x)
    simpa [Algebra.smul_def] using f.map_smul (a.down x) (b.down x))

private noncomputable def presheafVector {E F : Type} [Field E] [Field F]
    [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalRing E] [IsTopologicalRing F] [Algebra E F]
    (ha : Continuous (algebraMap E F)) (v : F) :
    Mod.regular (fieldPresheaf E) ⟶
      (Mod.comap (Functor.whiskerRight
        (Profinite.continuousMapRingPresheafMap (algebraMap E F) ha)
        (forget₂ RingCat Ab))).obj (Mod.regular (fieldPresheaf F)) :=
  let f : E →L[E] F :=
    ⟨(LinearMap.id : E →ₗ[E] E).smulRight v, by
      change Continuous (fun x : E ↦ x • v)
      simp only [Algebra.smul_def]
      exact continuous_mul.comp (ha.prodMk continuous_const)⟩
  Mod.homMk (postcompLinear f) (by
    ext S : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    apply ULift.ext
    ext x
    change f (a.down x * b.down x) = algebraMap E F (a.down x) * f (b.down x)
    simpa [Algebra.smul_def] using f.map_smul (a.down x) (b.down x))

private theorem presheaf_basis_iso {E F : Type} [Field E] [Field F]
    [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalRing E] [IsTopologicalRing F] [Algebra E F]
    (ha : Continuous (algebraMap E F)) {n : ℕ} (b : Module.Basis (Fin n) E F)
    (hb : ∀ i, Continuous (b.coord i)) :
    Nonempty ((Mod.comap (Functor.whiskerRight
      (Profinite.continuousMapRingPresheafMap (algebraMap E F) ha)
      (forget₂ RingCat Ab))).obj (Mod.regular (fieldPresheaf F)) ≅
      Mod.finiteFree (fieldPresheaf E) n) := by
  classical
  let c i := presheafCoordinate ha (⟨b.coord i, hb i⟩ : F →L[E] E)
  let v i := presheafVector ha (b i)
  refine ⟨⟨biproduct.lift c, biproduct.desc v, ?_, ?_⟩⟩
  · rw [biproduct.lift_desc]
    apply Mod.hom_ext
    change (Mod.forget _).map (∑ i, c i ≫ v i) = 𝟙 _
    rw [Functor.map_sum]
    ext S x
    apply ULift.ext
    ext y
    simp only [NatTrans.app_sum, NatTrans.id_app]
    change (AddCommGrpCat.homAddEquiv (∑ i, (c i ≫ v i).hom.app S) x).down y = x.down y
    rw [_root_.map_sum, AddMonoidHom.finsetSum_apply]
    change (ULift.moduleEquiv (R := ℤ) (M := ContinuousMap S.unop F)
      (∑ i, (((c i ≫ v i).hom.app S).hom x))) y = x.down y
    rw [_root_.map_sum]
    simp only [ContinuousMap.sum_apply]
    change (∑ i, b.coord i (x.down y) • b i) = x.down y
    simpa only [Module.Basis.coord_apply] using b.sum_repr (x.down y)
  · apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π,
      Category.id_comp, biproduct.ι_π]
    apply Mod.hom_ext
    ext S x
    apply ULift.ext
    ext y
    change b.coord j (x.down y • b i) = _
    by_cases hij : i = j
    · subst j
      simp [_root_.map_smul, Module.Basis.coord_apply]
    · simp [_root_.map_smul, Module.Basis.coord_apply, hij]

private theorem map_preserves_free
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ X : C, PreservesFiniteColimits (tensorLeft X)]
    [∀ X : D, PreservesFiniteColimits (tensorLeft X)]
    (L : C ⥤ D) [L.LaxMonoidal] [L.Additive]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]
    {n : ℕ} (e : (Mod.comap φ).obj (Mod.regular S) ≅ Mod.finiteFree R n) :
    Nonempty ((Mod.comap (L.map φ)).obj (Mod.regular (L.obj S)) ≅
      Mod.finiteFree (L.obj R) n) := by
  have : (L.mapMod R).Additive := ⟨by
    intro X Y f g
    exact Mod.hom_ext _ _ (L.map_add (f := f.hom) (g := g.hom))⟩
  let reg (A : C) [MonObj A] : (L.mapMod A).obj (Mod.regular A) ≅
      Mod.regular (L.obj A) := Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  exact ⟨((L.mapModComapIso φ).app (Mod.regular S) ≪≫
      (Mod.comap (L.map φ)).mapIso (reg S)).symm ≪≫
    (L.mapMod R).mapIso e ≪≫ (L.mapMod R).mapBiproduct _ ≪≫
      biproduct.mapIso (fun _ : Fin n ↦ reg R)⟩

private def restrictedRegularIso
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B B' : C} [MonObj A] [MonObj B] [MonObj B']
    (φ : A ⟶ B) (φ' : A ⟶ B') [IsMonHom φ] [IsMonHom φ']
    (e : B ≅ B') [IsMonHom e.hom] (w : φ ≫ e.hom = φ') :
    (Mod.comap φ).obj (Mod.regular B) ≅ (Mod.comap φ').obj (Mod.regular B') :=
  Mod.isoMk e (by
    change (φ ▷ B ≫ μ[B]) ≫ e.hom = A ◁ e.hom ≫ φ' ▷ B' ≫ μ[B']
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
      ← comp_whiskerRight_assoc, w, whisker_exchange_assoc])

private theorem transport_free
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] [∀ X : C, PreservesFiniteColimits (tensorLeft X)]
    {R R' S S' : C} [MonObj R] [MonObj R'] [MonObj S] [MonObj S']
    (a : R ≅ R') (b : S ≅ S') [IsMonHom a.hom] [IsMonHom b.hom]
    (φ : R ⟶ S) (φ' : R' ⟶ S') [IsMonHom φ] [IsMonHom φ']
    (w : a.hom ≫ φ' = φ ≫ b.hom) {n : ℕ}
    (e : (Mod.comap φ).obj (Mod.regular S) ≅ Mod.finiteFree R n) :
    Nonempty ((Mod.comap φ').obj (Mod.regular S') ≅ Mod.finiteFree R' n) := by
  let L : Mod C R ⥤ Mod C R' := Mod.comap a.inv
  let t : L.obj ((Mod.comap φ).obj (Mod.regular S)) ≅
      (Mod.comap φ').obj (Mod.regular S') :=
    (Mod.comapComp a.inv φ).symm.app (Mod.regular S) ≪≫
      restrictedRegularIso (a.inv ≫ φ) φ' b (by
        rw [Category.assoc, ← w, Iso.inv_hom_id_assoc])
  let r : L.obj (Mod.regular R) ≅ Mod.regular R' :=
    restrictedRegularIso a.inv (𝟙 R') a (by simp) ≪≫
      (Mod.comapId R').app (Mod.regular R')
  exact ⟨t.symm ≪≫ L.mapIso e ≪≫ L.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ : Fin n ↦ r)⟩

private theorem point_finiteFree (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)} (h : E ≤ F) :
    Nonempty ((Mod.comap (Profinite.padicSubfieldRingObjMap.{u} ℓ h)).obj
      (Mod.regular (Profinite.continuousMapRingObj F)) ≅
      Mod.finiteFree (Profinite.continuousMapRingObj E)
        (@Module.finrank E F inferInstance inferInstance
          (Module.compHom F (IntermediateField.inclusion h).toRingHom))) := by
  let := Sheaf.symmetricCategory (coherentTopology Profinite.{u}) Ab.{u + 1}
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  let := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[ℓ] E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E F
  let b := Module.finBasis E F
  have hb (i : Fin (Module.finrank E F)) : Continuous (b.coord i) :=
    ((b.coord i).restrictScalars ℚ_[ℓ]).continuous_of_finiteDimensional
  have ha : Continuous (algebraMap E F) := continuous_subtype_val.subtype_mk _
  obtain ⟨e⟩ := presheaf_basis_iso.{u} ha b hb
  obtain ⟨e'⟩ := map_preserves_free (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (Functor.whiskerRight
      (Profinite.continuousMapRingPresheafMap (algebraMap E F) ha)
      (forget₂ RingCat Ab)) e
  exact transport_free
    (Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheaf E))
    (Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheaf F))
    _ (Profinite.padicSubfieldRingObjMap ℓ h) (by
      rw [Profinite.padicSubfieldRingObjMap, Sheaf.sheafCompose_map_eq]
      simp only [Iso.hom_inv_id_assoc]
      rfl) e'

private theorem scheme_finiteFree (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)} (h : E ≤ F) :
    Nonempty ((Mod.comap (padicSubfieldRingObjMap T ℓ h)).obj
      (Mod.regular (padicSubfieldRingObj T ℓ F)) ≅
      Mod.finiteFree (padicSubfieldRingObj T ℓ E)
        (@Module.finrank E F inferInstance inferInstance
          (Module.compHom F (IntermediateField.inclusion h).toRingHom))) := by
  let := Sheaf.symmetricCategory (coherentTopology Profinite.{u}) Ab.{u + 1}
  obtain ⟨e⟩ := point_finiteFree.{u} ℓ h
  have : (upperStarFromPoint T).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  exact map_preserves_free (upperStarFromPoint T) (Profinite.padicSubfieldRingObjMap ℓ h) e

end FiniteFree

/-- Source: Compatibility.lean, A0.2 and Flat; ordinary module tensor adjunction;
TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
Proof: choose a finite field basis; its coordinate maps are continuous by the
finite-dimensional linear homeomorphism lemma. Continuous maps on profinite sets
therefore identify the finite coefficient module with the free module of that rank.
The exact strong monoidal inverse image from the point preserves this identification.
The tensor/restriction adjunction is given by `p ↦ 1 ⊗ p` and multiplication.
Restriction is exact because it only changes the action. Finite-stage tensor is exact
because its underlying module is a finite direct sum. For the algebraic closure, its
finite-stage coefficient cocone is a filtered colimit already on the finite-cover
basis of profinite sets; pullback preserves this colimit. Module sheaf filtered
colimits are exact and commute with tensor, giving flatness at the closure.
The exact-functor factorization and exact-derived-functor lemmas identify derivation
with termwise tensor on every complex, with its canonical shifts and cone triangles.
Descend the termwise unit and counit through localization; their triangle identities
are detected before localization, yielding the unbounded derived adjunction. -/
theorem condensedFiniteCoefficientCalculus
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)} (h : E ≤ F) :
    Nonempty ((Mod.comap (padicSubfieldRingObjMap T ℓ h)).obj (Mod.regular (padicSubfieldRingObj T ℓ
      F)) ≅
      Mod.finiteFree (padicSubfieldRingObj T ℓ E) (@Module.finrank E F inferInstance inferInstance
          (Module.compHom F (IntermediateField.inclusion h).toRingHom))) ∧
    PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)) ∧
    PreservesFiniteColimits (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)) ∧
    PreservesFiniteLimits
      (Mod.comap (padicSubfieldRingObjMap T ℓ h) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ F) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    PreservesFiniteColimits
      (Mod.comap (padicSubfieldRingObjMap T ℓ h) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ F) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)) ⊣ (Mod.comap
      (padicSubfieldRingObjMap T ℓ h))) ∧
    Nonempty (DerivedCategory.Q ⋙ (Mod.extendScalars (padicSubfieldRingObjMap T ℓ
      h)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).mapHomologicalComplex (ComplexShape.up ℤ)
        ⋙ DerivedCategory.Q) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ⊣ (Mod.comap
      (padicSubfieldRingObjMap T ℓ h)).mapDerivedCategory) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).mapDerivedCategory) ∧
    (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor.IsTriangulated ∧
    (∀ n : ℤ, Nonempty (shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (padicSubfieldRingObj T ℓ E))) n ⋙
      (Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ≅ (Mod.extendScalars
        (padicSubfieldRingObjMap T ℓ h)).leftDerivedFunctor ⋙ shiftFunctor (DerivedCategory (Mod
        (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ F))) n)) := by
  let f := Mod.extendScalars (padicSubfieldRingObjMap T ℓ h)
  refine ⟨scheme_finiteFree T ℓ h, inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨Mod.extendRestrictAdjunction _⟩, ?_,
    ⟨Mod.derivedExtendMapDerivedCategoryAdjunction _⟩,
    ⟨f.leftDerivedFunctorIsoMapDerivedCategory⟩, ?_, ?_⟩
  · exact ⟨Functor.isoWhiskerLeft DerivedCategory.Q
      f.leftDerivedFunctorIsoMapDerivedCategory ≪≫ f.mapDerivedCategoryFactors⟩
  · let e := f.leftDerivedFunctorIsoMapDerivedCategory.symm
    have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
    exact Functor.isTriangulated_of_iso e
  · intro n
    exact ⟨f.leftDerivedFunctor.commShiftIso n⟩

/-- Source: Compatibility.lean, A0.2 and Flat; ordinary module tensor adjunction;
TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
Proof: choose a finite field basis; its coordinate maps are continuous by the
finite-dimensional linear homeomorphism lemma. Continuous maps on profinite sets
therefore identify the finite coefficient module with the free module of that rank.
The exact strong monoidal inverse image from the point preserves this identification.
The tensor/restriction adjunction is given by `p ↦ 1 ⊗ p` and multiplication.
Restriction is exact because it only changes the action. Finite-stage tensor is exact
because its underlying module is a finite direct sum. For the algebraic closure, its
finite-stage coefficient cocone is a filtered colimit already on the finite-cover
basis of profinite sets; pullback preserves this colimit. Module sheaf filtered
colimits are exact and commute with tensor, giving flatness at the closure.
The exact-functor factorization and exact-derived-functor lemmas identify derivation
with termwise tensor on every complex, with its canonical shifts and cone triangles.
Descend the termwise unit and counit through localization; their triangle identities
are detected before localization, yielding the unbounded derived adjunction. -/
theorem condensedAlgClCoefficientCalculus
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ∧
    PreservesFiniteColimits (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ∧
    PreservesFiniteLimits
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    PreservesFiniteColimits
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E) :
        Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ) ⥤
          Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)) ⊣ (Mod.comap
      (padicSubfieldRingObjToPadicAlgCl T ℓ E))) ∧
    Nonempty (DerivedCategory.Q ⋙ (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ
      E)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ⊣
      (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E)).mapDerivedCategory) ∧
    Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ≅
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).mapDerivedCategory) ∧
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor.IsTriangulated ∧
    (∀ n : ℤ, Nonempty (shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (padicSubfieldRingObj T ℓ E))) n ⋙
      (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ≅
        (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).leftDerivedFunctor ⋙
        shiftFunctor (DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj
        T ℓ))) n)) := by
  let f := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Mod.extendRestrictAdjunction _⟩, ?_,
    ⟨Mod.derivedExtendMapDerivedCategoryAdjunction _⟩,
    ⟨f.leftDerivedFunctorIsoMapDerivedCategory⟩, ?_, ?_⟩
  · exact ⟨Functor.isoWhiskerLeft DerivedCategory.Q
      f.leftDerivedFunctorIsoMapDerivedCategory ≪≫ f.mapDerivedCategoryFactors⟩
  · let e := f.leftDerivedFunctorIsoMapDerivedCategory.symm
    have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
    exact Functor.isTriangulated_of_iso e
  · intro n
    exact ⟨f.leftDerivedFunctor.commShiftIso n⟩

-- Keep the resolution constructions behind their proved comparison API.
/-- Coherence of the canonical multiplication and unit comparisons.
Source: TwoColimit.lean, ExtendScalars; sheaf tensor coherence and localization
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
Proof: multiplication and its inverse are balanced and natural before sheafification.
The two associativity paths send `d ⊗ (c ⊗ (b ⊗ p))` to `dcb ⊗ p`.
Together with associativity of functor composition this gives the five-ring pentagon:
every path sends `h ⊗ (d ⊗ (c ⊗ (b ⊗ p)))` to `hdcb ⊗ p`.
The unit sends `a ⊗ p` to `ap`; either insertion of it in a multiplication comparison
has the same value. The same calculations hold with the last ring the closure.
These are equalities of maps from presheaf tensors and pass through the universal
property of sheafification, without asserting that global sections are pure tensors.
Apply these comparisons termwise. Shifts introduce the same differential sign on both
sides, and all coefficient factors have degree zero. Localization descends these
transformations and detects their equalities, proving the unit, associativity,
pentagon and shift compatibility laws. -/
theorem condensedCoefficientCoherence
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime] :
    (∀ (E F G H : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (h : E ≤ F) (k : F ≤ G) (l : G ≤ H),
      Functor.isoWhiskerRight (condensedCoefficientCompIso T ℓ h k) (derivedExtendScalarsSubfield T
        ℓ l) ≪≫
          (condensedCoefficientCompIso T ℓ (h.trans k) l) =
        Functor.associator (derivedExtendScalarsSubfield T ℓ h) (derivedExtendScalarsSubfield T ℓ k)
          (derivedExtendScalarsSubfield T ℓ l) ≪≫
          Functor.isoWhiskerLeft (derivedExtendScalarsSubfield T ℓ h) (condensedCoefficientCompIso T
            ℓ k l)
            ≪≫
          (condensedCoefficientCompIso T ℓ h (k.trans l))) ∧
    (∀ (E F G : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F) (k : F ≤ G),
      Functor.isoWhiskerRight (condensedCoefficientCompIso T ℓ h k)
        (derivedExtendScalarsToPadicAlgCl T ℓ G)
        ≪≫ (derivedExtendScalarsCompIso T ℓ (h.trans k)) =
        Functor.associator (derivedExtendScalarsSubfield T ℓ h) (derivedExtendScalarsSubfield T ℓ k)
          (derivedExtendScalarsToPadicAlgCl T ℓ G) ≪≫
          Functor.isoWhiskerLeft (derivedExtendScalarsSubfield T ℓ h) (derivedExtendScalarsCompIso T
            ℓ k) ≪≫
            (derivedExtendScalarsCompIso T ℓ h)) ∧
    (∀ (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
      (condensedCoefficientCompIso T ℓ (le_refl E) h) =
        Functor.isoWhiskerRight (condensedCoefficientUnitIso T ℓ E) (derivedExtendScalarsSubfield T
          ℓ h) ≪≫
          Functor.leftUnitor (derivedExtendScalarsSubfield T ℓ h)) ∧
    (∀ (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
      (condensedCoefficientCompIso T ℓ h (le_refl F)) =
        Functor.isoWhiskerLeft (derivedExtendScalarsSubfield T ℓ h) (condensedCoefficientUnitIso T ℓ
          F) ≪≫
          Functor.rightUnitor (derivedExtendScalarsSubfield T ℓ h)) ∧
    (∀ E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ),
      (derivedExtendScalarsCompIso T ℓ (le_refl E)) =
        Functor.isoWhiskerRight (condensedCoefficientUnitIso T ℓ E)
          (derivedExtendScalarsToPadicAlgCl T ℓ E)
          ≪≫ Functor.leftUnitor (derivedExtendScalarsToPadicAlgCl T ℓ E)) ∧
    (∀ (E F G : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F) (k : F ≤ G),
      NatTrans.CommShift (condensedCoefficientCompIso T ℓ h k).hom ℤ) ∧
    (∀ (E F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
      NatTrans.CommShift (derivedExtendScalarsCompIso T ℓ h).hom ℤ) ∧
    (∀ E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ), NatTrans.CommShift
      (condensedCoefficientUnitIso T ℓ E).hom ℤ) := by
  sorry

/-- Tensor preserves the finite-coefficient colimit, in the category of modules over E.
Source: Compatibility.lean, RingObj; Stacks Tags 03DB, 03EP, 03EU
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).
The parameters `D`, `e`, `hD`, `c`, `ec`, `hc` describe exactly the diagram of restricted
finite coefficient modules above E, with its inclusion cocone into the closure. This
allows any choices of the diagram and its colimit, without defining a second diagram.
`tensorRight P` is the internal relative tensor product over the E coefficient ring.
Preservation of this cocone says the canonical comparison is an isomorphism. Its
naturality in P follows from the functorial tensor and colimit comparison.
Proof: finite intermediate fields above E form a nonempty filtered poset. The union of
the continuous-function sheaves is already a sheaf, since a finite covering uses only
finitely many fields and hence their compositum. The inverse image from the point
preserves this colimit. The module forgetful functor creates it with the given action.
Tensor commutes with filtered colimits of module sheaves, so tensoring its universal
cocone by P remains a universal cocone, naturally in P. -/
theorem condensedCoefficientTensorColimit
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (D : Under E ⥤ (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)))
    (e : ∀ F : Under E, D.obj F ≅
      (Mod.comap (padicSubfieldRingObjMap T ℓ (leOfHom F.hom))).obj
        (Mod.regular (padicSubfieldRingObj T ℓ F.right)))
    (hD : ∀ (F G : Under E) (f : F ⟶ G),
      (D.map f).hom ≫ (e G).hom.hom =
        (e F).hom.hom ≫ padicSubfieldRingObjMap T ℓ (leOfHom f.right))
    (c : Cocone D)
    (ec : c.pt ≅ (Mod.comap (padicSubfieldRingObjToPadicAlgCl T ℓ E)).obj (Mod.regular
      (padicAlgClRingObj T ℓ)))
    (hc : ∀ F : Under E, (c.ι.app F).hom ≫ ec.hom.hom =
      (e F).hom.hom ≫ padicSubfieldRingObjToPadicAlgCl T ℓ F.right)
    (hcolim : IsColimit c) :
    ∀ P : (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)),
      Nonempty (IsColimit ((tensorRight P).mapCocone c)) := by
  have _ := hD
  have _ := hc
  intro P
  exact ⟨isColimitOfPreserves (tensorRight P) hcolim⟩

end AlgebraicGeometry.ProEtale
