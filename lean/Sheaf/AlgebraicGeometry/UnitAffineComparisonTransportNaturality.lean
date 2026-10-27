/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.UnitAffineComparisonTransportCore
import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData
import Sheaf.AlgebraicGeometry.TensorCompositeCohomologyRestriction
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
/-! # Naturality of canonical structural-unit cohomology transport -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
-- Keep morphism binders on the same quiver as compositions and functor images.
attribute [-instance] CategoryTheory.catToReflQuiver
attribute [local irreducible] RingedSpace.moduleCohomology tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local reducible] TopCat.Sheaf TopCat.instCategorySheaf
  topDegreeCohomologyOnBase Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory Scheme.Modules.instAbelian pushforward
attribute [local instance 2000] topDegreeModuleCategory topDegreeModulePreadditive
  topDegreeModuleAbelian
set_option allowUnsafeReducibility true in
attribute [local reducible] topDegreeModuleCategory topDegreeModulePreadditive
  topDegreeModuleAbelian
attribute [-instance] unitAffineSectionsModule unitAffineCohomModule
  unitAffineForgetCohomModule unitAffineHModule unitAffineForgetModule

private theorem sectionAdjunction_eq {A B : Scheme.{u}} (g : A ⟶ B) :
    tensorPullbackSectionAdjunction g =
      Classical.choose (exists_tensorPullbackAdjunction g) := by
  apply (existsUnique_tensorPullbackSectionAdjunction g).unique
  · exact (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction g)).1
  · intro M U m
    exact Classical.choose_spec (exists_tensorPullbackAdjunction g) M (op U) m

private theorem uniq_inv_mate
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (e : R' ≅ R) :
    (a.leftAdjointUniq (b.ofNatIsoRight e)).inv =
      ((conjugateIsoEquiv a b).symm e.symm).hom := by
  ext X
  apply (b.homEquiv _ _).injective
  apply (cancel_mono (e.hom.app _)).1
  rw [Adjunction.leftAdjointUniq_inv_app,
    ← Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hu := unit_conjugateEquiv_symm a b e.inv X
  change a.unit.app X ≫ e.inv.app _ =
    b.homEquiv _ _ (((conjugateIsoEquiv a b).symm e.symm).hom.app X) at hu
  rw [← hu]
  simp

private theorem sectionComp_eq {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    (tensorPullbackSectionComp a b).inv = (tensorSectionsComp a b).hom := by
  unfold tensorPullbackSectionComp tensorSectionsComp
  rw [sectionAdjunction_eq, sectionAdjunction_eq, sectionAdjunction_eq]
  exact uniq_inv_mate _ _ _

private theorem mate_homEquiv
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (e : R ≅ R')
    (M : C) (N : D) (v : L.obj M ⟶ N) :
    b.homEquiv M N ((((conjugateIsoEquiv a b).symm e).hom.app M) ≫ v) =
      a.homEquiv M N v ≫ e.hom.app N := by
  rw [Adjunction.homEquiv_naturality_right]
  have hu := unit_conjugateEquiv_symm a b e.hom M
  change a.unit.app M ≫ e.hom.app (L.obj M) =
    b.homEquiv M (L.obj M) (((conjugateIsoEquiv a b).symm e).hom.app M) at hu
  rw [← hu, Category.assoc, ← e.hom.naturality]
  simp only [Adjunction.homEquiv_unit, Category.assoc]

private theorem coefficient_triangle {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    (Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _
      ((tensorSectionsComp a b).hom.app (SheafOfModules.unit C.ringCatSheaf)) ≫
        (pushforward a).map (tensorPullbackObjUnitToUnit (a ≫ b)) =
      tensorPullbackObjUnitToUnit b ≫
        SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom := by
  let aa := Classical.choose (exists_tensorPullbackAdjunction a)
  let ab := Classical.choose (exists_tensorPullbackAdjunction b)
  let ac := Classical.choose (exists_tensorPullbackAdjunction (a ≫ b))
  apply (ab.homEquiv _ _).injective
  rw [← aa.homEquiv_naturality_right]
  have hm := mate_homEquiv ac (ab.comp aa) (pushforwardComp a b).symm
    (SheafOfModules.unit C.ringCatSheaf) (SheafOfModules.unit A.ringCatSheaf)
    (tensorPullbackObjUnitToUnit (a ≫ b))
  change (ab.comp aa).homEquiv _ _
      ((tensorSectionsComp a b).hom.app _ ≫ tensorPullbackObjUnitToUnit (a ≫ b)) =
    ac.homEquiv _ _ (tensorPullbackObjUnitToUnit (a ≫ b)) ≫
      (pushforwardComp a b).inv.app _ at hm
  have hm' := hm
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply] at hm'
  rw [hm']
  have hn := ab.homEquiv_naturality_right (tensorPullbackObjUnitToUnit b)
    (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom)
  refine Eq.trans ?_ hn.symm
  have he (D E : Scheme.{u}) (k : D ⟶ E) :
      (Classical.choose (exists_tensorPullbackAdjunction k)).homEquiv _ _
        (tensorPullbackObjUnitToUnit k) =
      SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom :=
    (Equiv.apply_symm_apply _ _)
  rw [he, he]
  ext U
  rfl

attribute [local irreducible] tensorSectionsComp tensorSectionsUnit moduleCohomologyFMap
  tensorPullbackSectionComp tensorPullbackSectionAdjunction unitAffineCoefficientH
  unitAffineHMap unitAffineHIso unitAffineSymmetry Functor.rightDerived

private theorem coefficient_triangle_congr {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) :
    (Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _
      ((tensorSectionsComp a b).hom.app (SheafOfModules.unit C.ringCatSheaf) ≫
        eqToHom (congrArg (fun k ↦ (tensorPullback k).obj
          (SheafOfModules.unit C.ringCatSheaf)) w)) ≫
        (pushforward a).map (tensorPullbackObjUnitToUnit c) =
      tensorPullbackObjUnitToUnit b ≫
        SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom := by
  subst c
  simpa using coefficient_triangle a b

private theorem cohomology_triangle {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (q : ℕ) :
    moduleCohomologyFMap a
      ((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _
        ((tensorSectionsComp a b).hom.app (SheafOfModules.unit C.ringCatSheaf) ≫
          eqToHom (congrArg (fun k ↦ (tensorPullback k).obj
            (SheafOfModules.unit C.ringCatSheaf)) w))) q ≫
      (unitAffineCoefficientH c q).hom =
    (unitAffineCoefficientH b q).hom ≫ unitAffineHMap a q := by
  unfold unitAffineCoefficientH unitAffineHMap unitAffineCoefficientIso
  change moduleCohomologyFMap a _ q ≫
      (forget₂ _ AddCommGrpCat).map
        ((RingedSpace.moduleCohomology A.toRingedSpace q).map
          (tensorPullbackObjUnitToUnit c)) =
    (forget₂ _ AddCommGrpCat).map
        ((RingedSpace.moduleCohomology B.toRingedSpace q).map
          (tensorPullbackObjUnitToUnit b)) ≫ moduleCohomologyFMap a _ q
  exact (moduleCohomologyFMap_target_naturality a (tensorPullbackObjUnitToUnit c) _ q).trans
    ((congrArg (fun φ ↦ moduleCohomologyFMap a φ q)
      (coefficient_triangle_congr a b c w)).trans
      (moduleCohomologyFMap_source_naturality a (tensorPullbackObjUnitToUnit b)
        (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom) q).symm)

private theorem degree_hom (A : Scheme.{u}) {M N : A.Modules}
    (i : @Iso A.Modules (@Scheme.Modules.instCategory A) M N) :
    @Iso.hom A.Modules (topDegreeModuleCategory A) M N i =
      @Iso.hom A.Modules (@Scheme.Modules.instCategory A) M N i := by
  rfl

private theorem degree_transport_comp (A : Scheme.{u}) {M N P : A.Modules}
    (t : @Quiver.Hom A.Modules (topDegreeModuleCategory A).toCategoryStruct.toQuiver M N)
    (w : N = P) :
    @CategoryStruct.comp A.Modules (topDegreeModuleCategory A).toCategoryStruct M N P t
        (@eqToHom A.Modules (topDegreeModuleCategory A).toCategoryStruct N P w) =
      @CategoryStruct.comp A.Modules (@Scheme.Modules.instCategory A).toCategoryStruct
        M N P t (@eqToHom A.Modules (@Scheme.Modules.instCategory A).toCategoryStruct N P w) := by
  subst P
  rfl

private theorem sectionComp_transport_hom {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (G : C.Modules) :
    (@Iso.trans A.Modules (topDegreeModuleCategory A)
      ((tensorPullback a).obj ((tensorPullback b).obj G))
      ((tensorPullback (a ≫ b)).obj G) ((tensorPullback c).obj G)
      ((tensorPullbackSectionComp a b).symm.app G)
      (@eqToIso A.Modules (topDegreeModuleCategory A) _ _
        (congrArg (fun k ↦ (tensorPullback k).obj G) w))).hom =
      (tensorSectionsComp a b).hom.app G ≫
        eqToHom (congrArg (fun k ↦ (tensorPullback k).obj G) w) := by
  rw [Iso.trans_hom]
  rw [degree_hom A ((tensorPullbackSectionComp a b).symm.app G)]
  rw [Iso.app_hom, Iso.symm_hom, sectionComp_eq, eqToIso.hom]

private theorem coherentEdgeCoefficientIso_hom {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : T' ⟶ T)
    (w : coherentEdgeXMap f g h ≫ pullback.fst f g = pullback.fst f (h ≫ g)) :
    (coherentEdgeCoefficientIso f G g h).hom =
      (tensorSectionsComp (coherentEdgeXMap f g h) (pullback.fst f g)).hom.app G ≫
        eqToHom (congrArg (fun k ↦ (tensorPullback k).obj G) w) :=
  sectionComp_transport_hom (coherentEdgeXMap f g h) (pullback.fst f g)
    (pullback.fst f (h ≫ g)) w G

private def baseForgetIso {A B : Scheme.{u}} (f : A ⟶ B) (F : A.Modules) :
    (forget₂ _ AddCommGrpCat).obj (topDegreeCohomologyOnBase f F) ≅
      (forget₂ _ AddCommGrpCat).obj
        ((RingedSpace.moduleCohomology A.toRingedSpace 1).obj F) := by
  unfold topDegreeCohomologyOnBase
  exact Iso.refl _

attribute [local irreducible] baseForgetIso

-- Keep the scalar-restricted group in the same form as the public comparison.
private def coherentForgetIso {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :
    (forget₂ _ AddCommGrpCat).obj (coherentEdgeH f G g) ≅
      (forget₂ _ AddCommGrpCat).obj
        ((RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace 1).obj
          (coherentEdgeCoefficient f G g)) :=
  baseForgetIso (pullback.snd f g) (coherentEdgeCoefficient f G g)

attribute [local irreducible] coherentForgetIso

private theorem basePullback_square {A B C D : Scheme.{u}}
    (f : A ⟶ C) (g : B ⟶ D) (p : B ⟶ A) (F : A.Modules) (G : B.Modules)
    (a : (tensorPullback p).obj F ⟶ G) :
    topDegreeCohomologyPullback f g p F G a ≫ (baseForgetIso g G).hom =
      (baseForgetIso f F).hom ≫
        moduleCohomologyFMap p ((tensorPullbackSectionAdjunction p).homEquiv F G a) 1 := by
  delta topDegreeCohomologyPullback baseForgetIso
  rfl

-- This interface fixes the underlying cohomology groups before specialization.
private def coefficientCohomologyMap {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (_w : a ≫ b = c) (q : ℕ) :
    AddCommGrpCat.of
      ((RingedSpace.moduleCohomology B.toRingedSpace q).obj
        ((tensorPullback b).obj (SheafOfModules.unit C.ringCatSheaf))) ⟶
    AddCommGrpCat.of
      ((RingedSpace.moduleCohomology A.toRingedSpace q).obj
        ((tensorPullback c).obj (SheafOfModules.unit C.ringCatSheaf))) :=
  (unitAffineCoefficientH b q).hom ≫ unitAffineHMap a q ≫
    (unitAffineCoefficientH c q).inv

attribute [local irreducible] coefficientCohomologyMap

private theorem coefficientCohomologyMap_eq {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (q : ℕ) :
    coefficientCohomologyMap a b c w q =
      moduleCohomologyFMap a
        ((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _
          ((tensorSectionsComp a b).hom.app (SheafOfModules.unit C.ringCatSheaf) ≫
            eqToHom (congrArg (fun k ↦ (tensorPullback k).obj
              (SheafOfModules.unit C.ringCatSheaf)) w))) q := by
  apply (cancel_mono (unitAffineCoefficientH c q).hom).1
  calc
    coefficientCohomologyMap a b c w q ≫ (unitAffineCoefficientH c q).hom =
        (unitAffineCoefficientH b q).hom ≫ unitAffineHMap a q := by
      simp only [coefficientCohomologyMap, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    _ = _ := (cohomology_triangle a b c w q).symm

section
attribute [local instance 4000] Scheme.Modules.instCategory
private theorem coefficientCohomologyMap_eq_native_fmap {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (q : ℕ) :
    coefficientCohomologyMap a b c w q =
      moduleCohomologyFMap a
        (((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _).toFun
          ((tensorSectionsComp a b).hom.app (SheafOfModules.unit C.ringCatSheaf) ≫
            eqToHom (congrArg (fun k ↦ (tensorPullback k).obj
              (SheafOfModules.unit C.ringCatSheaf)) w))) q := by
  exact (coefficientCohomologyMap_eq a b c w q).trans
    (congrArg (fun t ↦ moduleCohomologyFMap a
      (((Classical.choose (exists_tensorPullbackAdjunction a)).homEquiv _ _).toFun t) q)
      (degree_transport_comp A
        ((tensorSectionsComp a b).hom.app (SheafOfModules.unit C.ringCatSheaf))
        (congrArg (fun k ↦ (tensorPullback k).obj (SheafOfModules.unit C.ringCatSheaf)) w)))

private theorem coefficientCohomologyMap_eq_native {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (q : ℕ) :
    coefficientCohomologyMap a b c w q =
      tensorCompositeCohomologyRestriction a b c w (SheafOfModules.unit C.ringCatSheaf) q := by
  exact (coefficientCohomologyMap_eq_native_fmap a b c w q).trans
    (tensorCompositeCohomologyRestriction_eq a b c w
      (SheafOfModules.unit C.ringCatSheaf) q).symm

end

private theorem postcomp_eq {C : Type*} [Category C] {A B D : C}
    (r s : A ⟶ B) (h : r = s) (t : B ⟶ D) : r ≫ t = s ≫ t :=
  congrArg (fun v ↦ v ≫ t) h

private theorem coefficientCohomologyMap_triangle {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (q : ℕ) :
    coefficientCohomologyMap a b c w q ≫ (unitAffineCoefficientH c q).hom =
      (unitAffineCoefficientH b q).hom ≫ unitAffineHMap a q := by
  exact (postcomp_eq _ _ (coefficientCohomologyMap_eq a b c w q)
    (unitAffineCoefficientH c q).hom).trans (cohomology_triangle a b c w q)

private theorem basePullback_square_normalized {A B C D Z : Scheme.{u}}
    (f : A ⟶ C) (g : B ⟶ D) (p : B ⟶ A) (b : A ⟶ Z) (c : B ⟶ Z)
    (w : p ≫ b = c)
    (a : (tensorPullback p).obj ((tensorPullback b).obj
      (SheafOfModules.unit Z.ringCatSheaf)) ⟶
        (tensorPullback c).obj (SheafOfModules.unit Z.ringCatSheaf))
    (ha : a = (tensorSectionsComp p b).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      eqToHom (congrArg (fun k ↦ (tensorPullback k).obj
        (SheafOfModules.unit Z.ringCatSheaf)) w)) :
    topDegreeCohomologyPullback f g p
        ((tensorPullback b).obj (SheafOfModules.unit Z.ringCatSheaf))
        ((tensorPullback c).obj (SheafOfModules.unit Z.ringCatSheaf)) a ≫
        (baseForgetIso g ((tensorPullback c).obj (SheafOfModules.unit Z.ringCatSheaf))).hom =
      (baseForgetIso f ((tensorPullback b).obj (SheafOfModules.unit Z.ringCatSheaf))).hom ≫
        coefficientCohomologyMap p b c w 1 := by
  rw [coefficientCohomologyMap_eq p b c w 1, ← ha]
  have hs := basePullback_square f g p
    ((tensorPullback b).obj (SheafOfModules.unit Z.ringCatSheaf))
    ((tensorPullback c).obj (SheafOfModules.unit Z.ringCatSheaf)) a
  rw [sectionAdjunction_eq p] at hs
  exact hs

private theorem coherentPullback_square_normalized {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T)
    (w : coherentEdgeXMap f g h ≫ pullback.fst f g = pullback.fst f (h ≫ g)) :
    coherentEdgePullback f (SheafOfModules.unit X.ringCatSheaf) g h ≫
        (coherentForgetIso f (SheafOfModules.unit X.ringCatSheaf) (h ≫ g)).hom =
      (coherentForgetIso f (SheafOfModules.unit X.ringCatSheaf) g).hom ≫
        coefficientCohomologyMap (coherentEdgeXMap f g h) (pullback.fst f g)
          (pullback.fst f (h ≫ g)) w 1 := by
  unfold coherentForgetIso
  exact basePullback_square_normalized (pullback.snd f g) (pullback.snd f (h ≫ g))
    (coherentEdgeXMap f g h) (pullback.fst f g) (pullback.fst f (h ≫ g)) w
    (coherentEdgeCoefficientIso f (SheafOfModules.unit X.ringCatSheaf) g h).hom
    (coherentEdgeCoefficientIso_hom f (SheafOfModules.unit X.ringCatSheaf) g h w)

private theorem unitAffineSymmetry_raw {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) :
    (unitAffineSymmetry f g).hom ≫
        (coherentForgetIso f (SheafOfModules.unit X.ringCatSheaf) g).hom =
      (unitAffineCoefficientH (pullback.snd g f) 1).hom ≫
        unitAffineHMap (pullbackSymmetry g f).inv 1 ≫
          (unitAffineCoefficientH (pullback.fst f g) 1).inv := by
  unfold unitAffineSymmetry unitAffineHIso coherentForgetIso baseForgetIso
  rfl

private theorem conjugate_square {C : Type*} [Category C]
    {A A' B B' U U' V V' : C}
    (iA : A ≅ U) (iA' : A' ≅ U') (iB : B ≅ V) (iB' : B' ≅ V')
    (r : A ⟶ A') (q : B ⟶ B') (s : U ⟶ V) (s' : U' ⟶ V')
    (a : U ⟶ U') (b : V ⟶ V')
    (hr : r ≫ iA'.hom = iA.hom ≫ a)
    (hq : q ≫ iB'.hom = iB.hom ≫ b) (hs : a ≫ s' = s ≫ b) :
    r ≫ (iA'.hom ≫ s' ≫ iB'.inv) = (iA.hom ≫ s ≫ iB.inv) ≫ q := by
  apply (cancel_mono iB'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hr]
  simp only [Category.assoc]
  rw [hs, hq]
  simp only [Iso.inv_hom_id_assoc]


private theorem square_of_iso {C : Type*} [Category C]
    {A A' B B' N N' : C} (i : B ≅ N) (i' : B' ≅ N')
    (j : A ⟶ B) (j' : A' ⟶ B') (r : A ⟶ A') (p : B ⟶ B') (q : N ⟶ N')
    (t : A ⟶ N) (t' : A' ⟶ N')
    (hj : j ≫ i.hom = t) (hj' : j' ≫ i'.hom = t')
    (hp : p ≫ i'.hom = i.hom ≫ q) (hr : r ≫ t' = t ≫ q) :
    r ≫ j' = j ≫ p := by
  apply (cancel_mono i'.hom).1
  calc
    (r ≫ j') ≫ i'.hom = r ≫ t' := by rw [Category.assoc, hj']
    _ = t ≫ q := hr
    _ = (j ≫ i.hom) ≫ q := by rw [hj]
    _ = (j ≫ p) ≫ i'.hom := by simp only [Category.assoc, hp]

private theorem symmetry_square {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T)
    (a : Limits.pullback (h ≫ g) f ⟶ Limits.pullback g f)
    (ha : a ≫ pullback.snd g f = pullback.snd (h ≫ g) f)
    (hb : a ≫ pullback.fst g f = pullback.fst (h ≫ g) f ≫ h)
    : coefficientCohomologyMap a (pullback.snd g f) (pullback.snd (h ≫ g) f) ha 1 ≫
        (unitAffineSymmetry f (h ≫ g)).hom =
      (unitAffineSymmetry f g).hom ≫
        coherentEdgePullback f (SheafOfModules.unit X.ringCatSheaf) g h := by
  let b := coherentEdgeXMap f g h
  have hbf : b ≫ pullback.fst f g = pullback.fst f (h ≫ g) := by
    simp [b, coherentEdgeXMap, baseChangeMap, pullback.map, pullback.lift_fst]
  have hab : (pullbackSymmetry (h ≫ g) f).inv ≫ a =
      b ≫ (pullbackSymmetry g f).inv := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hb]
      simp [b, coherentEdgeXMap, baseChangeMap, pullback.map, pullback.lift_snd]
    · simp only [Category.assoc, ha]
      simp [b, coherentEdgeXMap, baseChangeMap, pullback.map, pullback.lift_fst]
  have hH : unitAffineHMap a 1 ≫
      unitAffineHMap (pullbackSymmetry (h ≫ g) f).inv 1 =
      unitAffineHMap (pullbackSymmetry g f).inv 1 ≫ unitAffineHMap b 1 := by
    rw [← unitAffineHMap_comp, ← unitAffineHMap_comp, hab]
  have hR := coefficientCohomologyMap_triangle a (pullback.snd g f)
    (pullback.snd (h ≫ g) f) ha 1
  have hQ := coefficientCohomologyMap_triangle b (pullback.fst f g)
    (pullback.fst f (h ≫ g)) hbf 1
  let r := coefficientCohomologyMap a (pullback.snd g f) (pullback.snd (h ≫ g) f) ha 1
  let q := coefficientCohomologyMap b (pullback.fst f g) (pullback.fst f (h ≫ g)) hbf 1
  let t := (unitAffineCoefficientH (pullback.snd g f) 1).hom ≫
    unitAffineHMap (pullbackSymmetry g f).inv 1 ≫
      (unitAffineCoefficientH (pullback.fst f g) 1).inv
  let t' := (unitAffineCoefficientH (pullback.snd (h ≫ g) f) 1).hom ≫
    unitAffineHMap (pullbackSymmetry (h ≫ g) f).inv 1 ≫
      (unitAffineCoefficientH (pullback.fst f (h ≫ g)) 1).inv
  have he := conjugate_square
    (unitAffineCoefficientH (pullback.snd g f) 1)
    (unitAffineCoefficientH (pullback.snd (h ≫ g) f) 1)
    (unitAffineCoefficientH (pullback.fst f g) 1)
    (unitAffineCoefficientH (pullback.fst f (h ≫ g)) 1)
    r q (unitAffineHMap (pullbackSymmetry g f).inv 1)
    (unitAffineHMap (pullbackSymmetry (h ≫ g) f).inv 1)
    (unitAffineHMap a 1) (unitAffineHMap b 1) hR hQ hH
  have hQbase := coherentPullback_square_normalized f g h hbf
  have hi := square_of_iso
    (coherentForgetIso f (SheafOfModules.unit X.ringCatSheaf) g)
    (coherentForgetIso f (SheafOfModules.unit X.ringCatSheaf) (h ≫ g))
    (unitAffineSymmetry f g).hom (unitAffineSymmetry f (h ≫ g)).hom r
    (coherentEdgePullback f (SheafOfModules.unit X.ringCatSheaf) g h) q t t'
    (unitAffineSymmetry_raw f g) (unitAffineSymmetry_raw f (h ≫ g)) hQbase he
  exact hi

private theorem sections_restriction {S T T' : Scheme.{u}}
    (g : T ⟶ S) (h : T' ⟶ T) (E : S.Modules)
    (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
      ((tensorPullback g).obj E)) :
    coherentEdgeRho g h E s =
      ((tensorSectionsComp h g).hom.app E).app ⊤
        (tensorSectionsUnit h ((tensorPullback g).obj E) s) := by
  unfold coherentEdgeRho coherentEdgeSectionPullback topDegreeSectionPullback
    tensorSectionsUnit
  rw [sectionComp_eq, sectionAdjunction_eq]
  rfl

-- Keep cohomology on its bundled module structure; only name section evaluation.
attribute [local instance 3000] unitAffineSectionsModule


section
attribute [local instance 4000] Scheme.Modules.instCategory

private theorem sectionsEvaluation_left (Y : Scheme.{u}) (M : Y.Modules)
    (x : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M) :
    ((x : Γ(M, ⊤)) : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M) = x := by
  rfl

private theorem sectionsEvaluation_right (Y : Scheme.{u}) (M : Y.Modules)
    (x : Γ(M, ⊤)) :
    ((x : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M) : Γ(M, ⊤)) = x := by
  rfl

private theorem sectionsEvaluation_add (Y : Scheme.{u}) (M : Y.Modules)
    (x y : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M) :
    ((x + y : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M) : Γ(M, ⊤)) =
      (x : Γ(M, ⊤)) + (y : Γ(M, ⊤)) := by
  rfl

-- Construct the identity with its two declared section-group endpoints.
private def sectionsEvaluation (Y : Scheme.{u}) (M : Y.Modules) :
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M ≃+ Γ(M, ⊤) where
  toFun := fun x ↦ x
  invFun := fun x ↦ x
  left_inv := sectionsEvaluation_left Y M
  right_inv := sectionsEvaluation_right Y M
  map_add' := sectionsEvaluation_add Y M

private theorem sectionsEvaluation_comp {Y Z : Scheme.{u}} (M : Y.Modules)
    (N : Z.Modules) {B C : AddCommGrpCat.{u}}
    (a : Γ(M, ⊤) ⟶ B) (b : B ⟶ C) (c : C ⟶ Γ(N, ⊤))
    (s : (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj M) :
    (a ≫ b ≫ c) (sectionsEvaluation Y M s) =
      sectionsEvaluation Z N (c (b (a s))) := by
  rfl

-- Keep the chart's identity-functor scheme in both section-group endpoints.
private def chartSectionsEquiv {S : Scheme.{u}} (V : S.Etale) (E : S.Modules) :
    (RingedSpace.globalSectionsFunctor ((𝟭 Scheme).obj V.left).toRingedSpace).obj
      ((tensorPullback V.hom).obj E) ≃+ Γ((tensorPullback V.hom).obj E, ⊤) :=
  sectionsEvaluation ((𝟭 Scheme).obj V.left) ((tensorPullback V.hom).obj E)

attribute [local irreducible] chartSectionsEquiv

section
attribute [local instance 4000] Scheme.Modules.instCategory
private theorem affineRestriction_eq {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etale} (h : V' ⟶ V) :
    letI : MorphismProperty.HasPullbacksAlong @AlgebraicGeometry.Etale f :=
      Etale.RawRestrictedComparison.etalePullbacks f
    letI : MorphismProperty.IsStableUnderBaseChangeAlong @AlgebraicGeometry.Etale f :=
      Etale.RawRestrictedComparison.etaleBaseChange f
    let B : S.Etale ⥤ X.Etale :=
      MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f
    let a : B.obj V' ⟶ B.obj V := B.map h
    @coefficientCohomologyMap (Limits.pullback V'.hom f) (Limits.pullback V.hom f) X
      a.left (pullback.snd V.hom f)
      (pullback.snd V'.hom f) a.w 1 =
      affineRealizationRestriction f (SheafOfModules.unit X.ringCatSheaf) 1 h := by
  dsimp only [affineRealizationRestriction, affineRealizationCoefficient]
  exact @coefficientCohomologyMap_eq_native (Limits.pullback V'.hom f)
    (Limits.pullback V.hom f) X _ _ _ _ _

end

private theorem chart_restriction {S : Scheme.{u}} (E : S.Modules)
    {V V' : S.Etale} (h : V' ⟶ V)
    (s : (RingedSpace.globalSectionsFunctor ((𝟭 Scheme).obj V.left).toRingedSpace).obj
      ((tensorPullback V.hom).obj E)) :
    etaleTensorSectionsRestriction E h (chartSectionsEquiv V E s) =
      chartSectionsEquiv V' E
        ((eqToHom (congrArg (fun k ↦ (tensorPullback k).obj E) h.w)).app ⊤
          (((tensorSectionsComp h.left V.hom).hom.app E).app ⊤
            (tensorSectionsUnit h.left ((tensorPullback V.hom).obj E) s))) := by
  rcases V with ⟨⟨T, p, g⟩, hg⟩
  rcases V' with ⟨⟨T', p', g'⟩, hg'⟩
  rcases h with ⟨⟨l, r, w⟩, hl, hr⟩
  change T' ⟶ T at l
  change p' ⟶ p at r
  have w' : l ≫ g = g' := by simpa using w
  subst g'
  unfold chartSectionsEquiv etaleTensorSectionsRestriction
  exact sectionsEvaluation_comp _ _ _ _ _ s

private def symmetryFn {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : (RingedSpace.moduleCohomology (Limits.pullback g f).toRingedSpace 1).obj
      ((tensorPullback (pullback.snd g f)).obj (SheafOfModules.unit X.ringCatSheaf))) :
    coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g :=
  (unitAffineSymmetry f g).hom x

private def coefficientFn {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (w : a ≫ b = c) (q : ℕ)
    (x : (RingedSpace.moduleCohomology B.toRingedSpace q).obj
      ((tensorPullback b).obj (SheafOfModules.unit C.ringCatSheaf))) :
    (RingedSpace.moduleCohomology A.toRingedSpace q).obj
      ((tensorPullback c).obj (SheafOfModules.unit C.ringCatSheaf)) :=
  coefficientCohomologyMap a b c w q x

private def affineFn {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) (q : ℕ)
    {V V' : S.Etale} (h : V' ⟶ V)
    (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V)) :
    (RingedSpace.moduleCohomology (Limits.pullback V'.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V') :=
  affineRealizationRestriction f G q h x

private theorem symmetryFn_square {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T)
    (a : Limits.pullback (h ≫ g) f ⟶ Limits.pullback g f)
    (ha : a ≫ pullback.snd g f = pullback.snd (h ≫ g) f)
    (hb : a ≫ pullback.fst g f = pullback.fst (h ≫ g) f ≫ h)
    (x : (RingedSpace.moduleCohomology (Limits.pullback g f).toRingedSpace 1).obj
      ((tensorPullback (pullback.snd g f)).obj (SheafOfModules.unit X.ringCatSheaf))) :
    symmetryFn f (h ≫ g)
      (coefficientFn a (pullback.snd g f) (pullback.snd (h ≫ g) f) ha 1 x) =
      coherentEdgePullback f (SheafOfModules.unit X.ringCatSheaf) g h
        (symmetryFn f g x) := by
  unfold symmetryFn coefficientFn
  exact CategoryTheory.congr_fun (symmetry_square f g h a ha hb) x


private theorem coefficientFn_affineFn_eq {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etale} (h : V' ⟶ V) :
    letI : MorphismProperty.HasPullbacksAlong @AlgebraicGeometry.Etale f :=
      Etale.RawRestrictedComparison.etalePullbacks f
    letI : MorphismProperty.IsStableUnderBaseChangeAlong @AlgebraicGeometry.Etale f :=
      Etale.RawRestrictedComparison.etaleBaseChange f
    let B : S.Etale ⥤ X.Etale :=
      MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f
    let a : B.obj V' ⟶ B.obj V := B.map h
    @coefficientFn (Limits.pullback V'.hom f) (Limits.pullback V.hom f) X
      a.left (pullback.snd V.hom f)
      (pullback.snd V'.hom f) a.w 1 =
      affineFn f (SheafOfModules.unit X.ringCatSheaf) 1 h := by
  dsimp only [coefficientFn, affineFn]
  funext x
  exact CategoryTheory.congr_fun (affineRestriction_eq f h) x

attribute [local irreducible] symmetryFn coefficientFn affineFn

private theorem comparisonFn_square {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (E : S.Modules)
    (e : ∀ (U : Scheme.{u}) (k : U ⟶ S) (_ : IsAffine U),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) k →
        (RingedSpace.globalSectionsFunctor U.toRingedSpace).obj ((tensorPullback k).obj E))
    (en : ∀ (U U' : Scheme.{u}) (k : U ⟶ S) (l : U' ⟶ U)
      (hU : IsAffine U) (hU' : IsAffine U')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) k),
      e U' (l ≫ k) hU' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) k l x) =
      coherentEdgeRho k l E (e U k hU x))
    (g : T ⟶ S) (g' : T' ⟶ S) (h : T' ⟶ T) (w : h ≫ g = g')
    (hT : IsAffine T) (hT' : IsAffine T')
    (a : Limits.pullback g' f ⟶ Limits.pullback g f)
    (ha : a ≫ pullback.snd g f = pullback.snd g' f)
    (hb : a ≫ pullback.fst g f = pullback.fst g' f ≫ h)
    (x : (RingedSpace.moduleCohomology (Limits.pullback g f).toRingedSpace 1).obj
      ((tensorPullback (pullback.snd g f)).obj (SheafOfModules.unit X.ringCatSheaf))) :
    e T' g' hT' ((symmetryFn f g')
      (coefficientFn a (pullback.snd g f) (pullback.snd g' f) ha 1 x)) =
      Scheme.Modules.Hom.app
        (eqToHom (congrArg (fun k ↦ (tensorPullback k).obj E) w)) ⊤
        (((tensorSectionsComp h g).hom.app E).app ⊤
          (tensorSectionsUnit h ((tensorPullback g).obj E)
            (e T g hT ((symmetryFn f g) x)))) := by
  subst g'
  have hs := symmetryFn_square f g h a ha hb x
  change e T' (h ≫ g) hT' _ =
    ((tensorSectionsComp h g).hom.app E).app ⊤
      (tensorSectionsUnit h ((tensorPullback g).obj E)
        (e T g hT ((symmetryFn f g) x)))
  exact (congrArg (e T' (h ≫ g) hT') hs).trans
    ((en T T' g h hT hT' ((symmetryFn f g) x)).trans
      (sections_restriction g h E _))


private theorem raw_chart_comparison_square {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (E : S.Modules) [E.IsQuasicoherent]
    (e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g →
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E))
    (e_natural : ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
      (hT : IsAffine T) (hT' : IsAffine T')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g),
      e T' (h ≫ g) hT' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) g h x) =
      coherentEdgeRho g h E (e T g hT x)) :
      (∀ (V V' : S.Etale) [hV : IsAffine V.left] [hV' : IsAffine V'.left]
        (h : V' ⟶ V)
        (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
          (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)),
        e V'.left V'.hom hV' ((symmetryFn f V'.hom)
          (affineFn f (SheafOfModules.unit X.ringCatSheaf) 1 h x)) =
        Scheme.Modules.Hom.app
          (eqToHom (congrArg (fun k ↦ (tensorPullback k).obj E) h.w)) ⊤
          (((tensorSectionsComp h.left V.hom).hom.app E).app ⊤
            (tensorSectionsUnit h.left ((tensorPullback V.hom).obj E)
              (e V.left V.hom hV ((symmetryFn f V.hom) x))))) := by
  intro V V' hV hV' h x
  rcases V with ⟨⟨T, p, g⟩, hg⟩
  rcases V' with ⟨⟨T', p', g'⟩, hg'⟩
  rcases h with ⟨⟨l, r, w⟩, hl, hr⟩
  change T' ⟶ T at l
  change p' ⟶ p at r
  have w' : l ≫ g = g' := by simpa using w
  subst g'
  let V : S.Etale := ⟨⟨T, p, g⟩, hg⟩
  let V' : S.Etale := ⟨⟨T', p', l ≫ g⟩, hg'⟩
  let h : V' ⟶ V := ⟨⟨l, r, w⟩, hl, hr⟩
  let : MorphismProperty.HasPullbacksAlong @AlgebraicGeometry.Etale f :=
    Etale.RawRestrictedComparison.etalePullbacks f
  let : MorphismProperty.IsStableUnderBaseChangeAlong @AlgebraicGeometry.Etale f :=
    Etale.RawRestrictedComparison.etaleBaseChange f
  let B : S.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f
  let a : Limits.pullback V'.hom f ⟶ Limits.pullback V.hom f := (B.map h).left
  have ha : a ≫ pullback.snd V.hom f = pullback.snd V'.hom f := (B.map h).w
  have hs := @comparisonFn_square X S ((𝟭 Scheme).obj V.left) ((𝟭 Scheme).obj V'.left)
    f E e e_natural
    V.hom V'.hom h.left h.w hV hV' a ha (by
      change pullback.lift (pullback.fst V'.hom f ≫ h.left)
          (pullback.snd V'.hom f) _ ≫ pullback.fst V.hom f = _
      exact pullback.lift_fst _ _ _) x
  have hm := congrFun (coefficientFn_affineFn_eq f h) x
  exact (congrArg (fun y ↦ e V'.left V'.hom hV'
    ((symmetryFn f V'.hom) y)) hm).symm.trans hs

private def equivalenceFn {X S : Scheme.{u}} (f : X ⟶ S)
    (E : S.Modules)
    (e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g ≃ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E)) :
    ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g →
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E) :=
  fun T g hT x ↦ e T g hT x

private theorem equivalenceFn_natural {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (E : S.Modules) [E.IsQuasicoherent]
    (e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g ≃ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E))
    (e_natural : ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
      (hT : IsAffine T) (hT' : IsAffine T')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g),
      e T' (h ≫ g) hT' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) g h x) =
      coherentEdgeRho g h E (e T g hT x)) :
    ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
      (hT : IsAffine T) (hT' : IsAffine T')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g),
      equivalenceFn f E e T' (h ≫ g) hT' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) g h x) =
      coherentEdgeRho g h E (equivalenceFn f E e T g hT x) := by
  unfold equivalenceFn
  exact e_natural

attribute [local irreducible] equivalenceFn

private theorem family_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (E : S.Modules) [E.IsQuasicoherent]
    (e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g ≃ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E))
    (e_natural : ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
      (hT : IsAffine T) (hT' : IsAffine T')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g),
      e T' (h ≫ g) hT' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) g h x) =
      coherentEdgeRho g h E (e T g hT x)) (V : S.Etale) [hV : IsAffine V.left]
    (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
      (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)) :
    unitAffineComparisonFamily f E e e_natural V x =
      chartSectionsEquiv V E (equivalenceFn f E e V.left V.hom hV (symmetryFn f V.hom x)) := by
  unfold unitAffineComparisonFamily unitAffineComparison chartSectionsEquiv
    sectionsEvaluation unitAffineSectionsEquiv symmetryFn equivalenceFn
  exact congrArg (fun y ↦ e V.left V.hom hV y)
    (Iso.addCommGroupIsoToAddEquiv_apply (unitAffineSymmetry f V.hom) x)

private theorem raw_linear_chart_square {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (E : S.Modules) [E.IsQuasicoherent]
    (e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g ≃ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E))
    (e_natural : ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
      (hT : IsAffine T) (hT' : IsAffine T')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g),
      e T' (h ≫ g) hT' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) g h x) =
      coherentEdgeRho g h E (e T g hT x)) :
      (∀ (V V' : S.Etale) [hV : IsAffine V.left] [hV' : IsAffine V'.left]
        (h : V' ⟶ V)
        (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
          (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)),
        equivalenceFn f E e V'.left V'.hom hV' ((symmetryFn f V'.hom)
          (affineFn f (SheafOfModules.unit X.ringCatSheaf) 1 h x)) =
        Scheme.Modules.Hom.app
          (eqToHom (congrArg (fun k ↦ (tensorPullback k).obj E) h.w)) ⊤
          (((tensorSectionsComp h.left V.hom).hom.app E).app ⊤
            (tensorSectionsUnit h.left ((tensorPullback V.hom).obj E)
              (equivalenceFn f E e V.left V.hom hV ((symmetryFn f V.hom) x))))) := by
  intro V V' hV hV' h x
  rcases V with ⟨⟨T, p, g⟩, hg⟩
  rcases V' with ⟨⟨T', p', g'⟩, hg'⟩
  rcases h with ⟨⟨l, r, w⟩, hl, hr⟩
  change T' ⟶ T at l
  change p' ⟶ p at r
  have w' : l ≫ g = g' := by simpa using w
  subst g'
  let V : S.Etale := ⟨⟨T, p, g⟩, hg⟩
  let V' : S.Etale := ⟨⟨T', p', l ≫ g⟩, hg'⟩
  let h : V' ⟶ V := ⟨⟨l, r, w⟩, hl, hr⟩
  exact raw_chart_comparison_square f E (equivalenceFn f E e)
    (equivalenceFn_natural f E e e_natural) V V' h x

private theorem comparison_chart_square {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (E : S.Modules) [E.IsQuasicoherent]
    (e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g ≃ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E))
    (e_natural : ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
      (hT : IsAffine T) (hT' : IsAffine T')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g),
      e T' (h ≫ g) hT' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) g h x) =
      coherentEdgeRho g h E (e T g hT x)) (V V' : S.Etale)
    [hV : IsAffine V.left] [hV' : IsAffine V'.left] (h : V' ⟶ V)
    (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
      (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)) :
    chartSectionsEquiv V' E
        (equivalenceFn f E e V'.left V'.hom hV' (symmetryFn f V'.hom
          (affineFn f (SheafOfModules.unit X.ringCatSheaf) 1 h x))) =
      etaleTensorSectionsRestriction E h
        (chartSectionsEquiv V E (equivalenceFn f E e V.left V.hom hV (symmetryFn f V.hom x))) := by
  have hs := raw_linear_chart_square f E e e_natural V V' h x
  exact (congrArg (chartSectionsEquiv V' E) hs).trans (chart_restriction E h _).symm

/-- The restriction square for the explicit factor-order cohomology isomorphism.
Source: Stacks, Cohomology, Tags 01F8, 01FB and 0ATM; Sheaves, Tags 0096 and 0097.
(blueprint: new-unit-affine-comparison-canonical-naturality).

Proof: identify the section-normalized tensor adjunction with the chosen adjunction
using uniqueness of its section unit. The conjugate-unit equation identifies its
composition isomorphism with tensorSectionsComp. Apply the same unit equation to
the adjoint structural-unit maps to show their compatibility with composition.
Normalize each restriction map by these structural-unit maps. Source and target
naturality of moduleCohomologyFMap identify it with structural-unit cohomology pullback.
The two projections identify the composite of base change with pullback symmetry
with the opposite-order composite. Contravariant cohomology functoriality therefore
commutes the normalized restriction with unitAffineSymmetry. Apply e_natural and
identify coherentEdgeRho with the tensor-section restriction using the composition
identity. Equality elimination along h.w accounts for the coefficient transport.
This calculation applies to identity arrows, empty schemes and zero modules. -/
theorem unitAffineComparison_canonical_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (E : S.Modules) [E.IsQuasicoherent]
    (e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g ≃ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          ((tensorPullback g).obj E))
    (e_natural : ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
      (hT : IsAffine T) (hT' : IsAffine T')
      (x : coherentEdgeH f (SheafOfModules.unit X.ringCatSheaf) g),
      e T' (h ≫ g) hT' (coherentEdgePullback f
        (SheafOfModules.unit X.ringCatSheaf) g h x) =
      coherentEdgeRho g h E (e T g hT x)) :
      (∀ (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left] (h : V' ⟶ V)
        (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace 1).obj
          (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)),
        unitAffineComparisonFamily f E e e_natural V'
          (affineRealizationRestriction f (SheafOfModules.unit X.ringCatSheaf) 1 h x) =
          etaleTensorSectionsRestriction E h
            (unitAffineComparisonFamily f E e e_natural V x)) := by
  intro V V' hV hV' h x
  have hs := comparison_chart_square f E e e_natural V V' h x
  unfold affineFn at hs
  have hl := family_apply f E e e_natural V'
    (affineRealizationRestriction f (SheafOfModules.unit X.ringCatSheaf) 1 h x)
  have hr := congrArg (etaleTensorSectionsRestriction E h)
    (family_apply f E e e_natural V x)
  exact hl.trans (hs.trans hr.symm)


end

attribute [instance] CategoryTheory.catToReflQuiver
end
end AlgebraicGeometry.Scheme.Modules
