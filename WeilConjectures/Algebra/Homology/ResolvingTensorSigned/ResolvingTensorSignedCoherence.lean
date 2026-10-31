/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
public import WeilConjectures.Algebra.Homology.DerivedTensorConstraints.DerivedTensorAdditiveConstraints
public import WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import all WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
import all WeilConjectures.Algebra.Homology.DerivedTensorConstraints.DerivedTensorAdditiveConstraints
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Transport and signed coherence of a normalized resolving tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 06YU and 0FPT;
more-algebra.tex, section-sign-rules, item-shift-tensor and item-flip-tensor-product.
(blueprint: lem-pur-resolving-tensor-signed-coherence).

All tensors and representative comparisons are the published K-flat constructions.
The sole construction below conjugates the specified natural isomorphism by eta.
In the shift equation the first shift is extracted before the second: the second
shift therefore uses the original first-factor degree, as in the source node.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor
open SheafOfModules.PullbackTensorCanonical

namespace SheafOfModules.ResolvingTensorSigned

attribute [local irreducible] SheafOfModules.monoidalCategory
  siteDerivedTensorIndependentCoefficients representativeIso
  CategoryTheory.Functor.mapDerivedCategory
  PullbackTensorCanonical.IsNormalized HasCanonicalTensorShifts
  DerivedTensorConstraints.IsNormalized

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
  (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
  (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Conjugation of the given normalized canonical tensor comparison by eta.
The components are eta inverse, followed by muL, followed by eta tensor eta.
This is a composite of actual natural isomorphisms, with no new tensor choice.
Source: Stacks 07A4, transport of the representative comparison
(blueprint: lem-pur-resolving-tensor-signed-coherence). -/
def transportedComparison
    (muL : Phi L ≅ Psi L) (eta : L ≅ f.L.mapDerivedCategory) :
    Phi f.L.mapDerivedCategory ≅ Psi f.L.mapDerivedCategory :=
  isoWhiskerLeft (Functor.uncurry.obj (canonicalDerivedTensor R)) eta.symm ≪≫
    muL ≪≫ isoWhiskerRight (NatIso.prod eta eta)
      (Functor.uncurry.obj (canonicalDerivedTensor S))

attribute [local irreducible] transportedComparison

section

open CategoryTheory.MonoidalCategory
attribute [local instance 4000] SheafOfModules.monoidalCategory
  HomologicalComplex.monoidalCategoryStruct HomologicalComplex.monoidalCategory

private theorem conjugate_square
    {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) (eta : F ≅ G) (T : B × B ⥤ B)
    {X Y Z W : A} {X' Y' Z' : B} (r : Z ⟶ W)
    (m : F.obj W ⟶ T.obj (F.obj X, F.obj Y))
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (kX : G.obj X ⟶ X') (kY : G.obj Y ⟶ Y') (kZ : G.obj Z ⟶ Z')
    (c : Z' ⟶ T.obj (X', Y'))
    (hm : F.map r ≫ m ≫ T.map (Prod.mkHom eX eY) = eZ ≫ c)
    (hX : eta.hom.app X ≫ kX = eX) (hY : eta.hom.app Y ≫ kY = eY)
    (hZ : eta.hom.app Z ≫ kZ = eZ) :
    G.map r ≫ (eta.inv.app W ≫ m ≫
      T.map (Prod.mkHom (eta.hom.app X) (eta.hom.app Y))) ≫
      T.map (Prod.mkHom kX kY) = kZ ≫ c := by
  have he : Prod.mkHom (eta.hom.app X) (eta.hom.app Y) ≫
      Prod.mkHom kX kY = Prod.mkHom eX eY := by
    apply Prod.ext
    · exact hX
    · exact hY
  have hnat := eta.inv.naturality r
  simp only [Category.assoc]
  rw [← T.map_comp, he, reassoc_of% hnat, hm, ← hZ]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]


private theorem simultaneousShift
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasShift A ℤ] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
    (T : A ⥤ A ⥤ A) (V : B ⥤ B ⥤ B) (F : A ⥤ B)
    [T.CommShift₂Int] [V.CommShift₂Int] [F.CommShift ℤ]
    (m : Functor.uncurry.obj T ⋙ F ⟶ (F.prod F) ⋙ Functor.uncurry.obj V)
    (hr : ∀ (n : ℤ) (X Y : A), m.app (X⟦n⟧, Y) ≫
      (V.map ((F.commShiftIso n).hom.app X)).app (F.obj Y) ≫
      ((V.flip.obj (F.obj Y)).commShiftIso n).hom.app (F.obj X) =
      F.map (((T.flip.obj Y).commShiftIso n).hom.app X) ≫
      (F.commShiftIso n).hom.app ((T.obj X).obj Y) ≫ (m.app (X, Y))⟦n⟧')
    (hl : ∀ (n : ℤ) (X Y : A), m.app (X, Y⟦n⟧) ≫
      (V.obj (F.obj X)).map ((F.commShiftIso n).hom.app Y) ≫
      ((V.obj (F.obj X)).commShiftIso n).hom.app (F.obj Y) =
      F.map (((T.obj X).commShiftIso n).hom.app Y) ≫
      (F.commShiftIso n).hom.app ((T.obj X).obj Y) ≫ (m.app (X, Y))⟦n⟧')
    (a b : ℤ) (X Y : A) :
    m.app (X⟦a⟧, Y⟦b⟧) ≫ (Functor.uncurry.obj V).map
        (Prod.mkHom ((F.commShiftIso a).hom.app X) ((F.commShiftIso b).hom.app Y)) ≫
      ((V.flip.obj ((F.obj Y)⟦b⟧)).commShiftIso a).hom.app (F.obj X) ≫
      (shiftFunctor _ a).map (((V.obj (F.obj X)).commShiftIso b).hom.app (F.obj Y)) ≫
      (shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.app ((V.obj (F.obj X)).obj (F.obj Y)) =
    F.map ((((T.flip.obj (Y⟦b⟧)).commShiftIso a).hom.app X) ≫
      (shiftFunctor _ a).map (((T.obj X).commShiftIso b).hom.app Y) ≫
      (shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.app ((T.obj X).obj Y)) ≫
      (F.commShiftIso (a + b)).hom.app ((T.obj X).obj Y) ≫ (m.app (X, Y))⟦a + b⟧' := by
  have hx := (NatTrans.shift_app_comm
    (V.flip.map ((F.commShiftIso b).hom.app Y)) a (F.obj X)).symm
  change (V.obj ((F.obj X)⟦a⟧)).map ((F.commShiftIso b).hom.app Y) ≫
      ((V.flip.obj ((F.obj Y)⟦b⟧)).commShiftIso a).hom.app (F.obj X) =
    ((V.flip.obj (F.obj (Y⟦b⟧))).commShiftIso a).hom.app (F.obj X) ≫
      (shiftFunctor _ a).map ((V.obj (F.obj X)).map
        ((F.commShiftIso b).hom.app Y)) at hx
  have hnat := (F.commShiftIso a).hom.naturality (((T.obj X).commShiftIso b).hom.app Y)
  dsimp only [Functor.comp_map] at hnat
  have hadd := NatTrans.congr_app
    (congrArg Iso.hom (F.commShiftIso_add' (add_comm b a))) ((T.obj X).obj Y)
  simp only [Functor.CommShift.isoAdd'_hom_app] at hadd
  have hsum : (F.commShiftIso a).hom.app (((T.obj X).obj Y)⟦b⟧) ≫
      ((F.commShiftIso b).hom.app ((T.obj X).obj Y))⟦a⟧' ≫
      (shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.app (F.obj ((T.obj X).obj Y)) =
    F.map ((shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.app ((T.obj X).obj Y)) ≫
      (F.commShiftIso (a + b)).hom.app ((T.obj X).obj Y) := by
    rw [hadd]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  have hmadd := (shiftFunctorAdd' B b a (a + b) (add_comm b a)).inv.naturality (m.app (X, Y))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj] at hmadd
  rw [Functor.uncurry_obj_map]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  simp only [Category.assoc]
  rw [reassoc_of% hx, reassoc_of% (hr a X (Y⟦b⟧))]
  rw [← (shiftFunctor _ a).map_comp_assoc, ← (shiftFunctor _ a).map_comp_assoc]
  simp only [Category.assoc]
  rw [hl]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hnat, hmadd, reassoc_of% hsum]

private def tensorBridge (T : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{wR} (Modules T)] :
    Functor.uncurry.obj (canonicalDerivedTensor T) ≅ DerivedTensorConstraints.tensor T := by
  unfold canonicalDerivedTensor derivedTensor
  exact Functor.currying.counitIso.app _

private theorem tensorBridge_hom (T : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{wR} (Modules T)]
    (Z : DerivedCategory (Modules T) × DerivedCategory (Modules T)) :
    (tensorBridge T).hom.app Z = 𝟙 _ := by cases Z; rfl

private theorem tensorBridge_inv (T : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{wR} (Modules T)]
    (Z : DerivedCategory (Modules T) × DerivedCategory (Modules T)) :
    (tensorBridge T).inv.app Z = 𝟙 _ := by cases Z; rfl


set_option maxHeartbeats 1600000 in
-- Comparing the two tensor presentations needs additional elaboration heartbeats.
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
private theorem normalized_symmetry
    (k : Comparison.{r, uC, vC, uD, vD} f)
    (m : Phi f.L.mapDerivedCategory ⟶ Psi f.L.mapDerivedCategory)
    (hn : PullbackTensorCanonical.IsNormalized f k f.L.mapDerivedCategory
      f.L.mapDerivedCategoryFactors.hom m)
    (alphaR : DerivedTensorConstraints.leftAssociated R ≅
      DerivedTensorConstraints.rightAssociated R)
    (sigmaR : DerivedTensorConstraints.tensor R ≅ DerivedTensorConstraints.swapped R)
    (hconstraintsR : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource R a b ≅
        DerivedTensorConstraints.shiftedTarget R a b,
      DerivedTensorConstraints.IsNormalized R t alphaR sigmaR)
    (alphaS : DerivedTensorConstraints.leftAssociated S ≅
      DerivedTensorConstraints.rightAssociated S)
    (sigmaS : DerivedTensorConstraints.tensor S ≅ DerivedTensorConstraints.swapped S)
    (hconstraintsS : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource S a b ≅
        DerivedTensorConstraints.shiftedTarget S a b,
      DerivedTensorConstraints.IsNormalized S t alphaS sigmaS) :
    ∀ A B : DerivedCategory (Modules R),
      f.L.mapDerivedCategory.map (sigmaR.hom.app (A, B)) ≫ m.app (B, A) =
        m.app (A, B) ≫ sigmaS.hom.app
          (f.L.mapDerivedCategory.obj A, f.L.mapDerivedCategory.obj B) := by
  let U := f.L.mapDerivedCategory
  have tensor_map {X Y : DerivedCategory (Modules S) × DerivedCategory (Modules S)}
      (g : X ⟶ Y) : (Functor.uncurry.obj (canonicalDerivedTensor S)).map g =
        (DerivedTensorConstraints.tensor S).map g := by
    have h := (tensorBridge S).hom.naturality g
    simpa only [tensorBridge_hom, Category.id_comp, Category.comp_id] using h
  let sr := tensorBridge R ≪≫ sigmaR ≪≫
    isoWhiskerLeft (CategoryTheory.Prod.swap _ _) (tensorBridge R).symm
  let ss := tensorBridge S ≪≫ sigmaS ≪≫
    isoWhiskerLeft (CategoryTheory.Prod.swap _ _) (tensorBridge S).symm
  have sr_app (X Y : DerivedCategory (Modules R)) :
      sr.hom.app (X, Y) = sigmaR.hom.app (X, Y) := by
    simp only [sr, Iso.trans_hom, NatTrans.comp_app, tensorBridge_hom,
      isoWhiskerLeft_hom, whiskerLeft_app, Iso.symm_hom, tensorBridge_inv,
      Category.id_comp, CategoryTheory.Prod.swap_obj]
    exact Category.comp_id _
  have ss_app (X Y : DerivedCategory (Modules S)) :
      ss.hom.app (X, Y) = sigmaS.hom.app (X, Y) := by
    simp only [ss, Iso.trans_hom, NatTrans.comp_app, tensorBridge_hom,
      isoWhiskerLeft_hom, whiskerLeft_app, Iso.symm_hom, tensorBridge_inv,
      Category.id_comp, CategoryTheory.Prod.swap_obj]
    exact Category.comp_id _
  let a : Phi U ⟶ CategoryTheory.Prod.swap _ _ ⋙ Psi U :=
    Functor.whiskerRight sr.hom U ≫
      Functor.whiskerLeft (CategoryTheory.Prod.swap _ _) m
  let b : Phi U ⟶ CategoryTheory.Prod.swap _ _ ⋙ Psi U :=
    m ≫ Functor.whiskerLeft (U.prod U) ss.hom
  have hab : a = b := by
    have hff := resolving_fullyFaithful (R := R) (S := S)
    let ff := Classical.choice hff
    apply ff.map_injective
    apply NatTrans.ext
    funext Z
    obtain ⟨⟨P, hp, hf⟩, ⟨Q, hq, hg⟩⟩ := Z
    change a.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      b.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
    dsimp only [a, b, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      CategoryTheory.Prod.swap_obj, Functor.prod_obj]
    rw [sr_app, ss_app]
    change U.map (sigmaR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        m.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
      m.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        sigmaS.hom.app (U.obj (DerivedCategory.Q.obj P), U.obj (DerivedCategory.Q.obj Q))
    unfold PullbackTensorCanonical.IsNormalized at hn
    obtain ⟨hp', hq', hf', hg', hm⟩ := hn P Q hp hq hf hg
    obtain ⟨_, _, _, _, hm'⟩ := hn Q P hq hp hg hf
    simp only [tensor_map] at hm hm'
    let p : DerivedTensorConstraints.Model R := ⟨P, hp, hf⟩
    let q : DerivedTensorConstraints.Model R := ⟨Q, hq, hg⟩
    let p' : DerivedTensorConstraints.Model S := ⟨(pull f).obj P, hp', hf'⟩
    let q' : DerivedTensorConstraints.Model S := ⟨(pull f).obj Q, hq', hg'⟩
    obtain ⟨tR, hnR⟩ := hconstraintsR
    obtain ⟨tS, hnS⟩ := hconstraintsS
    unfold DerivedTensorConstraints.IsNormalized at hnR hnS
    have hsR := hnR.2.2 p q
    have hsS := hnS.2.2 p' q'
    have hr : (canonicalRepresentativeIso R P Q hp hq hf hg).hom ≫
        sigmaR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map (CochainComplex.Monoidal.braiding P Q).hom ≫
        (canonicalRepresentativeIso R Q P hq hp hg hf).hom := by
      have h := congrArg (fun z ↦ (DerivedTensorConstraints.representative R p q).hom ≫ z)
        (congrArg Iso.hom hsR)
      simpa only [Iso.app_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Category.assoc, Iso.hom_inv_id_assoc, DerivedTensorConstraints.representative,
        canonicalRepresentativeIso, p, q] using h
    have hs : (canonicalRepresentativeIso S ((pull f).obj P) ((pull f).obj Q)
        hp' hq' hf' hg').hom ≫
        sigmaS.hom.app (DerivedCategory.Q.obj ((pull f).obj P),
          DerivedCategory.Q.obj ((pull f).obj Q)) =
      DerivedCategory.Q.map (CochainComplex.Monoidal.braiding
        ((pull f).obj P) ((pull f).obj Q)).hom ≫
        (canonicalRepresentativeIso S ((pull f).obj Q) ((pull f).obj P)
          hq' hp' hg' hf').hom := by
      have h := congrArg (fun z ↦ (DerivedTensorConstraints.representative S p' q').hom ≫ z)
        (congrArg Iso.hom hsS)
      simpa only [Iso.app_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Category.assoc, Iso.hom_inv_id_assoc, DerivedTensorConstraints.representative,
        canonicalRepresentativeIso, p', q'] using h
    let t := (DerivedTensorConstraints.tensor S).map
      (Prod.mkHom (f.L.mapDerivedCategoryFactors.hom.app Q)
        (f.L.mapDerivedCategoryFactors.hom.app P))
    have : IsIso t := by
      change IsIso (((DerivedTensorConstraints.tensor S).mapIso
        (Iso.prod (f.L.mapDerivedCategoryFactors.app Q)
          (f.L.mapDerivedCategoryFactors.app P))).hom)
      infer_instance
    apply (cancel_epi (U.map (canonicalRepresentativeIso R P Q hp hq hf hg).hom)).1
    apply (cancel_mono t).1
    have hk := f.L.mapDerivedCategoryFactors.hom.naturality
      (CochainComplex.Monoidal.braiding P Q).hom
    have hc := (cochainComparison_monoidal f k).2.2.1 P Q
    have hnat := sigmaS.hom.naturality
      (Prod.mkHom (f.L.mapDerivedCategoryFactors.hom.app P)
        (f.L.mapDerivedCategoryFactors.hom.app Q))
    dsimp only [Functor.comp_map] at hk hnat
    simp only [t, Category.assoc]
    erw [← hnat]
    rw [← U.map_comp_assoc, hr, U.map_comp]
    simp only [Category.assoc]
    erw [hm', reassoc_of% hk]
    rw [← DerivedCategory.Q.map_comp_assoc, hc, DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rw [← hs]
    erw [← reassoc_of% hm]
    rfl
  intro A B
  simpa only [a, b, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    CategoryTheory.Prod.swap_obj, Functor.prod_obj, sr_app, ss_app] using
    NatTrans.congr_app hab (A, B)


private theorem nestedComparison_left
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ⟶ (F.prod F) ⋙ V)
    {X Y Z N H : A} {X' Y' Z' N' H' : B}
    (i : N ⟶ T.obj (X, Y)) (j : H ⟶ T.obj (N, Z))
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eN : F.obj N ⟶ N') (eH : F.obj H ⟶ H')
    (i' : N' ⟶ V.obj (X', Y')) (j' : H' ⟶ V.obj (N', Z'))
    (hi : F.map i ≫ m.app (X, Y) ≫ V.map (Prod.mkHom eX eY) = eN ≫ i')
    (hj : F.map j ≫ m.app (N, Z) ≫ V.map (Prod.mkHom eN eZ) = eH ≫ j') :
    F.map (j ≫ T.map (Prod.mkHom i (𝟙 Z))) ≫ m.app (T.obj (X, Y), Z) ≫
        V.map (Prod.mkHom (m.app (X, Y)) (𝟙 (F.obj Z))) ≫
        V.map (Prod.mkHom (V.map (Prod.mkHom eX eY)) eZ) =
      eH ≫ j' ≫ V.map (Prod.mkHom i' (𝟙 Z')) := by
  have hn := m.naturality (Prod.mkHom i (𝟙 Z))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [F.map_id] at hn
  calc
    _ = F.map j ≫ m.app (N, Z) ≫ V.map
        (Prod.mkHom (F.map i ≫ m.app (X, Y) ≫ V.map (Prod.mkHom eX eY)) eZ) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom,
        Category.id_comp]
    _ = F.map j ≫ m.app (N, Z) ≫ V.map (Prod.mkHom (eN ≫ i') eZ) := by rw [hi]
    _ = (F.map j ≫ m.app (N, Z) ≫ V.map (Prod.mkHom eN eZ)) ≫
        V.map (Prod.mkHom i' (𝟙 Z')) := by
      simp only [Category.assoc, ← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom,
        Category.comp_id]
    _ = _ := by rw [hj]; simp only [Category.assoc]

private theorem nestedComparison_right
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ⟶ (F.prod F) ⋙ V)
    {X Y Z N H : A} {X' Y' Z' N' H' : B}
    (i : N ⟶ T.obj (Y, Z)) (j : H ⟶ T.obj (X, N))
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eN : F.obj N ⟶ N') (eH : F.obj H ⟶ H')
    (i' : N' ⟶ V.obj (Y', Z')) (j' : H' ⟶ V.obj (X', N'))
    (hi : F.map i ≫ m.app (Y, Z) ≫ V.map (Prod.mkHom eY eZ) = eN ≫ i')
    (hj : F.map j ≫ m.app (X, N) ≫ V.map (Prod.mkHom eX eN) = eH ≫ j') :
    F.map (j ≫ T.map (Prod.mkHom (𝟙 X) i)) ≫ m.app (X, T.obj (Y, Z)) ≫
        V.map (Prod.mkHom (𝟙 (F.obj X)) (m.app (Y, Z))) ≫
        V.map (Prod.mkHom eX (V.map (Prod.mkHom eY eZ))) =
      eH ≫ j' ≫ V.map (Prod.mkHom (𝟙 X') i') := by
  have hn := m.naturality (Prod.mkHom (𝟙 X) i)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [F.map_id] at hn
  calc
    _ = F.map j ≫ m.app (X, N) ≫ V.map
        (Prod.mkHom eX (F.map i ≫ m.app (Y, Z) ≫ V.map (Prod.mkHom eY eZ))) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom,
        Category.id_comp]
    _ = F.map j ≫ m.app (X, N) ≫ V.map (Prod.mkHom eX (eN ≫ i')) := by rw [hi]
    _ = (F.map j ≫ m.app (X, N) ≫ V.map (Prod.mkHom eX eN)) ≫
        V.map (Prod.mkHom (𝟙 X') i') := by
      simp only [Category.assoc, ← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom,
        Category.comp_id]
    _ = _ := by rw [hj]; simp only [Category.assoc]

private def comparisonLeft
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ≅ (F.prod F) ⋙ V) :
    ((T.prod (𝟭 A)) ⋙ T) ⋙ F ≅
      ((F.prod F).prod F) ⋙ (V.prod (𝟭 B)) ⋙ V :=
  isoWhiskerLeft (T.prod (𝟭 A)) m ≪≫
    isoWhiskerRight (NatIso.prod m (Iso.refl F)) V

private def comparisonRight
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ≅ (F.prod F) ⋙ V) :
    (CategoryTheory.prod.associator A A A ⋙ ((𝟭 A).prod T) ⋙ T) ⋙ F ≅
      ((F.prod F).prod F) ⋙ CategoryTheory.prod.associator B B B ⋙
        ((𝟭 B).prod V) ⋙ V :=
  isoWhiskerLeft (CategoryTheory.prod.associator A A A)
    (isoWhiskerLeft ((𝟭 A).prod T) m ≪≫
      isoWhiskerRight (NatIso.prod (Iso.refl F) m) V)

private theorem associativity_from_representatives
    {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ A) (V : B × B ⥤ B) (F : A ⥤ B)
    (m : T ⋙ F ≅ (F.prod F) ⋙ V)
    (alpha : (T.prod (𝟭 A)) ⋙ T ≅
      CategoryTheory.prod.associator A A A ⋙ ((𝟭 A).prod T) ⋙ T)
    (beta : (V.prod (𝟭 B)) ⋙ V ≅
      CategoryTheory.prod.associator B B B ⋙ ((𝟭 B).prod V) ⋙ V)
    {X Y Z W H : A} {X' Y' Z' W' H' : B}
    (l : W ≅ T.obj (T.obj (X, Y), Z)) (r : H ≅ T.obj (X, T.obj (Y, Z)))
    (a : W ⟶ H)
    (l' : W' ⟶ V.obj (V.obj (X', Y'), Z'))
    (r' : H' ⟶ V.obj (X', V.obj (Y', Z'))) (a' : W' ⟶ H')
    (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y') (eZ : F.obj Z ≅ Z')
    (eW : F.obj W ⟶ W') (eH : F.obj H ⟶ H')
    (hB : l.hom ≫ alpha.hom.app ((X, Y), Z) = a ≫ r.hom)
    (hA : l' ≫ beta.hom.app ((X', Y'), Z') = a' ≫ r')
    (hL : F.map l.hom ≫ (comparisonLeft T V F m).hom.app ((X, Y), Z) ≫
      V.map (Prod.mkHom (V.map (Prod.mkHom eX.hom eY.hom)) eZ.hom) = eW ≫ l')
    (hR : F.map r.hom ≫ (comparisonRight T V F m).hom.app ((X, Y), Z) ≫
      V.map (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))) = eH ≫ r')
    (hC : F.map a ≫ eH = eW ≫ a') :
    F.map (alpha.hom.app ((X, Y), Z)) ≫ (comparisonRight T V F m).hom.app ((X, Y), Z) =
      (comparisonLeft T V F m).hom.app ((X, Y), Z) ≫
        beta.hom.app ((F.obj X, F.obj Y), F.obj Z) := by
  have : IsIso (Prod.mkHom eY.hom eZ.hom) :=
    (inferInstance : IsIso (Iso.prod eY eZ).hom)
  have : IsIso (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))) :=
    (inferInstance : IsIso (Iso.prod eX (V.mapIso (Iso.prod eY eZ))).hom)
  apply (cancel_epi (F.map l.hom)).1
  apply (cancel_mono (V.map
    (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))))).1
  have hnat := beta.hom.naturality
    (Prod.mkHom (Prod.mkHom eX.hom eY.hom) eZ.hom)
  change V.map (Prod.mkHom (V.map (Prod.mkHom eX.hom eY.hom)) eZ.hom) ≫
      beta.hom.app ((X', Y'), Z') = beta.hom.app ((F.obj X, F.obj Y), F.obj Z) ≫
      V.map (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))) at hnat
  calc
    _ = F.map a ≫ F.map r.hom ≫ (comparisonRight T V F m).hom.app ((X, Y), Z) ≫
        V.map (Prod.mkHom eX.hom (V.map (Prod.mkHom eY.hom eZ.hom))) := by
      rw [← F.map_comp_assoc, hB, F.map_comp]
      simp only [Category.assoc]
    _ = F.map a ≫ eH ≫ r' := by rw [hR]
    _ = eW ≫ a' ≫ r' := by rw [reassoc_of% hC]
    _ = eW ≫ l' ≫ beta.hom.app ((X', Y'), Z') := by rw [hA]
    _ = F.map l.hom ≫ (comparisonLeft T V F m).hom.app ((X, Y), Z) ≫
        V.map (Prod.mkHom (V.map (Prod.mkHom eX.hom eY.hom)) eZ.hom) ≫
        beta.hom.app ((X', Y'), Z') := by rw [reassoc_of% hL]
    _ = _ := by rw [hnat]; simp only [Category.assoc]


set_option maxHeartbeats 1600000 in
-- Comparing the two tensor presentations needs additional elaboration heartbeats.
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
private theorem normalized_associativity_model
    (k : Comparison.{r, uC, vC, uD, vD} f)
    (mu : Phi f.L.mapDerivedCategory ≅ Psi f.L.mapDerivedCategory)
    (hn : PullbackTensorCanonical.IsNormalized f k f.L.mapDerivedCategory
      f.L.mapDerivedCategoryFactors.hom mu.hom)
    (alphaR : DerivedTensorConstraints.leftAssociated R ≅
      DerivedTensorConstraints.rightAssociated R)
    (sigmaR : DerivedTensorConstraints.tensor R ≅ DerivedTensorConstraints.swapped R)
    (hconstraintsR : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource R a b ≅
        DerivedTensorConstraints.shiftedTarget R a b,
      DerivedTensorConstraints.IsNormalized R t alphaR sigmaR)
    (alphaS : DerivedTensorConstraints.leftAssociated S ≅
      DerivedTensorConstraints.rightAssociated S)
    (sigmaS : DerivedTensorConstraints.tensor S ≅ DerivedTensorConstraints.swapped S)
    (hconstraintsS : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource S a b ≅
        DerivedTensorConstraints.shiftedTarget S a b,
      DerivedTensorConstraints.IsNormalized S t alphaS sigmaS)
    (hresolving : ∀ p : DerivedTensorConstraints.Model R,
      DerivedTensorConstraints.resolvingComplex S ((pull f).obj p.obj))
    (p q n : DerivedTensorConstraints.Model R) :
    f.L.mapDerivedCategory.map (alphaR.hom.app
        ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
          DerivedCategory.Q.obj n.obj)) ≫
      mu.hom.app (DerivedCategory.Q.obj p.obj,
        ((derivedTensor R).obj (DerivedCategory.Q.obj q.obj)).obj
          (DerivedCategory.Q.obj n.obj)) ≫
      (Functor.uncurry.obj (derivedTensor S)).map
        (Prod.mkHom (𝟙 _) (mu.hom.app (DerivedCategory.Q.obj q.obj,
          DerivedCategory.Q.obj n.obj))) =
    mu.hom.app (((derivedTensor R).obj (DerivedCategory.Q.obj p.obj)).obj
        (DerivedCategory.Q.obj q.obj), DerivedCategory.Q.obj n.obj) ≫
      (Functor.uncurry.obj (derivedTensor S)).map
        (Prod.mkHom (mu.hom.app (DerivedCategory.Q.obj p.obj,
          DerivedCategory.Q.obj q.obj)) (𝟙 _)) ≫
      alphaS.hom.app ((f.L.mapDerivedCategory.obj (DerivedCategory.Q.obj p.obj),
        f.L.mapDerivedCategory.obj (DerivedCategory.Q.obj q.obj)),
        f.L.mapDerivedCategory.obj (DerivedCategory.Q.obj n.obj)) := by
  let U := f.L.mapDerivedCategory
  let T := DerivedTensorConstraints.tensor R
  let V := DerivedTensorConstraints.tensor S
  let m : T ⋙ U ≅ (U.prod U) ⋙ V :=
    isoWhiskerRight (tensorBridge R).symm U ≪≫ mu ≪≫
      isoWhiskerLeft (U.prod U) (tensorBridge S)
  have m_app (X Y : DerivedCategory (Modules R)) :
      m.hom.app (X, Y) = mu.hom.app (X, Y) := by
    dsimp only [m, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      whiskerRight_app, Iso.symm_hom, isoWhiskerLeft_hom, whiskerLeft_app,
      Functor.prod_obj]
    rw [tensorBridge_inv, tensorBridge_hom]
    rw [U.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _)
  have tensor_map {X Y : DerivedCategory (Modules S) × DerivedCategory (Modules S)}
      (g : X ⟶ Y) : (Functor.uncurry.obj (canonicalDerivedTensor S)).map g = V.map g := by
    have h := (tensorBridge S).hom.naturality g
    simpa only [tensorBridge_hom, Category.id_comp, Category.comp_id] using h
  let pm : DerivedTensorConstraints.Model R → DerivedTensorConstraints.Model S :=
    fun E ↦ ⟨(pull f).obj E.obj, hresolving E⟩
  let pq := DerivedTensorConstraints.totalModel R p q
  let qn := DerivedTensorConstraints.totalModel R q n
  let pp := pm p
  let qq := pm q
  let nn := pm n
  let apq := DerivedTensorConstraints.totalModel S pp qq
  let aqn := DerivedTensorConstraints.totalModel S qq nn
  let bPQ := DerivedTensorConstraints.representative R p q
  let bQN := DerivedTensorConstraints.representative R q n
  let bL := DerivedTensorConstraints.representative R pq n
  let bR := DerivedTensorConstraints.representative R p qn
  let aPQ := DerivedTensorConstraints.representative S pp qq
  let aQN := DerivedTensorConstraints.representative S qq nn
  let aL := DerivedTensorConstraints.representative S apq nn
  let aR := DerivedTensorConstraints.representative S pp aqn
  let aL₀ := DerivedTensorConstraints.representative S (pm pq) nn
  let aR₀ := DerivedTensorConstraints.representative S pp (pm qn)
  let lB := DerivedTensorConstraints.leftRepresentative R p q n
  let rB := DerivedTensorConstraints.rightRepresentative R p q n
  let lA := DerivedTensorConstraints.leftRepresentative S pp qq nn
  let rA := DerivedTensorConstraints.rightRepresentative S pp qq nn
  let e := f.L.mapDerivedCategoryFactors
  let cPQ := (comparison f k p.obj q.obj).hom
  let cQN := (comparison f k q.obj n.obj).hom
  let cL := (comparison f k pq.obj n.obj).hom
  let cR := (comparison f k p.obj qn.obj).hom
  let eL := e.hom.app ((DerivedTensorConstraints.totalModel R pq n).obj) ≫
    DerivedCategory.Q.map cL ≫ DerivedCategory.Q.map (cPQ ⊗ₘ 𝟙 nn.obj)
  let eR := e.hom.app ((DerivedTensorConstraints.totalModel R p qn).obj) ≫
    DerivedCategory.Q.map cR ≫ DerivedCategory.Q.map (𝟙 pp.obj ⊗ₘ cQN)
  have hm (E F : DerivedTensorConstraints.Model R) :
      U.map (DerivedTensorConstraints.representative R E F).hom ≫
        m.hom.app (DerivedCategory.Q.obj E.obj, DerivedCategory.Q.obj F.obj) ≫
        V.map (Prod.mkHom (e.hom.app E.obj) (e.hom.app F.obj)) =
      e.hom.app ((DerivedTensorConstraints.totalModel R E F).obj) ≫
        DerivedCategory.Q.map (comparison f k E.obj F.obj).hom ≫
        (DerivedTensorConstraints.representative S (pm E) (pm F)).hom := by
    have h := hn
    unfold PullbackTensorCanonical.IsNormalized at h
    obtain ⟨_, _, _, _, h⟩ := h E.obj F.obj E.property.1 F.property.1
      E.property.2 F.property.2
    simp only [m_app, ← tensor_map]
    exact h
  obtain ⟨tR, hnR⟩ := hconstraintsR
  obtain ⟨tS, hnS⟩ := hconstraintsS
  unfold DerivedTensorConstraints.IsNormalized at hnR hnS
  have hB : lB.hom ≫ alphaR.hom.app
      ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
        DerivedCategory.Q.obj n.obj) =
      DerivedCategory.Q.map (α_ p.obj q.obj n.obj).hom ≫ rB.hom := by
    have h := congrArg (fun z ↦ lB.hom ≫ z) (congrArg Iso.hom (hnR.2.1 p q n))
    simpa only [lB, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, Iso.hom_inv_id_assoc] using h
  have hA : lA.hom ≫ alphaS.hom.app
      ((DerivedCategory.Q.obj pp.obj, DerivedCategory.Q.obj qq.obj),
        DerivedCategory.Q.obj nn.obj) =
      DerivedCategory.Q.map (α_ pp.obj qq.obj nn.obj).hom ≫ rA.hom := by
    have h := congrArg (fun z ↦ lA.hom ≫ z) (congrArg Iso.hom (hnS.2.1 pp qq nn))
    simpa only [lA, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, Iso.hom_inv_id_assoc] using h
  have hnL := (DerivedTensorConstraints.representativeNatIso S).hom.naturality
    (Prod.mkHom (ObjectProperty.homMk cPQ : pm pq ⟶ apq) (𝟙 nn))
  have hnR := (DerivedTensorConstraints.representativeNatIso S).hom.naturality
    (Prod.mkHom (𝟙 pp) (ObjectProperty.homMk cQN : pm qn ⟶ aqn))
  simp only [Functor.comp_map,
    DerivedTensorConstraints.representativeNatIso_hom_app, Functor.prod_map,
    DerivedTensorConstraints.modelLocalization, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.id_hom, ObjectProperty.homMk_hom] at hnL hnR
  erw [MonoidalCategory.tensor_map, DerivedCategory.Q.map_id] at hnL
  erw [MonoidalCategory.tensor_map, DerivedCategory.Q.map_id] at hnR
  change DerivedCategory.Q.map (cPQ ⊗ₘ 𝟙 nn.obj) ≫ aL.hom =
    aL₀.hom ≫ V.map (Prod.mkHom (DerivedCategory.Q.map cPQ) (𝟙 _)) at hnL
  change DerivedCategory.Q.map (𝟙 pp.obj ⊗ₘ cQN) ≫ aR.hom =
    aR₀.hom ≫ V.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map cQN)) at hnR
  have hL₀ := nestedComparison_left T V U m.hom bPQ.hom bL.hom
    (e.hom.app p.obj) (e.hom.app q.obj) (e.hom.app n.obj) (e.hom.app pq.obj)
    (e.hom.app ((DerivedTensorConstraints.totalModel R pq n).obj))
    (DerivedCategory.Q.map cPQ ≫ aPQ.hom) (DerivedCategory.Q.map cL ≫ aL₀.hom)
    (hm p q) (hm pq n)
  have hR₀ := nestedComparison_right T V U m.hom bQN.hom bR.hom
    (e.hom.app p.obj) (e.hom.app q.obj) (e.hom.app n.obj) (e.hom.app qn.obj)
    (e.hom.app ((DerivedTensorConstraints.totalModel R p qn).obj))
    (DerivedCategory.Q.map cQN ≫ aQN.hom) (DerivedCategory.Q.map cR ≫ aR₀.hom)
    (hm q n) (hm p qn)
  have hL : U.map lB.hom ≫ (comparisonLeft T V U m).hom.app
      ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
        DerivedCategory.Q.obj n.obj) ≫
      V.map (Prod.mkHom (V.map (Prod.mkHom (e.hom.app p.obj) (e.hom.app q.obj)))
        (e.hom.app n.obj)) = eL ≫ lA.hom := by
    simp only [comparisonLeft, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      NatIso.prod_hom, NatTrans.prod, Iso.refl_hom, NatTrans.id_app, Functor.prod_obj,
      Functor.id_obj, Functor.comp_obj, Category.assoc]
    calc
      _ = e.hom.app ((DerivedTensorConstraints.totalModel R pq n).obj) ≫
          (DerivedCategory.Q.map cL ≫ aL₀.hom) ≫
          V.map (Prod.mkHom (DerivedCategory.Q.map cPQ ≫ aPQ.hom) (𝟙 _)) := hL₀
      _ = _ := by
        rw [show V.map (Prod.mkHom (DerivedCategory.Q.map cPQ ≫ aPQ.hom) (𝟙 _)) =
          V.map (Prod.mkHom (DerivedCategory.Q.map cPQ) (𝟙 _)) ≫
            V.map (Prod.mkHom aPQ.hom (𝟙 _)) by
            simp only [← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom, Category.id_comp]]
        simp only [Category.assoc]
        rw [← reassoc_of% hnL]
        simp only [eL, lA, DerivedTensorConstraints.leftRepresentative,
          Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Category.assoc]
        rfl
  have hR : U.map rB.hom ≫ (comparisonRight T V U m).hom.app
      ((DerivedCategory.Q.obj p.obj, DerivedCategory.Q.obj q.obj),
        DerivedCategory.Q.obj n.obj) ≫
      V.map (Prod.mkHom (e.hom.app p.obj)
        (V.map (Prod.mkHom (e.hom.app q.obj) (e.hom.app n.obj)))) = eR ≫ rA.hom := by
    simp only [comparisonRight, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      NatIso.prod_hom, NatTrans.prod, Iso.refl_hom, NatTrans.id_app, Functor.prod_obj,
      Functor.id_obj, Functor.comp_obj, CategoryTheory.prod.associator,
      Functor.comp_obj, Category.assoc]
    calc
      _ = e.hom.app ((DerivedTensorConstraints.totalModel R p qn).obj) ≫
          (DerivedCategory.Q.map cR ≫ aR₀.hom) ≫
          V.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map cQN ≫ aQN.hom)) := hR₀
      _ = _ := by
        rw [show V.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map cQN ≫ aQN.hom)) =
          V.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map cQN)) ≫
            V.map (Prod.mkHom (𝟙 _) aQN.hom) by
            simp only [← V.map_comp, CategoryTheory.prod_comp, Prod.mkHom, Category.id_comp]]
        simp only [Category.assoc]
        rw [← reassoc_of% hnR]
        simp only [eR, rA, DerivedTensorConstraints.rightRepresentative,
          Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Category.assoc]
        rfl
  have hC : U.map (DerivedCategory.Q.map (α_ p.obj q.obj n.obj).hom) ≫ eR =
      eL ≫ DerivedCategory.Q.map (α_ pp.obj qq.obj nn.obj).hom := by
    have hf := e.hom.naturality (α_ p.obj q.obj n.obj).hom
    change U.map (DerivedCategory.Q.map (α_ p.obj q.obj n.obj).hom) ≫
      e.hom.app ((DerivedTensorConstraints.totalModel R p qn).obj) =
      e.hom.app ((DerivedTensorConstraints.totalModel R pq n).obj) ≫
        DerivedCategory.Q.map ((pull f).map (α_ p.obj q.obj n.obj).hom) at hf
    have hc := (cochainComparison_monoidal f k).2.1 p.obj q.obj n.obj
    dsimp only [eL, eR]
    rw [reassoc_of% hf]
    simpa only [Functor.map_comp, Category.assoc, cPQ, cQN, cL, cR,
      pp, qq, nn, pm, pq, qn, DerivedTensorConstraints.totalModel] using
      congrArg (fun z ↦ e.hom.app ((DerivedTensorConstraints.totalModel R pq n).obj) ≫
        DerivedCategory.Q.map z) hc
  have h := associativity_from_representatives T V U m alphaR alphaS
    lB rB (DerivedCategory.Q.map (α_ p.obj q.obj n.obj).hom)
    lA.hom rA.hom (DerivedCategory.Q.map (α_ pp.obj qq.obj nn.obj).hom)
    (e.app p.obj) (e.app q.obj) (e.app n.obj) eL eR hB hA hL hR hC
  simpa only [comparisonLeft, comparisonRight, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    NatIso.prod_hom, NatTrans.prod, m_app, ← tensor_map,
      Functor.prod_obj, Functor.id_obj, CategoryTheory.prod.associator,
      Functor.comp_obj,
      Iso.refl_hom, NatTrans.id_app, Category.assoc, canonicalDerivedTensor, derivedTensor,
      Functor.curry_obj_obj_obj, DerivedTensorConstraints.tensor, T, U] using h

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
private theorem normalized_associativity
    (k : Comparison.{r, uC, vC, uD, vD} f)
    (mu : Phi f.L.mapDerivedCategory ≅ Psi f.L.mapDerivedCategory)
    (hn : PullbackTensorCanonical.IsNormalized f k f.L.mapDerivedCategory
      f.L.mapDerivedCategoryFactors.hom mu.hom)
    (alphaR : DerivedTensorConstraints.leftAssociated R ≅
      DerivedTensorConstraints.rightAssociated R)
    (sigmaR : DerivedTensorConstraints.tensor R ≅ DerivedTensorConstraints.swapped R)
    (hconstraintsR : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource R a b ≅
        DerivedTensorConstraints.shiftedTarget R a b,
      DerivedTensorConstraints.IsNormalized R t alphaR sigmaR)
    (alphaS : DerivedTensorConstraints.leftAssociated S ≅
      DerivedTensorConstraints.rightAssociated S)
    (sigmaS : DerivedTensorConstraints.tensor S ≅ DerivedTensorConstraints.swapped S)
    (hconstraintsS : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource S a b ≅
        DerivedTensorConstraints.shiftedTarget S a b,
      DerivedTensorConstraints.IsNormalized S t alphaS sigmaS)
    (hresolving : ∀ p : DerivedTensorConstraints.Model R,
      DerivedTensorConstraints.resolvingComplex S ((pull f).obj p.obj))
    :
    ∀ A B N : DerivedCategory (Modules R),
      f.L.mapDerivedCategory.map (alphaR.hom.app ((A, B), N)) ≫
        mu.hom.app (A, ((derivedTensor R).obj B).obj N) ≫
        (Functor.uncurry.obj (derivedTensor S)).map
          (Prod.mkHom (𝟙 _) (mu.hom.app (B, N))) =
      mu.hom.app (((derivedTensor R).obj A).obj B, N) ≫
        (Functor.uncurry.obj (derivedTensor S)).map
          (Prod.mkHom (mu.hom.app (A, B)) (𝟙 _)) ≫
        alphaS.hom.app ((f.L.mapDerivedCategory.obj A, f.L.mapDerivedCategory.obj B),
          f.L.mapDerivedCategory.obj N) := by
  let U := f.L.mapDerivedCategory
  let T := DerivedTensorConstraints.tensor R
  let V := DerivedTensorConstraints.tensor S
  let m : T ⋙ U ≅ (U.prod U) ⋙ V :=
    isoWhiskerRight (tensorBridge R).symm U ≪≫ mu ≪≫
      isoWhiskerLeft (U.prod U) (tensorBridge S)
  have m_app (X Y : DerivedCategory (Modules R)) :
      m.hom.app (X, Y) = mu.hom.app (X, Y) := by
    dsimp only [m, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      whiskerRight_app, Iso.symm_hom, isoWhiskerLeft_hom, whiskerLeft_app,
      Functor.prod_obj]
    rw [tensorBridge_inv, tensorBridge_hom]
    with_unfolding_all
      rw [U.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _)
  have tensor_map {X Y : DerivedCategory (Modules S) × DerivedCategory (Modules S)}
      (g : X ⟶ Y) : (Functor.uncurry.obj (canonicalDerivedTensor S)).map g = V.map g := by
    have h := (tensorBridge S).hom.naturality g
    simpa only [tensorBridge_hom, Category.id_comp, Category.comp_id] using h
  let a : DerivedTensorConstraints.leftAssociated R ⋙ U ≅
      ((U.prod U).prod U) ⋙ DerivedTensorConstraints.rightAssociated S :=
    isoWhiskerRight alphaR U ≪≫ comparisonRight T V U m
  let b : DerivedTensorConstraints.leftAssociated R ⋙ U ≅
      ((U.prod U).prod U) ⋙ DerivedTensorConstraints.rightAssociated S :=
    comparisonLeft T V U m ≪≫ isoWhiskerLeft ((U.prod U).prod U) alphaS
  have hab : a = b := by
    have := resolving_essSurj (R := R)
    let q := (PullbackTensorCanonical.resolvingProperty (R := R)).ι ⋙ DerivedCategory.Q
    apply Iso.ext
    apply NatTrans.ext
    funext z
    let p := q.objPreimage z.1.1
    let p' := q.objPreimage z.1.2
    let n := q.objPreimage z.2
    let e := Iso.prod (Iso.prod (q.objObjPreimageIso z.1.1)
      (q.objObjPreimageIso z.1.2)) (q.objObjPreimageIso z.2)
    apply (cancel_epi ((DerivedTensorConstraints.leftAssociated R ⋙ U).map e.hom)).1
    rw [a.hom.naturality, b.hom.naturality]
    apply congrArg (fun t ↦ t ≫
      (((U.prod U).prod U) ⋙ DerivedTensorConstraints.rightAssociated S).map e.hom)
    have hc := normalized_associativity_model f k mu hn alphaR sigmaR hconstraintsR
      alphaS sigmaS hconstraintsS hresolving
      ⟨p.obj, p.property⟩ ⟨p'.obj, p'.property⟩ ⟨n.obj, n.property⟩
    with_unfolding_all
      simpa only [a, b, comparisonLeft, comparisonRight, Iso.trans_hom,
        NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
        whiskerRight_app, NatIso.prod_hom, NatTrans.prod, m_app, ← tensor_map,
        Functor.prod_obj, Functor.id_obj, CategoryTheory.prod.associator,
        Functor.comp_obj, Iso.refl_hom, NatTrans.id_app, Category.assoc,
        canonicalDerivedTensor, derivedTensor, Functor.curry_obj_obj_obj,
        DerivedTensorConstraints.tensor, T, U, q, p, p', n,
        ObjectProperty.ι_obj, Functor.uncurry_obj_obj] using hc
  intro A B N
  have h := congrArg (fun z ↦ z.hom.app ((A, B), N)) hab
  with_unfolding_all
    simpa only [a, b, comparisonLeft, comparisonRight, Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, NatIso.prod_hom, NatTrans.prod, m_app, ← tensor_map,
      Functor.prod_obj, Functor.id_obj, CategoryTheory.prod.associator,
      Functor.comp_obj,
      Iso.refl_hom, NatTrans.id_app, Category.assoc, canonicalDerivedTensor, derivedTensor,
      Functor.curry_obj_obj_obj, DerivedTensorConstraints.tensor, T, U] using h


end

variable (k : Comparison.{r, uC, vC, uD, vD} f)
  (epsilon : DerivedCategory.Q ⋙ L ⟶ pull.{r, uC, vC, uD, vD} f ⋙ DerivedCategory.Q)
  [L.CommShift ℤ] [NatTrans.CommShift epsilon ℤ]
  [(derivedTensor R).CommShift₂Int] [(derivedTensor S).CommShift₂Int]

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan in
/-- Transport of the representative-normalized pullback tensor comparison has
its prescribed resolving components, is unique among all natural transformations,
and respects simultaneous integer shifts, Koszul symmetry and reassociation.
The normalized associator and symmetry use the existing constraint predicate;
its existential shift component merely projects out those two normalizations.
No restriction is made on the boundedness of any complex or derived object.

Source: Stacks sites-cohomology.tex, Tags 07A4, 06YU and 0FPT;
more-algebra.tex, section-sign-rules, item-shift-tensor and item-flip-tensor-product
(blueprint: lem-pur-resolving-tensor-signed-coherence).

Proof, following the node's seven steps:
1. Total tensors of flat-term K-flat complexes are resolving by
   lem-pur-kflat-total-tensor-model; the preservation hypothesis puts the
   pullbacks of all inputs and nested totals in the target resolving class.
2. Conjugate muL by eta. Naturality of eta at the representative map r cancels
   eta at the total tensor. Substitute eta followed by kappa = epsilon on each
   resolving input and its total tensor. The muL normalization becomes precisely
   IsNormalized with epsilon replaced by the exact factorization kappa.
3. Cancel U(r) and the tensor of the invertible kappa components. Two normalized
   natural transformations agree on resolving pairs; the faithful binary resolving
   restriction of lem-weil-pbc-pullback-tensor-canonical-shift-unit gives equality.
4. The exact derived functor is left derived since its factorization is an
   isomorphism. The fixed-right and fixed-left shift equations of
   lem-weil-pbc-pullback-tensor-canonical-shift-unit apply to the normalized
   comparison. Extract the first shift a before the second b, substitute the two
   one-variable equations, and combine the shifts by naturality and commShiftIso_add'.
5. On resolving pairs, the representative normalizations of sigma, sigma' and
   step 2 reduce the symmetry equation to the cochain braiding equation of
   lem-pur-cochain-comparison-monoidal-equations; cancel and restrict faithfully.
6. On resolving triples, paste the four binary normalization squares, move the
   cochain comparisons through the representative isomorphisms of
   lem-pur-derived-tensor-additive-constraints, and apply the unsigned cochain
   reassociation equation of lem-pur-cochain-comparison-monoidal-equations.
7. Both associativity paths are natural isomorphisms of trifunctors. Every derived
   object is isomorphic to a resolving localization (resolving essential
   surjectivity of lem-weil-pbc-pullback-tensor-canonical-shift-unit); naturality
   transports step 6 to every triple. No boundedness is used anywhere.
-/
theorem resolving_tensor_signed_coherence
    (hL : L.IsLeftDerivedFunctor epsilon
      (HomologicalComplex.quasiIso (Modules R) (.up ℤ)))
    (hshiftR : HasCanonicalTensorShifts (R := R))
    (hshiftS : HasCanonicalTensorShifts (R := S))
    (hflat : ∀ M : Modules R, IsFlatOnSite (J := J) (R := R) M →
      IsFlatOnSite (J := K) (R := S) (f.L.obj M))
    (hresolving : ∀ P : CochainComplex (Modules R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      CochainComplex.IsKFlatIndependentCoefficients ((pull.{r, uC, vC, uD, vD} f).obj P) ∧
        ∀ n : ℤ, IsFlatOnSite (J := K) (R := S)
          (((pull.{r, uC, vC, uD, vD} f).obj P).X n))
    (hsums : ∀ I : Type r, PreservesColimitsOfShape (Discrete I) f.L)
    (eta : L ≅ f.L.mapDerivedCategory) [NatTrans.CommShift eta.hom ℤ]
    (heta : ∀ P : CochainComplex (Modules R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
      eta.hom.app (DerivedCategory.Q.obj P) ≫ f.L.mapDerivedCategoryFactors.hom.app P =
        epsilon.app P)
    (muL : Phi L ≅ Psi L)
    (hmuL : PullbackTensorCanonical.IsNormalized f k L epsilon muL.hom)
    (alphaR : DerivedTensorConstraints.leftAssociated R ≅
      DerivedTensorConstraints.rightAssociated R)
    (sigmaR : DerivedTensorConstraints.tensor R ≅ DerivedTensorConstraints.swapped R)
    (hconstraintsR : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource R a b ≅
        DerivedTensorConstraints.shiftedTarget R a b,
      DerivedTensorConstraints.IsNormalized R t alphaR sigmaR)
    (alphaS : DerivedTensorConstraints.leftAssociated S ≅
      DerivedTensorConstraints.rightAssociated S)
    (sigmaS : DerivedTensorConstraints.tensor S ≅ DerivedTensorConstraints.swapped S)
    (hconstraintsS : ∃ t : ∀ a b : ℤ,
      DerivedTensorConstraints.shiftedSource S a b ≅
        DerivedTensorConstraints.shiftedTarget S a b,
      DerivedTensorConstraints.IsNormalized S t alphaS sigmaS) :
    PullbackTensorCanonical.IsNormalized f k f.L.mapDerivedCategory
      f.L.mapDerivedCategoryFactors.hom (transportedComparison f L muL eta).hom ∧
    (∀ tau : Phi f.L.mapDerivedCategory ⟶ Psi f.L.mapDerivedCategory,
      PullbackTensorCanonical.IsNormalized f k f.L.mapDerivedCategory
        f.L.mapDerivedCategoryFactors.hom tau →
      tau = (transportedComparison f L muL eta).hom) ∧
    (∀ (a b : ℤ) (A B : DerivedCategory (Modules R)),
      (transportedComparison f L muL eta).hom.app (A⟦a⟧, B⟦b⟧) ≫
          (Functor.uncurry.obj (derivedTensor S)).map
            (Prod.mkHom ((f.L.mapDerivedCategory.commShiftIso a).hom.app A)
              ((f.L.mapDerivedCategory.commShiftIso b).hom.app B)) ≫
          (((derivedTensor S).flip.obj ((f.L.mapDerivedCategory.obj B)⟦b⟧)).commShiftIso a).hom.app
            (f.L.mapDerivedCategory.obj A) ≫
          (shiftFunctor _ a).map
            ((((derivedTensor S).obj (f.L.mapDerivedCategory.obj A)).commShiftIso b).hom.app
              (f.L.mapDerivedCategory.obj B)) ≫
          (shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.app
            (((derivedTensor S).obj (f.L.mapDerivedCategory.obj A)).obj
              (f.L.mapDerivedCategory.obj B)) =
        f.L.mapDerivedCategory.map
          ((((derivedTensor R).flip.obj (B⟦b⟧)).commShiftIso a).hom.app A ≫
            (shiftFunctor _ a).map (((derivedTensor R).obj A).commShiftIso b |>.hom.app B) ≫
            (shiftFunctorAdd' _ b a (a + b) (add_comm b a)).inv.app
              (((derivedTensor R).obj A).obj B)) ≫
          (f.L.mapDerivedCategory.commShiftIso (a + b)).hom.app
            (((derivedTensor R).obj A).obj B) ≫
          ((transportedComparison f L muL eta).hom.app (A, B))⟦a + b⟧') ∧
    (∀ A B : DerivedCategory (Modules R),
      f.L.mapDerivedCategory.map (sigmaR.hom.app (A, B)) ≫
          (transportedComparison f L muL eta).hom.app (B, A) =
        (transportedComparison f L muL eta).hom.app (A, B) ≫
          sigmaS.hom.app (f.L.mapDerivedCategory.obj A, f.L.mapDerivedCategory.obj B)) ∧
    (∀ A B N : DerivedCategory (Modules R),
      f.L.mapDerivedCategory.map (alphaR.hom.app ((A, B), N)) ≫
          (transportedComparison f L muL eta).hom.app
            (A, ((derivedTensor R).obj B).obj N) ≫
          (Functor.uncurry.obj (derivedTensor S)).map
            (Prod.mkHom (𝟙 _) ((transportedComparison f L muL eta).hom.app (B, N))) =
        (transportedComparison f L muL eta).hom.app
            (((derivedTensor R).obj A).obj B, N) ≫
          (Functor.uncurry.obj (derivedTensor S)).map
            (Prod.mkHom ((transportedComparison f L muL eta).hom.app (A, B)) (𝟙 _)) ≫
          alphaS.hom.app ((f.L.mapDerivedCategory.obj A, f.L.mapDerivedCategory.obj B),
            f.L.mapDerivedCategory.obj N)) := by
  have _ := hL
  have _ := hflat
  have _ := hsums
  have _ := (inferInstance : NatTrans.CommShift epsilon ℤ)
  have hn : PullbackTensorCanonical.IsNormalized f k f.L.mapDerivedCategory
      f.L.mapDerivedCategoryFactors.hom (transportedComparison f L muL eta).hom := by
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.monoidalCategory S
    unfold PullbackTensorCanonical.IsNormalized
    have hmu := hmuL
    unfold PullbackTensorCanonical.IsNormalized at hmu
    intro P Q hp hq hf hg
    obtain ⟨hp', hq', hf', hg', hm⟩ := hmu P Q hp hq hf hg
    refine ⟨hp', hq', hf', hg', ?_⟩
    let V := ((totalTensor R).obj P).obj Q
    have hV := KFlatTotalTensorModel.kFlat_total_tensor_model R P Q hp hq hf hg
    have heV := heta V hV.1 hV.2.1
    with_unfolding_all
      exact conjugate_square L f.L.mapDerivedCategory eta
        (Functor.uncurry.obj (canonicalDerivedTensor S))
        (canonicalRepresentativeIso R P Q hp hq hf hg).hom
        (muL.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
        (epsilon.app P) (epsilon.app Q) (epsilon.app V)
        (f.L.mapDerivedCategoryFactors.hom.app P)
        (f.L.mapDerivedCategoryFactors.hom.app Q)
        (f.L.mapDerivedCategoryFactors.hom.app V)
        (DerivedCategory.Q.map (comparison f k P Q).hom ≫
          (canonicalRepresentativeIso S ((pull f).obj P) ((pull f).obj Q)
            hp' hq' hf' hg').hom)
        hm (heta P hp hf) (heta Q hq hg) heV
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · intro tau ht
    have hn' := hn
    unfold PullbackTensorCanonical.IsNormalized at ht hn'
    obtain ⟨ff⟩ := resolving_fullyFaithful (R := R) (S := S)
    apply ff.map_injective
    apply NatTrans.ext
    funext Z
    obtain ⟨⟨P, hp, hf⟩, ⟨Q, hq, hg⟩⟩ := Z
    change tau.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (transportedComparison f L muL eta).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
    obtain ⟨_, _, _, _, ha⟩ := ht P Q hp hq hf hg
    obtain ⟨_, _, _, _, hb⟩ := hn' P Q hp hq hf hg
    let t := (Functor.uncurry.obj (canonicalDerivedTensor S)).map
      (Prod.mkHom (f.L.mapDerivedCategoryFactors.hom.app P)
        (f.L.mapDerivedCategoryFactors.hom.app Q))
    have : IsIso t := by
      dsimp only [t, Functor.uncurry_obj_map]
      infer_instance
    apply (cancel_epi (f.L.mapDerivedCategory.map
      (canonicalRepresentativeIso R P Q hp hq hf hg).hom)).1
    apply (cancel_mono t).1
    rw [Category.assoc, Category.assoc]
    with_unfolding_all exact ha.trans hb.symm
  · intro a b A B
    let := canonicalDerivedTensorCommShift (R := R)
    let := canonicalDerivedTensorCommShift (R := S)
    let U := f.L.mapDerivedCategory
    let mu := transportedComparison f L muL eta
    have hU : U.IsLeftDerivedFunctor f.L.mapDerivedCategoryFactors.hom
        (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) :=
      Functor.isLeftDerivedFunctor_of_inverts _ U f.L.mapDerivedCategoryFactors
    have hr (n : ℤ) (X Y : DerivedCategory (Modules R)) := by
      have hh := rightShift_global f k U f.L.mapDerivedCategoryFactors.hom
        hshiftR hshiftS mu hn hU Y
      change NatTrans.CommShift (fixedRight (canonicalDerivedTensor R)
        (canonicalDerivedTensor S) U mu.hom Y) ℤ at hh
      letI := hh
      exact fixedRight_shift_equation (canonicalDerivedTensor R)
        (canonicalDerivedTensor S) U mu.hom Y n X
    have hl (n : ℤ) (X Y : DerivedCategory (Modules R)) := by
      have hh := leftShift_global f k U f.L.mapDerivedCategoryFactors.hom
        hshiftR hshiftS mu hn hU X
      change NatTrans.CommShift (fixedLeft (canonicalDerivedTensor R)
        (canonicalDerivedTensor S) U mu.hom X) ℤ at hh
      letI := hh
      exact fixedLeft_shift_equation (canonicalDerivedTensor R)
        (canonicalDerivedTensor S) U mu.hom X n Y
    exact simultaneousShift (canonicalDerivedTensor R) (canonicalDerivedTensor S)
      U mu.hom hr hl a b A B
  · exact normalized_symmetry f k (transportedComparison f L muL eta).hom hn
      alphaR sigmaR hconstraintsR alphaS sigmaS hconstraintsS
  · apply normalized_associativity f k (transportedComparison f L muL eta) hn
      alphaR sigmaR hconstraintsR alphaS sigmaS hconstraintsS
    intro E
    exact hresolving E.obj E.property.1 E.property.2

end SheafOfModules.ResolvingTensorSigned
