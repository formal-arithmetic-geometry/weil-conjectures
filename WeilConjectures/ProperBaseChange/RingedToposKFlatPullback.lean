/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat

import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.ProperBaseChange.GeometricModuleConstruction
import all WeilConjectures.ProperBaseChange.GeometricModuleTransport
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.ProperBaseChange.FlatAlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.ProperBaseChange.RingedToposPullbackFilteredColimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback

/-!
# Tensor pullback for a supplied ringed-topos module direct image

Source: Stacks Project, Modules on Sites, Tag 03D7, and Cohomology on Sites,
Tags 0G7E and 06YY (blueprint: lem-weil-pbc-supplied-ringed-topos-kflat-pullback).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open SheafOfModules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000

private theorem graph_binary
    {C D : Type*} [Category C] [Category D] [HasBinaryProducts C] [HasBinaryProducts D]
    (F : C ⥤ D) {X Y Z T : C} {A B E : D}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (h : F.map a = prodComparison F X Y ≫ prod.map eX.inv eY.inv ≫ b ≫ eZ.hom)
    (x : T ⟶ X) (y : T ⟶ Y) (t : T ⟶ Z) (ht : t = prod.lift x y ≫ a) :
    F.map t ≫ eZ.inv = prod.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv) ≫ b := by
  have hp : F.map (prod.lift x y) ≫ prodComparison F X Y =
      prod.lift (F.map x) (F.map y) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst, ← F.map_comp, prod.lift_fst]
    · simp only [Category.assoc, prodComparison_snd, ← F.map_comp, prod.lift_snd]
  rw [ht, F.map_comp, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, hp]
  rw [prod.lift_map]

private theorem graph_sections
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    {X Y Z T : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (eX : A ≅ F.obj X) (eY : B ≅ F.obj Y) (eZ : E ≅ F.obj Z)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (h : F.map a = prodComparison F X Y ≫ prod.map eX.inv eY.inv ≫ b ≫ eZ.hom)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p) ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p) ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z)
    (hz : ∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) :
    ∀ V p, (F.map z ≫ eZ.inv).hom.app V p =
      op' V ((F.map x ≫ eX.inv).hom.app V p)
        ((F.map y ≫ eY.inv).hom.app V p) := by
  have he : z = prod.lift x y ≫ a := by
    ext U p
    change z.hom.app U p = a.hom.app U ((prod.lift x y).hom.app U p)
    rw [hs, hz]
    have h₁ := congrArg (fun k : T ⟶ X ↦ k.hom.app U p) (prod.lift_fst x y)
    have h₂ := congrArg (fun k : T ⟶ Y ↦ k.hom.app U p) (prod.lift_snd x y)
    change (prod.fst : X ⨯ Y ⟶ X).hom.app U ((prod.lift x y).hom.app U p) = _ at h₁
    change (prod.snd : X ⨯ Y ⟶ Y).hom.app U ((prod.lift x y).hom.app U p) = _ at h₂
    rw [h₁, h₂]
  have he' := graph_binary F eX eY eZ a b h x y z he
  intro V p
  have hh := congrArg (fun k ↦ k.hom.app V p) he'
  change (F.map z ≫ eZ.inv).hom.app V p =
    b.hom.app V ((prod.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv)).hom.app V p) at hh
  rw [ht] at hh
  have h₁ := congrArg (fun k : F.obj T ⟶ A ↦ k.hom.app V p)
    (prod.lift_fst (F.map x ≫ eX.inv) (F.map y ≫ eY.inv))
  have h₂ := congrArg (fun k : F.obj T ⟶ B ↦ k.hom.app V p)
    (prod.lift_snd (F.map x ≫ eX.inv) (F.map y ≫ eY.inv))
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prod.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv)).hom.app V p) = _ at h₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prod.lift (F.map x ≫ eX.inv) (F.map y ≫ eY.inv)).hom.app V p) = _ at h₂
  rw [h₁, h₂] at hh
  exact hh


private theorem algebraic_image
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    [PreservesFiniteLimits F] (R : Sheaf J CommRingCat.{u}) :
    ∃ RI : Sheaf K CommRingCat.{u}, Nonempty (AlgebraicInverseImage F R RI) := by
  obtain ⟨RI, eR, addR, mulR, addRI, mulRI, haR, hmR, haRI, hmRI, hea, hem⟩ :=
    geometric_ring_transport J K F R
  obtain ⟨I, P, eI, eP, hI, hP⟩ :=
    geometric_module_construction J K F V adj R RI RI eR addR mulR addRI mulRI
      ⟨haR, hmR, haRI, hmRI, hea, hem⟩ (𝟙 RI)
  have hAdd (T : Sheaf J (Type u)) := graph_sections (T := T) F eR eR eR addR addRI hea
    (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add (RI.obj.obj U) inferInstance x y) haR haRI
  have hMul (T : Sheaf J (Type u)) := graph_sections (T := T) F eR eR eR mulR mulRI hem
    (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
    (fun U x y ↦ @Mul.mul (RI.obj.obj U) inferInstance x y) hmR hmRI
  refine ⟨RI, ⟨{
    ringUnderlying := eR.symm
    ringAdd := fun T x y z hz ↦ hAdd T x y z hz
    ringMul := fun T x y z hz ↦ hMul T x y z hz
    ringZero := ?_
    ringOne := ?_
    modules := I
    moduleUnderlying := eI
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_
  }⟩⟩
  · intro T z hz U x
    have h := hAdd T z z z (by
      intro W t
      have hz' : @Eq (R.obj.obj W) (z.hom.app W t) 0 := hz W t
      exact hz'.trans ((zero_add (0 : R.obj.obj W)).symm.trans
        (congrArg₂ (fun a b : R.obj.obj W ↦ a + b) hz'.symm hz'.symm))) U x
    exact add_eq_left.mp h.symm
  · intro T z hz U x
    let S := (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
    let X := T ⨯ S
    let q := sectionPair (F.obj T) (F.obj S) U x
      (eR.hom.hom.app U (1 : RI.obj.obj U))
    let p := (inv (prodComparison F T S)).hom.app U q
    have h₁ : inv (prodComparison F T S) ≫ F.map (prod.fst : X ⟶ T) = prod.fst := by
      rw [← prodComparison_fst, IsIso.inv_hom_id_assoc]
    have h₂ : inv (prodComparison F T S) ≫ F.map (prod.snd : X ⟶ S) = prod.snd := by
      rw [← prodComparison_snd, IsIso.inv_hom_id_assoc]
    have hp₁ : (F.map (prod.fst : X ⟶ T)).hom.app U p = x := by
      change (inv (prodComparison F T S) ≫ F.map (prod.fst : X ⟶ T)).hom.app U q = x
      rw [h₁]
      exact sectionPair_fst _ _ _ _ _
    have hp₂ : (F.map (prod.snd : X ⟶ S)).hom.app U p =
        eR.hom.hom.app U (1 : RI.obj.obj U) := by
      change (inv (prodComparison F T S) ≫ F.map (prod.snd : X ⟶ S)).hom.app U q = _
      rw [h₂]
      exact sectionPair_snd _ _ _ _ _
    have he := hMul X (prod.fst ≫ z) prod.snd prod.snd (by
      intro W t
      have hz' : @Eq (R.obj.obj W) (z.hom.app W ((prod.fst : X ⟶ T).hom.app W t)) 1 :=
        hz W _
      change (prod.snd : X ⟶ S).hom.app W t =
        @Mul.mul (R.obj.obj W) inferInstance
          (z.hom.app W ((prod.fst : X ⟶ T).hom.app W t))
          ((prod.snd : X ⟶ S).hom.app W t)
      exact (one_mul (show R.obj.obj W from (prod.snd : X ⟶ S).hom.app W t)).symm.trans
        (congrArg (fun a : R.obj.obj W ↦ a *
          (show R.obj.obj W from (prod.snd : X ⟶ S).hom.app W t)) hz'.symm)) U p
    rw [F.map_comp] at he
    change eR.inv.hom.app U ((F.map (prod.snd : X ⟶ S)).hom.app U p) =
      @Mul.mul (RI.obj.obj U) inferInstance
        (eR.inv.hom.app U ((F.map z).hom.app U
          ((F.map (prod.fst : X ⟶ T)).hom.app U p)))
        (eR.inv.hom.app U ((F.map (prod.snd : X ⟶ S)).hom.app U p)) at he
    rw [hp₁, hp₂] at he
    have hi := congrArg (fun k ↦ k.hom.app U (1 : RI.obj.obj U)) eR.hom_inv_id
    change eR.inv.hom.app U (eR.hom.hom.app U (1 : RI.obj.obj U)) =
      (1 : RI.obj.obj U) at hi
    let v : RI.obj.obj U := eR.inv.hom.app U ((F.map z).hom.app U x)
    exact (mul_one v).symm.trans
      ((congrArg (fun b : RI.obj.obj U ↦ v * b) hi.symm).trans (he.symm.trans hi))
  · intro M T a b t ht
    obtain ⟨addM, muM, addI, muI, haM, hsM, haI, hsI, heaI, hesI⟩ := hI M
    exact graph_sections F (eI.app M) (eI.app M) (eI.app M) addM addI heaI
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((I.obj M).val.obj U) inferInstance x y) haM haI a b t ht
  · intro M T a ha U x
    obtain ⟨addM, muM, addI, muI, haM, hsM, haI, hsI, heaI, hesI⟩ := hI M
    have h := graph_sections F (eI.app M) (eI.app M) (eI.app M) addM addI heaI
      (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((I.obj M).val.obj U) inferInstance x y) haM haI a a a
      (by
        intro W t
        have ha' : @Eq (M.val.obj W) (a.hom.app W t) 0 := ha W t
        exact ha'.trans ((zero_add (0 : M.val.obj W)).symm.trans
          (congrArg₂ (fun a b : M.val.obj W ↦ a + b) ha'.symm ha'.symm))) U x
    exact add_eq_left.mp h.symm
  · intro M T a b t ht
    obtain ⟨addM, muM, addI, muI, haM, hsM, haI, hsI, heaI, hesI⟩ := hI M
    exact graph_sections F eR (eI.app M) (eI.app M) muM muI hesI
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M.val.obj U) inferInstance x y)
      (fun U x y ↦ @SMul.smul (RI.obj.obj U) ((I.obj M).val.obj U) inferInstance x y)
      hsM hsI a b t ht


private theorem reflect_binary
    {C D : Type*} [Category C] [Category D] [HasBinaryProducts C] [HasBinaryProducts D]
    (F : C ⥤ D) [PreservesFiniteProducts F]
    {X : C} {A B : D} (e : A ≅ F.obj X)
    (a : X ⨯ X ⟶ X) (b : A ⨯ A ⟶ A) (c : B ⨯ B ⟶ B) (φ : F.obj X ⟶ B)
    (h : F.map a = prodComparison F X X ≫ prod.map e.inv e.inv ≫ b ≫ e.hom)
    (hφ : F.map a ≫ φ = prodComparison F X X ≫ prod.map φ φ ≫ c) :
    b ≫ e.hom ≫ φ = prod.map (e.hom ≫ φ) (e.hom ≫ φ) ≫ c := by
  apply (cancel_epi (prodComparison F X X ≫ prod.map e.inv e.inv)).mp
  have hh := (congrArg (fun k ↦ k ≫ φ) h).symm.trans hφ
  simpa only [Category.assoc, prod.map_map_assoc, Iso.inv_hom_id_assoc] using hh

private theorem binary_of_graph
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    {X Y Z : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (dX : F.obj X ⟶ A) (dY : F.obj Y ⟶ B) (dZ : F.obj Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (hgraph : ∀ (T : Sheaf J (Type u)) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
      (∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) →
      ∀ V p, (F.map z ≫ dZ).hom.app V p =
        op' V ((F.map x ≫ dX).hom.app V p) ((F.map y ≫ dY).hom.app V p)) :
    F.map a ≫ dZ = prodComparison F X Y ≫ prod.map dX dY ≫ b := by
  have h₁ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.fst =
      F.map prod.fst ≫ dX := by simp only [prod.map_fst, prodComparison_fst_assoc]
  have h₂ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.snd =
      F.map prod.snd ≫ dY := by simp only [prod.map_snd, prodComparison_snd_assoc]
  ext V p
  have h := hgraph (X ⨯ Y) prod.fst prod.snd a hs V p
  change (F.map a ≫ dZ).hom.app V p = b.hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p)
  rw [ht]
  have hh₁ := congrArg (fun k ↦ k.hom.app V p) h₁
  have hh₂ := congrArg (fun k ↦ k.hom.app V p) h₂
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₂
  rw [hh₁, hh₂]
  exact h

private theorem binary_hom_sections
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {X Y Z A B E : Sheaf J (Type u)}
    (dX : X ⟶ A) (dY : Y ⟶ B) (dZ : Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ U, A.obj.obj U → B.obj.obj U → E.obj.obj U)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ U p, b.hom.app U p =
      op' U ((prod.fst : A ⨯ B ⟶ A).hom.app U p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app U p))
    (h : a ≫ dZ = prod.map dX dY ≫ b) :
    ∀ U x y, dZ.hom.app U (op U x y) =
      op' U (dX.hom.app U x) (dY.hom.app U y) := by
  intro U x y
  let p := SheafOfModules.sectionPair X Y U x y
  have hh := congrArg (fun k ↦ k.hom.app U p) h
  change dZ.hom.app U (a.hom.app U p) = b.hom.app U ((prod.map dX dY).hom.app U p) at hh
  rw [hs, ht] at hh
  rw [SheafOfModules.prodMap_fst_apply, SheafOfModules.prodMap_snd_apply] at hh
  simpa only [p, SheafOfModules.sectionPair_fst, SheafOfModules.sectionPair_snd] using hh

open SheafOfModules.GeometricConstruction

private noncomputable abbrev radd
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringAdd R

private noncomputable abbrev rmul
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringMul R

private theorem structural_map
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI) :
    ∃ c : RI ⟶ A, (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      I.ringUnderlying.inv ≫ f.ringMap := by
  let _ := f.leftExact
  let e := I.ringUnderlying.symm
  let φ := f.ringMap
  let d := e.hom ≫ φ
  have hca : f.inverse.map (radd B) ≫ e.inv =
      prodComparison f.inverse (rset B) (rset B) ≫ prod.map e.inv e.inv ≫ radd RI :=
    binary_of_graph f.inverse e.inv e.inv e.inv (radd B) (radd RI)
      (fun U x y ↦ @Add.add (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) I.ringAdd
  have hcm : f.inverse.map (rmul B) ≫ e.inv =
      prodComparison f.inverse (rset B) (rset B) ≫ prod.map e.inv e.inv ≫ rmul RI :=
    binary_of_graph f.inverse e.inv e.inv e.inv (rmul B) (rmul RI)
      (fun U x y ↦ @Mul.mul (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) I.ringMul
  have ha : f.inverse.map (radd B) =
      prodComparison f.inverse (rset B) (rset B) ≫
        prod.map e.inv e.inv ≫ radd RI ≫ e.hom := by
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hca
  have hm : f.inverse.map (rmul B) =
      prodComparison f.inverse (rset B) (rset B) ≫
        prod.map e.inv e.inv ≫ rmul RI ≫ e.hom := by
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hcm
  have hφa : f.inverse.map (radd B) ≫ φ =
      prodComparison f.inverse (rset B) (rset B) ≫ prod.map φ φ ≫ radd A :=
    binary_of_graph f.inverse φ φ φ (radd B) (radd A)
      (fun U x y ↦ @Add.add (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (A.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) f.ring_add
  have hφm : f.inverse.map (rmul B) ≫ φ =
      prodComparison f.inverse (rset B) (rset B) ≫ prod.map φ φ ≫ rmul A :=
    binary_of_graph f.inverse φ φ φ (rmul B) (rmul A)
      (fun U x y ↦ @Mul.mul (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (A.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) f.ring_mul
  have hAdd := binary_hom_sections d d d (radd RI) (radd A)
    (fun U x y ↦ @Add.add (RI.obj.obj U) inferInstance x y)
    (fun U x y ↦ @Add.add (A.obj.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (reflect_binary f.inverse e (radd B) (radd RI) (radd A) φ ha hφa)
  have hMul := binary_hom_sections d d d (rmul RI) (rmul A)
    (fun U x y ↦ @Mul.mul (RI.obj.obj U) inferInstance x y)
    (fun U x y ↦ @Mul.mul (A.obj.obj U) inferInstance x y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (reflect_binary f.inverse e (rmul B) (rmul RI) (rmul A) φ hm hφm)
  have hOne (U : Cᵒᵖ) : d.hom.app U (1 : RI.obj.obj U) = (1 : A.obj.obj U) := by
    let z : rset B ⟶ rset B := CartesianMonoidalCategory.toUnit _ ≫ ringOne B
    let p := e.hom.hom.app U (1 : RI.obj.obj U)
    have hi := I.ringOne (rset B) z (fun _ _ ↦ rfl) U p
    have hf := f.ring_one (rset B) z (fun _ _ ↦ rfl) U p
    have hi' : (f.inverse.map z).hom.app U p = p := by
      apply (ConcreteCategory.bijective_of_isIso (e.inv.hom.app U)).injective
      exact hi.trans (congrArg (fun k ↦ k.hom.app U (1 : RI.obj.obj U)) e.hom_inv_id).symm
    change φ.hom.app U p = (1 : A.obj.obj U)
    change φ.hom.app U ((f.inverse.map z).hom.app U p) = _ at hf
    rw [hi'] at hf
    exact hf
  have hZero (U : Cᵒᵖ) : d.hom.app U (0 : RI.obj.obj U) = (0 : A.obj.obj U) := by
    have h := hAdd U (0 : RI.obj.obj U) (0 : RI.obj.obj U)
    have hh := (congrArg (fun x : RI.obj.obj U ↦ d.hom.app U x)
      (zero_add (0 : RI.obj.obj U))).symm.trans h
    exact (@add_eq_left (A.obj.obj U) inferInstance inferInstance _ _).mp hh.symm
  refine ⟨⟨{
    app := fun U ↦ CommRingCat.ofHom {
      toFun := d.hom.app U
      map_one' := hOne U
      map_mul' := hMul U
      map_zero' := hZero U
      map_add' := hAdd U }
    naturality := ?_
  }⟩, rfl⟩
  intro U V i
  ext x
  exact CategoryTheory.congr_fun (d.hom.naturality i) x


open SheafOfModules.GeometricConstruction



private theorem h4_supplied_add
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (M : SheafOfModules.{u, u, u, u} (base A))
    (T : Sheaf K (Type u)) (x y z : T ⟶ (mset B).obj (f.modules.obj M))
    (hz : ∀ U t, @Eq ((f.modules.obj M).val.obj U) (z.hom.app U t)
      (@Add.add ((f.modules.obj M).val.obj U) inferInstance (x.hom.app U t) (y.hom.app U t))) :
    ∀ U t, @Eq (M.val.obj U)
      (((f.adj.homEquiv T _).symm (z ≫ f.underlying.hom.app M)).hom.app U t)
      (@Add.add (M.val.obj U) inferInstance
        (((f.adj.homEquiv T _).symm (x ≫ f.underlying.hom.app M)).hom.app U t)
        (((f.adj.homEquiv T _).symm (y ≫ f.underlying.hom.app M)).hom.app U t)) := by
  let one : T ⟶ rset B := CartesianMonoidalCategory.toUnit T ≫ ringOne B
  intro U t
  have h := f.module_linear M T one x y z (by
    intro W p
    exact (hz W p).trans (congrArg
      (fun a : (f.modules.obj M).val.obj W ↦ a + (show (f.modules.obj M).val.obj W from
        y.hom.app W p)) (one_smul (B.obj.obj W) (show (f.modules.obj M).val.obj W from
          x.hom.app W p)).symm)) U t
  have hOne := f.ring_one T one (fun _ _ ↦ rfl) U t
  rw [hOne] at h
  exact h.trans (congrArg₂ (fun a b : M.val.obj U ↦ a + b)
    (one_smul (A.obj.obj U) (show M.val.obj U from
      (((f.adj.homEquiv T _).symm (x ≫ f.underlying.hom.app M)).hom.app U t))) rfl)



private theorem h4_supplied_zero
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (M : SheafOfModules.{u, u, u, u} (base A))
    (T : Sheaf K (Type u)) (z : T ⟶ (mset B).obj (f.modules.obj M))
    (hz : ∀ U t, @Eq ((f.modules.obj M).val.obj U) (z.hom.app U t) 0) :
    ∀ U t, @Eq (M.val.obj U)
      (((f.adj.homEquiv T _).symm (z ≫ f.underlying.hom.app M)).hom.app U t) 0 := by
  intro U t
  have h := h4_supplied_add f M T z z z (by
    intro W p
    exact (hz W p).trans ((zero_add (0 : (f.modules.obj M).val.obj W)).symm.trans
      (congrArg₂ (fun a b : (f.modules.obj M).val.obj W ↦ a + b)
        (hz W p).symm (hz W p).symm))) U t
  exact (@add_eq_left (M.val.obj U) inferInstance inferInstance _ _).mp h.symm

private theorem h4_supplied_smul
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (M : SheafOfModules.{u, u, u, u} (base A))
    (T : Sheaf K (Type u)) (a : T ⟶ rset B)
    (x z : T ⟶ (mset B).obj (f.modules.obj M))
    (hz : ∀ U t, @Eq ((f.modules.obj M).val.obj U) (z.hom.app U t)
      (@SMul.smul (B.obj.obj U) ((f.modules.obj M).val.obj U) inferInstance
        (a.hom.app U t) (x.hom.app U t))) :
    ∀ U t, @Eq (M.val.obj U)
      (((f.adj.homEquiv T _).symm (z ≫ f.underlying.hom.app M)).hom.app U t)
      (@SMul.smul (A.obj.obj U) (M.val.obj U) inferInstance
        ((f.inverse.map a ≫ f.ringMap).hom.app U t)
        (((f.adj.homEquiv T _).symm (x ≫ f.underlying.hom.app M)).hom.app U t)) := by
  let z₀ : T ⟶ (mset B).obj (f.modules.obj M) := ⟨{
    app := fun W ↦ ↾(fun _ ↦ (0 : (f.modules.obj M).val.obj W))
    naturality := by
      intro W V i
      ext p
      exact ((f.modules.obj M).val.map i).hom.map_zero.symm }⟩
  intro U t
  have h := f.module_linear M T a x z₀ z (by
    intro W p
    exact (hz W p).trans (add_zero _).symm) U t
  have hZero := h4_supplied_zero f M T z₀ (fun _ _ ↦ rfl) U t
  rw [hZero] at h
  exact h.trans (@add_zero (M.val.obj U) inferInstance _)

open SheafOfModules.GeometricConstruction
private noncomputable abbrev madd
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u, u, u, u} (base R)) :=
  fromProd ((mset R).obj M) ((mset R).obj M) ≫ addition R M
private noncomputable abbrev msmul
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u, u, u, u} (base R)) :=
  fromProd (rset R) ((mset R).obj M) ≫ action R M



private theorem h4_supplied_operations
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (H : SheafOfModules.{u, u, u, u} (base A)) :
    letI : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
    (madd B (f.modules.obj H) ≫ f.underlying.hom.app H =
      prod.map (f.underlying.hom.app H) (f.underlying.hom.app H) ≫
        inv (prodComparison f.direct ((mset A).obj H) ((mset A).obj H)) ≫
          f.direct.map (madd A H)) ∧
    (msmul B (f.modules.obj H) ≫ f.underlying.hom.app H =
      prod.map (f.adj.homEquiv (rset B) (rset A) f.ringMap) (f.underlying.hom.app H) ≫
        inv (prodComparison f.direct (rset A) ((mset A).obj H)) ≫
          f.direct.map (msmul A H)) := by
  let _ : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
  let u := (f.adj.homEquiv ((mset B).obj (f.modules.obj H)) ((mset A).obj H)).symm
    (f.underlying.hom.app H)
  have ha : f.inverse.map (madd B (f.modules.obj H)) ≫ u =
      prodComparison f.inverse ((mset B).obj (f.modules.obj H))
        ((mset B).obj (f.modules.obj H)) ≫ prod.map u u ≫ madd A H :=
    binary_of_graph f.inverse u u u (madd B (f.modules.obj H)) (madd A H)
      (fun U x y ↦ @Add.add ((f.modules.obj H).val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (H.val.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by
        intro T x y z hz U t
        simpa only [f.adj.homEquiv_naturality_left_symm] using h4_supplied_add f H T x y z hz U t)
  have hs : f.inverse.map (msmul B (f.modules.obj H)) ≫ u =
      prodComparison f.inverse (rset B) ((mset B).obj (f.modules.obj H)) ≫
        prod.map f.ringMap u ≫ msmul A H :=
    binary_of_graph f.inverse f.ringMap u u (msmul B (f.modules.obj H)) (msmul A H)
      (fun U x y ↦ @SMul.smul (B.obj.obj U) ((f.modules.obj H).val.obj U) inferInstance x y)
      (fun U x y ↦ @SMul.smul (A.obj.obj U) (H.val.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by
        intro T a x z hz U t
        simpa only [f.adj.homEquiv_naturality_left_symm] using h4_supplied_smul f H T a x z hz U t)
  constructor
  · simpa only [u, Equiv.apply_symm_apply] using
      (binary_mate_iff f.adj (madd B (f.modules.obj H)) (madd A H) u u u).mp ha
  · simpa only [u, Equiv.apply_symm_apply] using
      (binary_mate_iff f.adj (msmul B (f.modules.obj H)) (msmul A H) f.ringMap u u).mp hs

set_option maxHeartbeats 600000 in
-- Restricting the adjunction to linear maps elaborates several large sheaf diagrams.
private theorem supplied_adjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      I.ringUnderlying.inv ≫ f.ringMap) :
    Nonempty (I.modules ⋙ tensorFunctor c ⊣ f.modules) := by
  let _ := f.leftExact
  let _ : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
  let eR := I.ringUnderlying.symm
  let eI := I.moduleUnderlying
  let eP := f.underlying
  have hec : eR.inv ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      f.ringMap := by
    rw [hc]
    simp only [eR, Iso.symm_inv, Iso.hom_inv_id_assoc]
  let E : ∀ M H, ((mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) ≃
      ((mset B).obj M ⟶ (mset B).obj (f.modules.obj H)) :=
    fun M H ↦ mateIsoEquiv f.adj (eI.app M) (eP.app H)
  have hImage M H (α : (mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) :
      (∃ a : I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj H, (mset RI).map a = α) ↔
        ∃ b : M ⟶ f.modules.obj H, (mset B).map b = E M H α := by
    have hLA : f.inverse.map (madd B M) =
        prodComparison f.inverse ((mset B).obj M) ((mset B).obj M) ≫
          prod.map (eI.inv.app M) (eI.inv.app M) ≫ madd RI (I.modules.obj M) ≫
            eI.hom.app M := by
      apply (cancel_mono (eI.inv.app M)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph f.inverse (eI.inv.app M) (eI.inv.app M) (eI.inv.app M)
        (madd B M) (madd RI (I.modules.obj M))
        (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
        (fun U x y ↦ @Add.add ((I.modules.obj M).val.obj U) inferInstance x y)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun T x y z hz U t ↦ I.moduleAdd M T x y z hz U t)
    have hLS : f.inverse.map (msmul B M) =
        prodComparison f.inverse (rset B) ((mset B).obj M) ≫
          prod.map eR.inv (eI.inv.app M) ≫ msmul RI (I.modules.obj M) ≫ eI.hom.app M := by
      apply (cancel_mono (eI.inv.app M)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph f.inverse eR.inv (eI.inv.app M) (eI.inv.app M)
        (msmul B M) (msmul RI (I.modules.obj M))
        (fun U x y ↦ @SMul.smul (B.obj.obj U) (M.val.obj U) inferInstance x y)
        (fun U x y ↦ @SMul.smul (RI.obj.obj U) ((I.modules.obj M).val.obj U)
          inferInstance x y)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun T a x z hz U t ↦ I.moduleSMul M T a x z hz U t)
    have hRightAdd := (h4_supplied_operations f H).1
    have hRightSmul := (h4_supplied_operations f H).2
    rw [← hec] at hRightSmul
    have hm : f.adj.homEquiv _ _ (eI.inv.app M ≫ α) = E M H α ≫ eP.hom.app H :=
      mateIsoEquiv_equation f.adj (eI.app M) (eP.app H) α
    have hAdd := binary_mate_iso_iff f.adj (eI.app M) (eI.app M) (eI.app M)
      (eP.hom.app H) (eP.hom.app H) (eP.app H) (madd B M)
      (madd RI (I.modules.obj M)) (madd A H) (madd B (f.modules.obj H))
      hLA hRightAdd α α α (E M H α) (E M H α) (E M H α) hm hm hm
    have hSmul := binary_mate_iso_iff f.adj eR (eI.app M) (eI.app M)
      (f.adj.homEquiv _ _ (eR.inv ≫ (sheafCompose J
        (CategoryTheory.forget CommRingCat.{u})).map c))
      (eP.hom.app H) (eP.app H) (msmul B M) (msmul RI (I.modules.obj M))
      (msmul A H) (msmul B (f.modules.obj H)) hLS hRightSmul
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c) α α
      (𝟙 (rset B)) (E M H α) (E M H α)
      (by exact (Category.id_comp _).symm) hm hm
    have hSame := linear_iff (𝟙 B) M (f.modules.obj H)
      (madd B M) (madd B (f.modules.obj H)) (msmul B M) (msmul B (f.modules.obj H))
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (E M H α)
    exact (linear_iff c (I.modules.obj M) H (madd RI (I.modules.obj M)) (madd A H)
      (msmul RI (I.modules.obj M)) (msmul A H)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) α).trans
        ((and_congr hAdd hSmul).trans hSame.symm)
  let B' : ∀ M H, (I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj H) ≃ (M ⟶ f.modules.obj H) :=
    fun M H ↦ restrictHomEquiv (mset RI) (mset B) (E M H) (hImage M H)
  have hB M H a : (mset B).map (B' M H a) ≫ eP.hom.app H =
      f.adj.homEquiv _ _ (eI.inv.app M ≫ (mset RI).map a) := by
    rw [restrictHomEquiv_map]
    exact (mateIsoEquiv_equation f.adj (eI.app M) (eP.app H) _).symm
  have hBL {M N} (a : M ⟶ N) H b :
      B' M H (I.modules.map a ≫ b) = a ≫ B' N H b := by
    apply (mset B).map_injective
    apply (cancel_mono (eP.hom.app H)).mp
    rw [hB, (mset B).map_comp, Category.assoc, hB, (mset RI).map_comp]
    have hn : eI.inv.app M ≫ (mset RI).map (I.modules.map a) =
        f.inverse.map ((mset B).map a) ≫ eI.inv.app N := (eI.inv.naturality a).symm
    rw [← Category.assoc, hn, Category.assoc, f.adj.homEquiv_naturality_left]
  have hBR M {H H'} a (b : H ⟶ H') :
      B' M H' (a ≫ (restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).map c)).map b) = B' M H a ≫ f.modules.map b := by
    apply (mset B).map_injective
    apply (cancel_mono (eP.hom.app H')).mp
    rw [hB, (mset B).map_comp, Category.assoc]
    have hn : (mset B).map (f.modules.map b) ≫ eP.hom.app H' =
        eP.hom.app H ≫ f.direct.map ((mset A).map b) := eP.hom.naturality b
    rw [hn, ← Category.assoc, hB, (mset RI).map_comp]
    change f.adj.homEquiv _ _ (eI.inv.app M ≫
      ((mset RI).map a ≫ (mset A).map b)) = _
    rw [← Category.assoc, f.adj.homEquiv_naturality_right]
  let T := I.modules ⋙ tensorFunctor c
  let E' : ∀ M H, (T.obj M ⟶ H) ≃ (M ⟶ f.modules.obj H) :=
    fun M H ↦ ((tensorAdjunction c).homEquiv (I.modules.obj M) H).trans (B' M H)
  have hEL {M N} (a : M ⟶ N) H (b : T.obj N ⟶ H) :
      E' M H (T.map a ≫ b) = a ≫ E' N H b := by
    dsimp only [E', Equiv.trans_apply, T, Functor.comp_map]
    change B' M H ((tensorAdjunction c).homEquiv (I.modules.obj M) H
      ((tensorFunctor c).map (I.modules.map a) ≫ b)) = _
    rw [(tensorAdjunction c).homEquiv_naturality_left, hBL]
    rfl
  exact ⟨Adjunction.mkOfHomEquiv {
    homEquiv := E'
    homEquiv_naturality_left_symm := by
      intro M N H a b
      apply (E' M H).injective
      rw [Equiv.apply_symm_apply, hEL, Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M H H' a b
      dsimp only [E', Equiv.trans_apply]
      change B' M H' ((tensorAdjunction c).homEquiv (I.modules.obj M) H' (a ≫ b)) = _
      rw [(tensorAdjunction c).homEquiv_naturality_right]
      exact hBR M ((tensorAdjunction c).homEquiv (I.modules.obj M) H a) b }⟩

open MonoidalCategory
section FlatComparison
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
end FlatComparison

namespace CategoryTheory

end CategoryTheory
