/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.Flat
import all Sheaf.CategoryTheory.RingedToposKFlatPullback
import all Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import all Sheaf.CategoryTheory.GeometricModuleConstruction
import all Sheaf.CategoryTheory.GeometricModuleTransport
import all Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all Sheaf.Paper.KFlatRingedToposPullback
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

/-! # Flat K-flat complexes under continuous module inverse image

Source: Stacks Project, Tag 0G7E.
(blueprint: lem-trf-continuous-module-pullback-kflat).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v d z w
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules


namespace ContinuousPullbackProof
open GeometricConstruction
private structure PullbackData
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{w}) (B : Sheaf K RingCat.{w}) where
  /-- Inverse image of sheaves of sets. -/
  inverse : Sheaf K (Type w) ⥤ Sheaf J (Type w)
  /-- Direct image of sheaves of sets. -/
  direct : Sheaf J (Type w) ⥤ Sheaf K (Type w)
  /-- The geometric adjunction. -/
  adj : inverse ⊣ direct
  /-- Left exactness is required only for the underlying inverse image. -/
  leftExact : PreservesFiniteLimits inverse
  /-- The structural map, with ring structure specified by generalized elements below. -/
  ringMap : inverse.obj ((sheafCompose K (CategoryTheory.forget RingCat.{w})).obj B) ⟶
    (sheafCompose J (CategoryTheory.forget RingCat.{w})).obj A
  /-- Preservation of zero. -/
  ring_zero : ∀ (T : Sheaf K (Type w))
    (z : T ⟶ (sheafCompose K (CategoryTheory.forget RingCat.{w})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Zero.zero (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @Zero.zero (A.obj.obj U) inferInstance
  /-- Preservation of one. -/
  ring_one : ∀ (T : Sheaf K (Type w))
    (z : T ⟶ (sheafCompose K (CategoryTheory.forget RingCat.{w})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @One.one (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @One.one (A.obj.obj U) inferInstance
  /-- Preservation of add. -/
  ring_add : ∀ (T : Sheaf K (Type w))
    (x y z : T ⟶ (sheafCompose K (CategoryTheory.forget RingCat.{w})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Add.add (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- Preservation of mul. -/
  ring_mul : ∀ (T : Sheaf K (Type w))
    (x y z : T ⟶ (sheafCompose K (CategoryTheory.forget RingCat.{w})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Mul.mul (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Mul.mul (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- The induced direct image on module sheaves. -/
  modules : ringedSiteModules.{w} A ⥤ ringedSiteModules.{w} B
  /-- Additivity of the induced direct image. -/
  additive : modules.Additive
  /-- The underlying direct image of sheaves of sets, naturally in the module. -/
  underlying :
    modules ⋙ SheafOfModules.toSheaf B ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w}) ≅
      (SheafOfModules.toSheaf A ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})) ⋙ direct
  /-- Addition and the structural-map-induced scalar action, under adjunction. -/
  module_linear : ∀ (M : ringedSiteModules.{w} A) (T : Sheaf K (Type w))
    (a : T ⟶ (sheafCompose K (CategoryTheory.forget RingCat.{w})).obj B)
    (x y z : T ⟶ (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{w})).obj
      ((SheafOfModules.toSheaf B).obj (modules.obj M))),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((modules.obj M).val.obj U) inferInstance
        (@SMul.smul (B.obj.obj U) ((modules.obj M).val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((adj.homEquiv T _).symm (z ≫ underlying.hom.app M)).hom.app U t =
        @Add.add (M.val.obj U) inferInstance
          (@SMul.smul (A.obj.obj U) (M.val.obj U) inferInstance
            (((inverse.map a) ≫ ringMap).hom.app U t)
            (((adj.homEquiv T _).symm (x ≫ underlying.hom.app M)).hom.app U t))
          (((adj.homEquiv T _).symm (y ≫ underlying.hom.app M)).hom.app U t)


attribute [local instance] PullbackData.additive
private theorem graph_sections
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {X Y Z T : Sheaf J (Type w)} {A B E : Sheaf K (Type w)}
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
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {X Y Z : Sheaf J (Type w)} {A B E : Sheaf K (Type w)}
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
    (hgraph : ∀ (T : Sheaf J (Type w)) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
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
    {C : Type c} [Category.{v} C]
    [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    {X Y Z A B E : Sheaf J (Type w)}
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
    {C : Type c} [Category.{v} C]
    [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) := fromProd (rset R) (rset R) ≫ ringAdd R

private noncomputable abbrev rmul
    {C : Type c} [Category.{v} C]
    [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) := fromProd (rset R) (rset R) ≫ ringMul R

private theorem structural_map
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Sheaf J CommRingCat.{w}) (B : Sheaf K CommRingCat.{w})
    (f : PullbackData (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (RI : Sheaf J CommRingCat.{w}) (I : AlgebraicInverseImage f.inverse B RI) :
    ∃ c : RI ⟶ A, (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map c =
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
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{w}} {B : Sheaf K CommRingCat.{w}}
    (f : PullbackData (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (M : SheafOfModules.{w} (base A))
    (T : Sheaf K (Type w)) (x y z : T ⟶ (mset B).obj (f.modules.obj M))
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
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{w}} {B : Sheaf K CommRingCat.{w}}
    (f : PullbackData (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (M : SheafOfModules.{w} (base A))
    (T : Sheaf K (Type w)) (z : T ⟶ (mset B).obj (f.modules.obj M))
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
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{w}} {B : Sheaf K CommRingCat.{w}}
    (f : PullbackData (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (M : SheafOfModules.{w} (base A))
    (T : Sheaf K (Type w)) (a : T ⟶ rset B)
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
    {C : Type c} [Category.{v} C]
    [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R)) :=
  fromProd ((mset R).obj M) ((mset R).obj M) ≫ addition R M
private noncomputable abbrev msmul
    {C : Type c} [Category.{v} C]
    [EssentiallySmall.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (M : SheafOfModules.{w} (base R)) :=
  fromProd (rset R) ((mset R).obj M) ≫ action R M



private theorem h4_supplied_operations
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{w}} {B : Sheaf K CommRingCat.{w}}
    (f : PullbackData (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (H : SheafOfModules.{w} (base A)) :
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
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{w}} {B : Sheaf K CommRingCat.{w}}
    (f : PullbackData (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (RI : Sheaf J CommRingCat.{w}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map c =
      I.ringUnderlying.inv ≫ f.ringMap) :
    Nonempty (I.modules ⋙ CoefficientOrdinaryProof.tensorFunctor.{w, c, v} c ⊣ f.modules) := by
  let _ := f.leftExact
  let _ : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
  let eR := I.ringUnderlying.symm
  let eI := I.moduleUnderlying
  let eP := f.underlying
  have hec : eR.inv ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map c =
      f.ringMap := by
    rw [hc]
    simp only [eR, Iso.symm_inv, Iso.hom_inv_id_assoc]
  let E : ∀ M H, ((mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) ≃
      ((mset B).obj M ⟶ (mset B).obj (f.modules.obj H)) :=
    fun M H ↦ mateIsoEquiv f.adj (eI.app M) (eP.app H)
  have hImage M H (α : (mset RI).obj (I.modules.obj M) ⟶ (mset A).obj H) :
      (∃ a : I.modules.obj M ⟶ (restrictScalars ((sheafCompose J
        (forget₂ CommRingCat.{w} RingCat.{w})).map c)).obj H, (mset RI).map a = α) ↔
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
        (CategoryTheory.forget CommRingCat.{w})).map c))
      (eP.hom.app H) (eP.app H) (msmul B M) (msmul RI (I.modules.obj M))
      (msmul A H) (msmul B (f.modules.obj H)) hLS hRightSmul
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map c) α α
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
      (forget₂ CommRingCat.{w} RingCat.{w})).map c)).obj H) ≃ (M ⟶ f.modules.obj H) :=
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
        (forget₂ CommRingCat.{w} RingCat.{w})).map c)).map b) = B' M H a ≫ f.modules.map b := by
    apply (mset B).map_injective
    apply (cancel_mono (eP.hom.app H')).mp
    rw [hB, (mset B).map_comp, Category.assoc]
    have hn : (mset B).map (f.modules.map b) ≫ eP.hom.app H' =
        eP.hom.app H ≫ f.direct.map ((mset A).map b) := eP.hom.naturality b
    rw [hn, ← Category.assoc, hB, (mset RI).map_comp]
    change f.adj.homEquiv _ _ (eI.inv.app M ≫
      ((mset RI).map a ≫ (mset A).map b)) = _
    rw [← Category.assoc, f.adj.homEquiv_naturality_right]
  let T := I.modules ⋙ CoefficientOrdinaryProof.tensorFunctor.{w, c, v} c
  let E' : ∀ M H, (T.obj M ⟶ H) ≃ (M ⟶ f.modules.obj H) :=
    fun M H ↦ ((CoefficientOrdinaryProof.tensorAdjunction.{w, c, v} c).homEquiv (I.modules.obj M)
      H).trans (B' M H)
  have hEL {M N} (a : M ⟶ N) H (b : T.obj N ⟶ H) :
      E' M H (T.map a ≫ b) = a ≫ E' N H b := by
    dsimp only [E', Equiv.trans_apply, T, Functor.comp_map]
    change B' M H ((CoefficientOrdinaryProof.tensorAdjunction.{w, c, v} c).homEquiv (I.modules.obj
      M) H
      ((CoefficientOrdinaryProof.tensorFunctor.{w, c, v} c).map (I.modules.map a) ≫ b)) = _
    rw [(CoefficientOrdinaryProof.tensorAdjunction.{w, c, v} c).homEquiv_naturality_left, hBL]
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
      change B' M H' ((CoefficientOrdinaryProof.tensorAdjunction.{w, c, v} c).homEquiv
        (I.modules.obj M) H' (a ≫ b)) = _
      rw [(CoefficientOrdinaryProof.tensorAdjunction.{w, c, v} c).homEquiv_naturality_right]
      exact hBR M ((CoefficientOrdinaryProof.tensorAdjunction.{w, c, v} c).homEquiv (I.modules.obj
        M) H a) b }⟩
section
variable {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : D ⥤ C) [F.IsContinuous K J]
  (L : Sheaf K (Type w) ⥤ Sheaf J (Type w))
  (adj : L ⊣ F.sheafPushforwardContinuous (Type w) K J)

private def directPair {X Y : Sheaf J (Type w)} {T : Sheaf K (Type w)}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj Y) :
    T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj (X ⊗ Y) :=
  ⟨{ app U := ↾(fun t ↦ (x.hom.app U t, y.hom.app U t))
     naturality := by
       intro U V f
       ext t
       change (x.hom.app V (T.obj.map f t), y.hom.app V (T.obj.map f t)) =
         (X.obj.map (F.op.map f) (x.hom.app U t),
           Y.obj.map (F.op.map f) (y.hom.app U t))
       exact Prod.ext (CategoryTheory.congr_fun (x.hom.naturality f) t)
         (CategoryTheory.congr_fun (y.hom.naturality f) t) }⟩

omit [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] in
private theorem transpose_pair {X Y : Sheaf J (Type w)} {T : Sheaf K (Type w)}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj Y) :
    (adj.homEquiv T (X ⊗ Y)).symm (directPair F x y) =
      CartesianMonoidalCategory.lift ((adj.homEquiv T X).symm x)
        ((adj.homEquiv T Y).symm y) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst, ← adj.homEquiv_naturality_right_symm]
    rfl
  · rw [CartesianMonoidalCategory.lift_snd, ← adj.homEquiv_naturality_right_symm]
    rfl

omit [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] in
private theorem transpose_binary
    {X Y Z : Sheaf J (Type w)} {T : Sheaf K (Type w)} (op : X ⊗ Y ⟶ Z)
    (x : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj Y)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj Z)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U)
      (x.hom.app U t, y.hom.app U t)) :
    ∀ U t, ((adj.homEquiv T Z).symm z).hom.app U t =
      op.hom.app U (((adj.homEquiv T X).symm x).hom.app U t,
        ((adj.homEquiv T Y).symm y).hom.app U t) := by
  have he : z = directPair F x y ≫
      (F.sheafPushforwardContinuous (Type w) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm, transpose_pair F L adj]
  intro U t
  rfl

omit [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] in
private theorem transpose_constant
    {X : Sheaf J (Type w)} {T : Sheaf K (Type w)}
    (op : 𝟙_ (Sheaf J (Type w)) ⟶ X)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj X)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U) PUnit.unit) :
    ∀ U t, ((adj.homEquiv T X).symm z).hom.app U t = op.hom.app U PUnit.unit := by
  let w : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj (𝟙_ _) :=
    ⟨{ app U := ↾(fun _ ↦ PUnit.unit) }⟩
  have he : z = w ≫ (F.sheafPushforwardContinuous (Type w) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm]
  intro U t
  change op.hom.app U _ = _
  congr 1

open SheafOfModules.GeometricConstruction in
private noncomputable def siteContinuousRingedTopos
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
    (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} K J).obj R) :
    PullbackData (base R) (base S) := by
  let φR : base S ⟶ (F.sheafPushforwardContinuous RingCat.{w} K J).obj (base R) :=
    (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map φ
  let φs : rset S ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj (rset R) :=
    (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map φ
  let g := (adj.homEquiv (rset S) (rset R)).symm φs
  let P := SheafOfModules.pushforward.{w} (F := F) φR
  refine {
    inverse := L
    direct := F.sheafPushforwardContinuous (Type w) K J
    adj := adj
    leftExact := inferInstance
    ringMap := g
    ring_zero := ?_
    ring_one := ?_
    ring_add := ?_
    ring_mul := ?_
    modules := P
    additive := ?_
    underlying := Iso.refl _
    module_linear := ?_
  }
  · intro T z hz U t
    change T ⟶ rset S at z
    change ((L.map z) ≫ g).hom.app U t = (0 : R.obj.obj U)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm]
    let zeroR : 𝟙_ (Sheaf J (Type w)) ⟶ rset R :=
      ⟨{ app U := ↾(fun _ ↦ (0 : R.obj.obj U))
         naturality := by intro U V f; ext t; exact (R.obj.map f).hom.map_zero.symm }⟩
    apply transpose_constant F L adj zeroR (z ≫ φs) _ U t
    intro V x
    change (φ.hom.app V).hom (z.hom.app V x) = 0
    have h : (show S.obj.obj V from z.hom.app V x) = 0 := hz V x
    exact (congrArg (φ.hom.app V).hom h).trans (φ.hom.app V).hom.map_zero
  · intro T z hz U t
    change T ⟶ rset S at z
    change ((L.map z) ≫ g).hom.app U t = (1 : R.obj.obj U)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm]
    apply transpose_constant F L adj (ringOne R) (z ≫ φs) _ U t
    intro V x
    change (φ.hom.app V).hom (z.hom.app V x) = 1
    have h : (show S.obj.obj V from z.hom.app V x) = 1 := hz V x
    exact (congrArg (φ.hom.app V).hom h).trans (φ.hom.app V).hom.map_one
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Add.add (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (ringAdd R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') + (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') + (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_add _ _)
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Mul.mul (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (ringMul R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') * (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') * (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_mul _ _)
  · exact ⟨by intro M N a b; ext U x; rfl⟩
  · intro M T a x y z hz U t
    change T ⟶ rset S at a
    change T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj ((mset R).obj M)
      at x y z
    let ax : T ⟶ (F.sheafPushforwardContinuous (Type w) K J).obj ((mset R).obj M) :=
      CartesianMonoidalCategory.lift a x ≫ action S (P.obj M)
    have hAdd := transpose_binary F L adj (addition R M) ax y z
      (fun V x' ↦ hz V x') U t
    have hSmul := transpose_binary F L adj (action R M) (a ≫ φs) x ax
      (fun V x' ↦ rfl) U t
    change ((adj.homEquiv T _).symm z).hom.app U t = _
    rw [hAdd, hSmul]
    rw [adj.homEquiv_naturality_left_symm]
    rfl

end

end ContinuousPullbackProof

/-- Inverse image of modules along a flat continuous site functor preserves K-flat
complexes with flat terms; the coefficient universe contains the site universes.
Source: Stacks Project, Tag 0G7E, lemma-pullback-K-flat
(blueprint: lem-trf-continuous-module-pullback-kflat).

Proof: the flat continuous site functor induces a left exact inverse image of
set sheaves by Kan extension and sheafification. Reconstruct its algebraic inverse
image of the source ring and modules from the transported operations. Transpose
the structural ring map to obtain the map from this inverse-image ring to S.
The tensor adjunction, restricted to linear maps using the transported operation
graphs, identifies the resulting tensor pullback as left adjoint to the prescribed
module pushforward. Apply Tag 0G7E to that tensor pullback. Uniqueness of left
adjoints gives a natural isomorphism to L, and tensoring that complex isomorphism
transports the acyclic-test definition of K-flatness. -/
theorem continuousModulePullback_kFlat
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max w c v d z} C]
    {D : Type d} [Category.{z} D] [EssentiallySmall.{max w c v d z} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [RepresentablyFlat F]
    (R : Sheaf J CommRingCat.{max w c v d z}) (S : Sheaf K CommRingCat.{max w c v d z})
    (φ : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{max w c v d z} J K).obj S)
    (L : SheafOfModules.{max w c v d z} ((sheafCompose J (forget₂ CommRingCat.{max w c v d z}
      RingCat.{max w c v d z})).obj R) ⥤
      SheafOfModules.{max w c v d z} ((sheafCompose K (forget₂ CommRingCat.{max w c v d z}
        RingCat.{max w c v d z})).obj S))
    [L.Additive]
    (adj : L ⊣ pushforward.{max w c v d z}
      ((sheafCompose J (forget₂ CommRingCat.{max w c v d z} RingCat.{max w c v d z})).map φ))
    (P : CochainComplex
      (SheafOfModules.{max w c v d z} ((sheafCompose J (forget₂ CommRingCat.{max w c v d z}
        RingCat.{max w c v d z})).obj R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, IsFlatOnSite.{c, v, max w c v d z, max w c v d z} (J := J) (R := R) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
  let V := F.sheafPushforwardContinuous (Type (max w c v d z)) J K
  let U := Functor.sheafPullbackConstruction.sheafPullback F
    (Type (max w c v d z)) J K
  let a : U ⊣ V := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    (Type (max w c v d z)) J K
  have : AB5OfSize.{v, max c z} (Type (max w c v d z)) :=
    ⟨fun I _ _ ↦ ⟨inferInstance⟩⟩
  have : PreservesFiniteLimits (F.op.lan :
      (Cᵒᵖ ⥤ Type (max w c v d z)) ⥤ Dᵒᵖ ⥤ Type (max w c v d z)) :=
    CategoryTheory.preservesFiniteLimits_op_lan_of_flat F
  have : PreservesFiniteLimits U := by dsimp only [U]; infer_instance
  let p := ContinuousPullbackProof.siteContinuousRingedTopos F U a S R φ
  obtain ⟨RI, ⟨I⟩⟩ :=
    CategoryTheory.GeometricMorphism.algebraic_presentation_exists U R
  obtain ⟨c, hc⟩ := ContinuousPullbackProof.structural_map K J S R p RI I
  obtain ⟨b⟩ := ContinuousPullbackProof.supplied_adjunction p RI I c hc
  let G := I.modules ⋙ CoefficientOrdinaryProof.tensorFunctor.{max w c v d z, d, z} c
  have : PreservesColimits G := b.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts G
  have : G.Additive := Functor.additive_of_preservesBinaryBiproducts G
  have hobj M : G.obj M = changeOfRings c (I.modules.obj M) := rfl
  have hmap {M N} (g : M ⟶ N) : G.map g = eqToHom (hobj M) ≫
      changeOfRingsHom c (I.modules.obj M) (I.modules.map g) ≫ eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hk := (isKFlat_ringedToposPullback U V a I c G hobj hmap P hP hf).1
  let e : G ≅ L := b.leftAdjointUniq adj
  let eP := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  exact kFlat_iso_independent (R := S) eP hk

end SheafOfModules
