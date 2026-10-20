/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import all Sheaf.CategoryTheory.RingedToposKFlatPullback
import all Sheaf.CategoryTheory.GeometricModuleConstruction
import all Sheaf.CategoryTheory.GeometricModuleTransport
import all Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.ExactPullbackDerivedAdjunction
import Sheaf.Paper.ConstantDirectImagePreservesComplete

/-!
# Completed pullback is left adjoint to direct image

Source: Stacks Project, `proetale.tex`, Tags 099M and 099N (1), (2), and
`algebraization.tex`, Tag 099K
(blueprint: lem-sp-completed-pullback-adjunction).

All coefficient sheaves, local-completeness predicates and quotient-tower completions
are the constructions of `ConstantCompletionEquivalence`. Positive exponents are n+1.
The existential witnesses below specify geometric module direct image and its total
right derived functor by their underlying maps and universal comparisons. In particular
no preservation or adjunction on complete objects is an assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ConstantCompletion



set_option maxHeartbeats 600000 in
-- The normalized module Hom equivalence elaborates the two transported operation diagrams.
open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem supplied_module_adjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K) (base A) (base B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
      I.ringUnderlying.inv ≫ f.ringMap) :
    ∃ am : I.modules ⋙ tensorFunctor c ⊣ f.modules,
      ∀ M H k, (underlying B).map (am.homEquiv M H k) ≫ f.underlying.hom.app H =
        f.adj.homEquiv ((underlying B).obj M) ((underlying A).obj H)
          (I.moduleUnderlying.inv.app M ≫ tensorUnit c (I.modules.obj M) ≫
            (underlying A).map k) := by
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
  let am : T ⊣ f.modules := Adjunction.mkOfHomEquiv {
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
      exact hBR M ((tensorAdjunction c).homEquiv (I.modules.obj M) H a) b }
  refine ⟨am, ?_⟩
  intro M H k
  dsimp only [am]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change (underlying B).map (B' M H
    ((tensorAdjunction c).homEquiv (I.modules.obj M) H k)) ≫ eP.hom.app H = _
  rw [hB, tensorAdjunction_underlying]
  rfl

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem module_adjunction_exists
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)}
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    {R : Sheaf JC CommRingCat.{u}} {S : Sheaf JD CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) :
    ∃ (G : Mod S ⥤+ Mod R)
      (eG : G.obj ⋙ underlying R ≅ underlying S ⋙ V) (aM : pull F c ⊣ G.obj),
      ∀ M N f, (underlying R).map (aM.homEquiv M N f) ≫ eG.hom.app N =
        adj.homEquiv ((underlying R).obj M) ((underlying S).obj N)
          (pullInsertion F c M ≫ (underlying S).map f) := by
  let AI := F.algebra R
  let d : RingedToposMorphism.RingData (siteModuleRings S) (siteModuleRings R) :=
    { inverse := L
      direct := V
      adj := adj
      leftExact := inferInstance
      ringMap := AI.ringUnderlying.hom ≫ (sheafCompose JD (forget CommRingCat)).map c
      ring_zero := by
        intro T z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) = 0
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringZero T z hz U t)).trans (map_zero _)
      ring_one := by
        intro T z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) = 1
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringOne T z hz U t)).trans (map_one _)
      ring_add := by
        intro T x y z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) =
          (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map x).hom.app U t)) +
            (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map y).hom.app U t))
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringAdd T x y z hz U t)).trans (map_add _ _ _)
      ring_mul := by
        intro T x y z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) =
          (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map x).hom.app U t)) *
            (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map y).hom.app U t))
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringMul T x y z hz U t)).trans (map_mul _ _ _) }
  obtain ⟨md⟩ := ringData_inducedModules S R d
  let f := d.withModules md
  let : f.modules.Additive := f.additive
  have hc : (sheafCompose JD (forget CommRingCat)).map c =
      AI.ringUnderlying.inv ≫ f.ringMap := by
    change _ = AI.ringUnderlying.inv ≫
      (AI.ringUnderlying.hom ≫ (sheafCompose JD (forget CommRingCat)).map c)
    simp only [Iso.inv_hom_id_assoc]
  obtain ⟨aM, haM⟩ := supplied_module_adjunction f (F.rings.obj R) AI c hc
  refine ⟨AdditiveFunctor.of f.modules, f.underlying, aM, ?_⟩
  intro M N k
  refine (haM M N k).trans ?_
  have hq : insertion c (AI.modules.obj M) = tensorUnit c (AI.modules.obj M) := by
    ext U m
    exact ((insertion_existsUnique c (AI.modules.obj M)).exists.choose_spec U m).trans
      (tensorUnit_apply c (AI.modules.obj M) U m).symm
  dsimp only [pullInsertion]
  rw [hq, Category.assoc]
  rfl

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictScalars_equivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (c : R ≅ S) :
    (restrictScalars.{u} c.hom).IsEquivalence := by
  let ec : C ≌ C := Equivalence.refl
  have : ec.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : ec.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e := pushforwardPushforwardEquivalence (J := J) (K := J)
    ec c.hom c.inv
    (by
      ext U x
      dsimp [ec, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f : S ⟶ S ↦ f.hom.app U x) c.inv_hom_id.symm)
    (by
      ext U x
      dsimp [ec, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f : R ⟶ R ↦ f.hom.app U x) c.hom_inv_id)
  have h : restrictScalars.{u} c.hom = e.functor := by rfl
  rw [h]
  exact e.isEquivalence_functor

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pull_finiteLimits_of_isIso
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)} [PreservesFiniteLimits L]
    (F : InverseImageData L)
    {R : Sheaf JC CommRingCat.{u}} {S : Sheaf JD CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) [IsIso c] : PreservesFiniteLimits (pull F c) := by
  let r := sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})
  have : (restriction c).IsEquivalence :=
    restrictScalars_equivalence (r.mapIso (asIso c))
  have := (tensorAdjunction c).isEquivalence_left_of_isEquivalence_right
  have := algebraicInverseImage_finiteLimits L (F.algebra R)
  exact comp_preservesFiniteLimits (F.algebra R).modules (tensorFunctor c)

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reflector_of_bijective
    {B : Type*} [Category B] (P : ObjectProperty B) (T : B ⥤ B)
    (η : 𝟭 B ⟶ T) (hT : ∀ X, P (T.obj X))
    (hbij : ∀ X Y, P Y → Function.Bijective (fun f : T.obj X ⟶ Y ↦ η.app X ≫ f)) :
    ∃ a : ObjectProperty.lift P T hT ⊣ P.ι,
      ∀ X Y f, a.homEquiv X Y f = η.app X ≫ f.hom := by
  classical
  let E : ∀ X (Y : P.FullSubcategory),
      ((ObjectProperty.lift P T hT).obj X ⟶ Y) ≃ (X ⟶ Y.obj) :=
    fun X Y ↦ P.fullyFaithfulι.homEquiv.trans
      (Equiv.ofBijective (fun f ↦ η.app X ≫ f) (hbij X Y.obj Y.property))
  have hEL {X X' : B} (a : X ⟶ X') (Y : P.FullSubcategory)
      (f : (ObjectProperty.lift P T hT).obj X' ⟶ Y) :
      E X Y ((ObjectProperty.lift P T hT).map a ≫ f) = a ≫ E X' Y f := by
    change η.app X ≫ T.map a ≫ f.hom = a ≫ η.app X' ≫ f.hom
    rw [← Category.assoc, ← η.naturality]
    simp only [Category.assoc, Functor.id_map]
  let core : Adjunction.CoreHomEquiv (ObjectProperty.lift P T hT) P.ι :=
    { homEquiv := E
      homEquiv_naturality_left_symm := by
        intro X X' Y a g
        apply (E X Y).injective
        calc
          _ = a ≫ g := (E X Y).apply_symm_apply _
          _ = _ := by
            rw [hEL]
            exact congrArg (fun t ↦ a ≫ t) ((E X' Y).apply_symm_apply g).symm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        change η.app X ≫ f.hom ≫ g.hom = (η.app X ≫ f.hom) ≫ g.hom
        simp only [Category.assoc] }
  refine ⟨Adjunction.mkOfHomEquiv core, ?_⟩
  intro X Y f
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem complete_adjunction
    {B D' : Type*} [Category B] [Category D']
    (P : ObjectProperty B) (P' : ObjectProperty D')
    (F : B ⥤ D') (G : D' ⥤ B) (a : F ⊣ G)
    (T : D' ⥤ D') (η : 𝟭 D' ⟶ T) (hT : ∀ X, P' (T.obj X))
    (hG : ∀ Y, P' Y → P (G.obj Y))
    (aT : ObjectProperty.lift P' T hT ⊣ P'.ι)
    (haT : ∀ X Y f, aT.homEquiv X Y f = η.app X ≫ f.hom) :
    ∃ a' : ObjectProperty.lift P' (P.ι ⋙ F ⋙ T) (fun X ↦ hT (F.obj X.obj)) ⊣
        ObjectProperty.lift P (P'.ι ⋙ G) (fun Y ↦ hG Y.obj Y.property),
      ∀ M N (f : T.obj (F.obj M.obj) ⟶ N.obj),
        (a'.homEquiv M N (ObjectProperty.homMk f)).hom =
          a.homEquiv M.obj N.obj (η.app (F.obj M.obj) ≫ f) := by
  let LF := ObjectProperty.lift P' (P.ι ⋙ F ⋙ T) (fun X ↦ hT (F.obj X.obj))
  let RG := ObjectProperty.lift P (P'.ι ⋙ G) (fun Y ↦ hG Y.obj Y.property)
  let E : ∀ M N, (LF.obj M ⟶ N) ≃ (M ⟶ RG.obj N) :=
    fun M N ↦ (aT.homEquiv (F.obj M.obj) N).trans
      ((a.homEquiv M.obj N.obj).trans (P.fullyFaithfulι.homEquiv (X := M) (Y := RG.obj N)).symm)
  have hE (M : P.FullSubcategory) (N : P'.FullSubcategory) (f : LF.obj M ⟶ N) :
      (E M N f).hom = a.homEquiv M.obj N.obj (η.app (F.obj M.obj) ≫ f.hom) := by
    exact congrArg (a.homEquiv M.obj N.obj) (haT _ _ f)
  have hEL {M M' : P.FullSubcategory} (b : M ⟶ M') (N : P'.FullSubcategory)
      (f : LF.obj M' ⟶ N) : E M N (LF.map b ≫ f) = b ≫ E M' N f := by
    apply ObjectProperty.hom_ext
    change (E M N (LF.map b ≫ f)).hom = b.hom ≫ (E M' N f).hom
    rw [hE, hE]
    change a.homEquiv _ _ (η.app (F.obj M.obj) ≫ T.map (F.map b.hom) ≫ f.hom) = _
    rw [← Category.assoc, ← η.naturality, Functor.id_map, Category.assoc,
      a.homEquiv_naturality_left]
  let core : Adjunction.CoreHomEquiv LF RG :=
    { homEquiv := E
      homEquiv_naturality_left_symm := by
        intro M M' N b g
        apply (E M N).injective
        simp only [hEL, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro M N N' f b
        apply ObjectProperty.hom_ext
        change (E M N' (f ≫ b)).hom = (E M N f).hom ≫ G.map b.hom
        rw [hE, hE]
        change a.homEquiv _ _ (η.app (F.obj M.obj) ≫ f.hom ≫ b.hom) =
          a.homEquiv _ _ (η.app (F.obj M.obj) ≫ f.hom) ≫ G.map b.hom
        rw [← Category.assoc, a.homEquiv_naturality_right] }
  refine ⟨Adjunction.mkOfHomEquiv core, ?_⟩
  intro M N f
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  exact hE M N (ObjectProperty.homMk f)

open SheafOfModules SheafOfModules.GeometricConstruction in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completion_reflector
    {B : Type u} [SmallCategory B] (J : GrothendieckTopology B)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ (h : ∀ M : D (constant J A),
        IsComplete (quotient J A I 0) ((completion J A I false).obj M))
      (a : ObjectProperty.lift (IsComplete (quotient J A I 0))
        (completion J A I false) h ⊣ ObjectProperty.ι (IsComplete (quotient J A I 0))),
      ∀ M N f, a.homEquiv M N f = (completionUnit J A I false).app M ≫ f.hom := by
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing I)
  obtain ⟨K, _, h, hbij, _⟩ := koszul_quotient_reflector J A I false r a ha
  change ∀ M : D (constant J A),
    IsComplete (quotient J A I 0) ((completion J A I false).obj M) at h
  change ∀ M N : D (constant J A), IsComplete (quotient J A I 0) N →
    Function.Bijective (fun f : (completion J A I false).obj M ⟶ N ↦
      (completionUnit J A I false).app M ≫ f) at hbij
  obtain ⟨a, ha⟩ := reflector_of_bijective (IsComplete (quotient J A I 0))
    (completion J A I false) (completionUnit J A I false) h hbij
  exact ⟨h, a, ha⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- For arbitrary small sites and Noetherian coefficients, quotient-tower completion is
left adjoint to inclusion of the locally derived-complete objects. Derived direct image
preserves these objects, and completed inverse image is its left adjoint. The ordinary
module Hom equivalence is normalized by the given geometric adjunction and insertion
of 1 in scalar extension. Its derived version is normalized on K-flat source and
K-injective target representatives. Finally the complete Hom equivalence is exactly
completion-unit precomposition followed by this ordinary derived Hom equivalence.

Source: Stacks Project, Tags 099M, 099N (1), (2), 099K, and 07A6
(blueprint: lem-sp-completed-pullback-adjunction).

Proof:
1. Apply lem-weil-pbc-ringed-topoi-module-adjunction to the geometric adjunction and
   its canonical identification of constant rings. Its tensor pullback is `pull F
   (constantMap F A)`. Inverse image is exact. Functorial K-injective resolutions
   (prop-pur-kinjective-resolutions-exist) and preservation of K-injectives by the
   right adjoint (lem-weil-pbc-right-adjoint-preserves-kinjective) give the total
   derived direct image. The termwise adjunction descends to the ordinary derived
   adjunction, by lem-weil-pbc-kinjective-hom-derived. This yields its normalization.
2. Noetherianness gives finitely many ideal generators, including the empty list for
   I=0. Apply lem-weil-pbc-ringed-koszul-completion-reflector on both sites. The
   unit-preserving Koszul/quotient comparison of
   lem-weil-pbc-constant-completion-equivalence identifies the reflectors with the
   actual strict quotient-tower completions and their specified units.
3. For any scalar a form the constant strict multiplication tower on a representative
   of H. Exact slice restriction has an exact left adjoint by
   lem-pur-site-restriction-module-adjunction-exact. Levelwise restriction therefore
   preserves K-injective tower complexes and commutes with ordinary inverse limits.
   Consequently it commutes with the strict derived limit. By
   lem-weil-pbc-local-hom-tower-criterion, vanishing of that multiplication-tower
   limit is equivalent to the local RHom vanishing condition on every slice. The
   converse is detected by the cohomology sheaves on all slice terminal objects.
4. For complete N apply lem-weil-ringed-tower-pushforward-limit-comparison to each
   generator's multiplication tower. On a K-injective representative J, comparison
   with a K-injective tower resolution is levelwise a quasi-isomorphism between
   K-injectives: evaluation has the exact left adjoint supported at positions up to
   n. Such maps are homotopy equivalences, so additive direct image preserves them.
   This identifies the whole image tower, including scalar transitions, with the
   multiplication tower of RF(N). Its limit vanishes. Step 3 and
   lem-weil-pbc-ringed-derived-complete-elements-ideal give vanishing for every local
   section of I times the constant ring sheaf. Thus RF preserves completeness.
5. For complete M,N, precompose a map completion(LF(M)) → N with the completion
   unit, then use the ordinary derived Hom equivalence. Both bijections are natural;
   fullness identifies them with the actual Hom sets of the complete categories.
6. The resulting unit is the ordinary unit followed by RF of the completion unit.
   Its counit is the unique extension of the ordinary counit across the completion
   unit. Naturality follows from the two Hom bijections; their inverse identities
   give the triangle identities. The last equation fixes precisely these choices. -/
theorem completedPullbackAdjunction
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology E)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : L ⊣ V) [PreservesFiniteLimits L] :
    ∃ (F : InverseImageData L)
      (G : Mod (constant JD A) ⥤+ Mod (constant JC A))
      (eG : G.obj ⋙ underlying (constant JC A) ≅ underlying (constant JD A) ⋙ V)
      (aM : pull F (constantMap F A) ⊣ G.obj),
      (∀ (M : Mod (constant JC A)) (N : Mod (constant JD A))
        (f : (pull F (constantMap F A)).obj M ⟶ N),
        (underlying (constant JC A)).map (aM.homEquiv M N f) ≫ eG.hom.app N =
          adj.homEquiv ((underlying (constant JC A)).obj M)
            ((underlying (constant JD A)).obj N)
            (pullInsertion F (constantMap F A) M ≫
              (underlying (constant JD A)).map f)) ∧
      PreservesFiniteLimits (pull F (constantMap F A)) ∧
      PreservesFiniteColimits (pull F (constantMap F A)) ∧
      ∃ (RF : D (constant JD A) ⥤ D (constant JC A))
        (ηG : G.obj.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q (constant JC A) ⟶
          Q (constant JD A) ⋙ RF),
        RF.IsRightDerivedFunctor ηG
            (HomologicalComplex.quasiIso (Mod (constant JD A)) (ComplexShape.up ℤ)) ∧
        (∀ J : Cx (constant JD A), J.IsKInjective → IsIso (ηG.app J)) ∧
        ∃ aD : (derivedPull F V adj (constantMap F A)).functor ⊣ RF,
          (∀ (P : Cx (constant JC A)) (J : Cx (constant JD A)),
            P.IsAcyclicTensorKFlat → (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → J.IsKInjective →
            ∀ f : ((pull F (constantMap F A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P ⟶ J,
              aD.homEquiv ((Q (constant JC A)).obj P) ((Q (constant JD A)).obj J)
                ((derivedPull F V adj (constantMap F A)).comparison.app P ≫
                  (Q (constant JD A)).map f) =
                (Q (constant JC A)).map
                  ((aM.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv P J f) ≫
                    ηG.app J) ∧
          ∃ (hC : ∀ M : D (constant JC A),
              IsComplete (quotient JC A I 0) ((completion JC A I false).obj M))
            (hD : ∀ M : D (constant JD A),
              IsComplete (quotient JD A I 0) ((completion JD A I false).obj M))
            (hG : ∀ N : D (constant JD A), IsComplete (quotient JD A I 0) N →
              IsComplete (quotient JC A I 0) (RF.obj N))
            (aC : ObjectProperty.lift (IsComplete (quotient JC A I 0))
              (completion JC A I false) hC ⊣
              ObjectProperty.ι (IsComplete (quotient JC A I 0)))
            (aDCompletion : ObjectProperty.lift (IsComplete (quotient JD A I 0))
              (completion JD A I false) hD ⊣ ObjectProperty.ι (IsComplete (quotient JD A I 0))),
            (∀ (M : D (constant JC A))
              (N : ObjectProperty.FullSubcategory (IsComplete (quotient JC A I 0)))
              (f : (ObjectProperty.lift (IsComplete (quotient JC A I 0))
                (completion JC A I false) hC).obj M ⟶ N),
              aC.homEquiv M N f = (completionUnit JC A I false).app M ≫ f.hom) ∧
            (∀ (M : D (constant JD A))
              (N : ObjectProperty.FullSubcategory (IsComplete (quotient JD A I 0)))
              (f : (ObjectProperty.lift (IsComplete (quotient JD A I 0))
                (completion JD A I false) hD).obj M ⟶ N),
              aDCompletion.homEquiv M N f =
                (completionUnit JD A I false).app M ≫ f.hom) ∧
            ∃ aComplete :
              ObjectProperty.lift (IsComplete (quotient JD A I 0))
                (ObjectProperty.ι (IsComplete (quotient JC A I 0)) ⋙
                  (derivedPull F V adj (constantMap F A)).functor ⋙ completion JD A I false)
                (fun M ↦ hD ((derivedPull F V adj (constantMap F A)).functor.obj M.obj)) ⊣
              ObjectProperty.lift (IsComplete (quotient JC A I 0))
                (ObjectProperty.ι (IsComplete (quotient JD A I 0)) ⋙ RF)
                (fun N ↦ hG N.obj N.property),
              ∀ (M : ObjectProperty.FullSubcategory (IsComplete (quotient JC A I 0)))
                (N : ObjectProperty.FullSubcategory (IsComplete (quotient JD A I 0)))
                (f : (completion JD A I false).obj
                  ((derivedPull F V adj (constantMap F A)).functor.obj M.obj) ⟶ N.obj),
                (aComplete.homEquiv M N (ObjectProperty.homMk f)).hom =
                  aD.homEquiv M.obj N.obj
                    ((completionUnit JD A I false).app
                      ((derivedPull F V adj (constantMap F A)).functor.obj M.obj) ≫ f) := by
  classical
  obtain ⟨F⟩ := inverseImageData_exists L V adj
  obtain ⟨G, eG, aM, haM⟩ := module_adjunction_exists V adj F (constantMap F A)
  have : IsIso (constantMap F A) := by
    dsimp only [constantMap]
    infer_instance
  have hlim := pull_finiteLimits_of_isIso F (constantMap F A)
  have hcolim : PreservesFiniteColimits (pull F (constantMap F A)) := by
    have := aM.leftAdjoint_preservesColimits
    infer_instance
  obtain ⟨RF, ηG, hRF, hηG, aD, haD⟩ :=
    exactPullbackDerivedAdjunction V adj F (constantMap F A) G aM
  obtain ⟨hC, aC, haC⟩ := completion_reflector JC A I
  obtain ⟨hD, aDC, haDC⟩ := completion_reflector JD A I
  have hG := constantDirectImage_preservesComplete JC JD A I V adj F G aM
    RF ηG hRF hηG
  refine ⟨F, G, eG, aM, haM, hlim, hcolim, RF, ηG, hRF, hηG, aD, haD,
    hC, hD, hG, aC, aDC, haC, haDC, ?_⟩
  exact complete_adjunction (IsComplete (quotient JC A I 0))
    (IsComplete (quotient JD A I 0)) (derivedPull F V adj (constantMap F A)).functor RF aD
    (completion JD A I false) (completionUnit JD A I false) hD hG aDC haDC

end CategoryTheory.ConstantCompletion
