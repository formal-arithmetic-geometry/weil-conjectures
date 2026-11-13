/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.AlgebraicGeometry.ConstantPullbackScalar
import WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import WeilConjectures.AlgebraicGeometry.RestrictionSectionCompleteness
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal

set_option linter.privateModule false

/-!
# Completed pullback is left adjoint to direct image

Source: Stacks Project, `proetale.tex`, Tags 099M and 099N (1), (2), and
`algebraization.tex`, Tag 099K.

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

end CategoryTheory.ConstantCompletion
