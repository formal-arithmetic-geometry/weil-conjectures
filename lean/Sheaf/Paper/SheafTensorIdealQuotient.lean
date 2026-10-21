/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IdealModuleQuotients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # Sheaf tensor with an ideal quotient

Source: Stacks Project, Modules on Sites, Tags 03EK and 03CY; the quotient identification
and naturality squares extracted in the DAG proof.
(blueprint: lem-weil-pbc-sheaf-tensor-ideal-quotient).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedSiteIdeal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

-- Saturated submodules and their explicit local finite-sum description.

private def subfunctor (F : SheafOfModules.{u} (siteModuleRings R))
    (N : F.val.Submodule) : Subfunctor (F.val.presheaf ⋙ forget AddCommGrpCat) where
  obj W := (N.obj W : Set (F.val.obj W))
  map f := fun _ hx ↦ N.map_mem f hx

private lemma saturated_sInf (F : SheafOfModules.{u} (siteModuleRings R))
    (s : Set F.val.Submodule) (hs : ∀ N ∈ s, IsSaturated F N) :
    IsSaturated F (sInf s) := by
  intro U x S hS hx
  simp only [PresheafOfModules.Submodule.sInf_obj, Submodule.mem_iInf]
  intro N hN
  exact hs N hN U x S hS fun V g hg ↦
    (show (sInf s).obj (op V) ≤ N.obj (op V) from (sInf_le hN) (op V)) (hx V g hg)

private lemma localProduct_saturated (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) : IsSaturated F (localProduct I F) :=
  saturated_sInf F _ fun _ h ↦ h.1

private lemma idealProduct_le (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (U : C) :
    I.sections U • (⊤ : Submodule (R.obj.obj (op U)) (F.val.obj (op U))) ≤
      (localProduct I F).obj (op U) := by
  intro x hx
  simp only [localProduct, PresheafOfModules.Submodule.sInf_obj, Submodule.mem_iInf]
  intro N hN
  exact hN.2 U hx

private lemma saturated_isSheaf (F : SheafOfModules.{u} (siteModuleRings R))
    (N : F.val.Submodule) (hN : IsSaturated F N) :
    Presheaf.IsSheaf J N.toPresheafOfModules.presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat)]
  rw [isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf J (subfunctor F N).toFunctor
  apply (Subfunctor.isSheaf_iff _
    ((Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat)).mp F.isSheaf |>
      (isSheaf_iff_isSheaf_of_type J _).mp)).mpr
  intro W x hx
  exact hN W.unop x _ hx fun V g hg ↦ hg

private noncomputable def idealProductPresheaf (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) : F.val.Submodule where
  obj W := I.sections W.unop • (⊤ : Submodule (R.obj.obj W) (F.val.obj W))
  map {W V} g := by
    intro x hx
    change F.val.map g x ∈ I.sections V.unop •
      (⊤ : Submodule (R.obj.obj V) (F.val.obj V))
    refine Submodule.smul_induction_on hx (fun r hr y _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [F.val.map_smul]
      exact Submodule.smul_mem_smul (I.restriction g.unop r hr) (Submodule.mem_top)
    · rw [map_add]
      exact Submodule.add_mem _ hx hy

private noncomputable def localHull (F : SheafOfModules.{u} (siteModuleRings R))
    (N : F.val.Submodule) : F.val.Submodule where
  obj W :=
    { carrier := ((subfunctor F N).sheafify J).obj W
      zero_mem' := by
        apply (subfunctor F N).le_sheafify J W
        exact (N.obj W).zero_mem
      add_mem' := by
        intro x y hx hy
        apply J.superset_covering _ (J.intersection_covering hx hy)
        intro V g hg
        change F.val.map g.op (x + y) ∈ N.obj (op V)
        rw [map_add]
        exact (N.obj _).add_mem hg.1 hg.2
      smul_mem' := by
        intro r x hx
        apply J.superset_covering _ hx
        intro V g hg
        change F.val.map g.op (r • x) ∈ N.obj (op V)
        rw [F.val.map_smul]
        exact (N.obj _).smul_mem _ hg }
  map g := ((subfunctor F N).sheafify J).map g

private lemma localHull_saturated (F : SheafOfModules.{u} (siteModuleRings R))
    (N : F.val.Submodule) : IsSaturated F (localHull F N) := by
  intro U x S hS hx
  apply J.transitive hS
  intro V g hg
  apply J.superset_covering _ (hx V g hg)
  intro Z k hk
  change F.val.map (k ≫ g).op x ∈ N.obj (op Z)
  change F.val.map k.op (F.val.map g.op x) ∈ N.obj (op Z) at hk
  simpa only [op_comp, PresheafOfModules.map_comp_apply] using hk

private lemma localProduct_eq_hull (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    localProduct I F = localHull F (idealProductPresheaf I F) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨localHull_saturated F _, fun U x hx ↦ ?_⟩
    exact (subfunctor F (idealProductPresheaf I F)).le_sheafify J (op U) hx
  · intro W x hx
    exact localProduct_saturated I F W.unop x _ hx
      fun V g hg ↦ idealProduct_le I F V hg

private lemma finite_sum_iff {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (m : M) :
    m ∈ I • (⊤ : Submodule A M) ↔
      ∃ (n : ℕ) (i : Fin n → I) (x : Fin n → M), m = ∑ k, (i k).val • x k := by
  classical
  constructor
  · intro hm
    refine Submodule.smul_induction_on hm (fun r hr y _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · exact ⟨1, fun _ ↦ ⟨r, hr⟩, fun _ ↦ y, by simp⟩
    · obtain ⟨n, i, x, rfl⟩ := hx
      obtain ⟨m, j, y, rfl⟩ := hy
      refine ⟨n + m, Fin.append i j, Fin.append x y, ?_⟩
      simp [Fin.sum_univ_add]
  · rintro ⟨n, i, x, rfl⟩
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem_smul (i k).property
      (Submodule.mem_top)

private lemma localProduct_membership (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (U : C) (f : F.val.obj (op U)) :
    f ∈ (localProduct I F).obj (op U) ↔
      ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
        ∃ (n : ℕ) (i : Fin n → I.sections V) (x : Fin n → F.val.obj (op V)),
          F.val.map g.op f = ∑ k : Fin n, (i k).val • x k := by
  rw [localProduct_eq_hull]
  constructor
  · intro h
    exact ⟨_, h, fun V g hg ↦ (finite_sum_iff _ _).mp hg⟩
  · rintro ⟨S, hS, h⟩
    apply J.superset_covering _ hS
    intro V g hg
    change F.val.map g.op f ∈ I.sections V •
      (⊤ : Submodule (R.obj.obj (op V)) (F.val.obj (op V)))
    exact (finite_sum_iff _ _).mpr (h V g hg)

-- Local representatives, the quotient kernel, and annihilation by the ideal.

private lemma cokernel_zero_iff (F : SheafOfModules.{u} (siteModuleRings R))
    (N : F.val.Submodule) (W : Cᵒᵖ) (f : F.val.obj W) :
    (cokernel.π N.ι).app W f = 0 ↔ f ∈ N.obj W := by
  let E := PresheafOfModules.evaluation (siteModuleRings R).obj W
  let e := PreservesCokernel.iso E N.ι ≪≫ ModuleCat.cokernelIsoRangeQuotient (N.ι.app W)
  have he : e.hom ((cokernel.π N.ι).app W f) =
      Submodule.Quotient.mk (p := (N.ι.app W).hom.range) f := by
    have h := congrArg (fun k ↦ k f) (PreservesCokernel.π_iso_hom E N.ι)
    change (ModuleCat.cokernelIsoRangeQuotient (N.ι.app W)).hom
      ((PreservesCokernel.iso E N.ι).hom ((cokernel.π N.ι).app W f)) = _
    change (PreservesCokernel.iso E N.ι).hom ((cokernel.π N.ι).app W f) =
      (cokernel.π (N.ι.app W)) f at h
    rw [h]
    exact congrArg (fun k ↦ k.hom f)
      (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (f := N.ι.app W))
  have hi := (ModuleCat.mono_iff_injective e.hom).mp (inferInstance : Mono e.hom)
  have hm : Submodule.Quotient.mk (p := (N.ι.app W).hom.range) f = 0 ↔ f ∈ N.obj W := by
    rw [Submodule.Quotient.mk_eq_zero]
    change f ∈ (N.obj W).subtype.range ↔ _
    rw [Submodule.range_subtype]
  constructor
  · intro h
    apply hm.mp
    rw [← he, h, map_zero]
  · intro h
    apply hi
    rw [he, hm.mpr h, map_zero]

private lemma projection_locallySurjective (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (moduleProjection I F).val) := by
  let P := PresheafOfModules.toPresheaf (siteModuleRings R).obj
  have : Presheaf.IsLocallySurjective J (P.map (cokernel.π (localProduct I F).ι)) :=
    Presheaf.isLocallySurjective_of_surjective J _ fun W ↦
      PresheafOfModules.surjective_of_epi (cokernel.π (localProduct I F).ι) W
  change Presheaf.IsLocallySurjective J
    (P.map (cokernel.π (localProduct I F).ι) ≫
      toSheafify J (moduleQuotientPresheaf I F).presheaf)
  have : Presheaf.IsLocallySurjective J
      (toSheafify J (moduleQuotientPresheaf I F).presheaf) :=
    (J.W_toSheafify (moduleQuotientPresheaf I F).presheaf).isLocallySurjective
  exact Presheaf.isLocallySurjective_comp J _ _

private lemma projection_zero_iff (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) (f : F.val.obj W) :
    (moduleProjection I F).val.app W f = 0 ↔ f ∈ (localProduct I F).obj W := by
  let P := moduleQuotientPresheaf I F
  let q := cokernel.π (localProduct I F).ι
  constructor
  · intro h
    have he : (toSheafify J P.presheaf).app W (q.app W f) =
        (toSheafify J P.presheaf).app W 0 := by
      exact h.trans (map_zero _).symm
    apply localProduct_saturated I F W.unop f _
      (Presheaf.equalizerSieve_mem J (toSheafify J P.presheaf) _ _ he)
    intro V g hg
    apply (cokernel_zero_iff F _ _ _).mp
    have hn := PresheafOfModules.naturality_apply q g.op f
    exact hn.trans (hg.trans (map_zero _))
  · intro h
    change (toSheafify J P.presheaf).app W (q.app W f) = 0
    rw [(cokernel_zero_iff F _ W f).mpr h, map_zero]

private lemma locallySurjective_epi {F G : SheafOfModules.{u} (siteModuleRings R)}
    (f : F ⟶ G) (hf : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map f.val)) : Epi f := by
  let := hf
  constructor
  intro H a b h
  ext W x
  apply H.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J
    ((PresheafOfModules.toPresheaf _).map f.val) x)
  rintro V g ⟨y, hy⟩
  change H.val.map g.op (a.val.app W x) = H.val.map g.op (b.val.app W x)
  change f.val.app (op V) y = G.val.map g.op x at hy
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  erw [← hy]
  exact congrArg (fun k : F ⟶ H ↦ k.val.app (op V) y) h

private lemma projection_epi (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) : Epi (moduleProjection I F) :=
  locallySurjective_epi _ (projection_locallySurjective I F)

private lemma quotient_annihilated (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) :
    Module.IsTorsionBySet (R.obj.obj W) ((moduleQuotient I F).val.obj W)
      (I.sections W.unop) := by
  intro m a
  let H := moduleQuotient I F
  let := projection_locallySurjective I F
  apply H.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J
    ((PresheafOfModules.toPresheaf _).map (moduleProjection I F).val) m)
  rintro V g ⟨f, hf⟩
  change H.val.map g.op (a.val • m) = H.val.map g.op 0
  change (moduleProjection I F).val.app (op V) f = H.val.map g.op m at hf
  rw [H.val.map_smul, map_zero]
  erw [← hf]
  rw [← ((moduleProjection I F).val.app (op V)).hom.map_smul]
  apply (projection_zero_iff I F _ _).mpr
  apply idealProduct_le I F V
  exact Submodule.smul_mem_smul (I.restriction g a.val a.property) Submodule.mem_top

-- Construct the scalar action over the quotient ring sheaf on the same abelian sheaf.

private noncomputable def annihilatedOverPresheaf (I : RingedSiteIdeal R)
    (H : SheafOfModules.{u} (siteModuleRings R))
    (hH : ∀ W : Cᵒᵖ, Module.IsTorsionBySet (R.obj.obj W) (H.val.obj W)
      (I.sections W.unop)) :
    PresheafOfModules.{u} (ringQuotientPresheaf I ⋙ forget₂ CommRingCat RingCat) := by
  letI : ∀ W : Cᵒᵖ, Module
      ((ringQuotientPresheaf I ⋙ forget₂ CommRingCat RingCat).obj W)
      (H.val.presheaf.obj W) :=
    fun W ↦ (hH W).module
  refine PresheafOfModules.ofPresheaf H.val.presheaf ?_
  intro X Y g r m
  induction r using Quotient.inductionOn' with
  | h r => exact H.val.map_smul g r m

private noncomputable def quotientSheafificationMap (I : RingedSiteIdeal R) :
    (ringQuotientPresheaf I ⋙ forget₂ CommRingCat RingCat) ⟶
      (siteModuleRings (ringQuotient I)).obj :=
  Functor.whiskerRight (toSheafify J (ringQuotientPresheaf I)) (forget₂ CommRingCat RingCat)

private lemma quotientSheafificationMap_inj (I : RingedSiteIdeal R) :
    Presheaf.IsLocallyInjective J (quotientSheafificationMap I) where
  equalizerSieve_mem x y h :=
    Presheaf.equalizerSieve_mem J (toSheafify J (ringQuotientPresheaf I)) x y h

attribute [local instance] quotientSheafificationMap_inj

private lemma quotientSheafificationMap_surj (I : RingedSiteIdeal R) :
    Presheaf.IsLocallySurjective J (quotientSheafificationMap I) where
  imageSieve_mem s := Presheaf.imageSieve_mem J (toSheafify J (ringQuotientPresheaf I)) s

attribute [local instance] quotientSheafificationMap_surj

private noncomputable def annihilatedUnderlyingMap (I : RingedSiteIdeal R)
    (H : SheafOfModules.{u} (siteModuleRings R))
    (hH : ∀ W : Cᵒᵖ, Module.IsTorsionBySet (R.obj.obj W) (H.val.obj W)
      (I.sections W.unop)) :
    (annihilatedOverPresheaf I H hH).presheaf ⟶ H.val.presheaf :=
  𝟙 H.val.presheaf

private lemma annihilatedUnderlyingMap_inj (I : RingedSiteIdeal R)
    (H : SheafOfModules.{u} (siteModuleRings R))
    (hH : ∀ W : Cᵒᵖ, Module.IsTorsionBySet (R.obj.obj W) (H.val.obj W)
      (I.sections W.unop)) :
    Presheaf.IsLocallyInjective J (annihilatedUnderlyingMap I H hH) :=
  Presheaf.isLocallyInjective_of_injective J _ fun _ ↦ Function.injective_id

attribute [local instance] annihilatedUnderlyingMap_inj

private lemma annihilatedUnderlyingMap_surj (I : RingedSiteIdeal R)
    (H : SheafOfModules.{u} (siteModuleRings R))
    (hH : ∀ W : Cᵒᵖ, Module.IsTorsionBySet (R.obj.obj W) (H.val.obj W)
      (I.sections W.unop)) :
    Presheaf.IsLocallySurjective J (annihilatedUnderlyingMap I H hH) :=
  Presheaf.isLocallySurjective_of_surjective J _ fun _ ↦ Function.surjective_id

attribute [local instance] annihilatedUnderlyingMap_surj

private noncomputable def annihilatedOverSheaf (I : RingedSiteIdeal R)
    (H : SheafOfModules.{u} (siteModuleRings R))
    (hH : ∀ W : Cᵒᵖ, Module.IsTorsionBySet (R.obj.obj W) (H.val.obj W)
      (I.sections W.unop)) :
    SheafOfModules.{u} (siteModuleRings (ringQuotient I)) :=
  PresheafOfModules.sheafify (quotientSheafificationMap I)
    (M₀ := annihilatedOverPresheaf I H hH) (A := (SheafOfModules.toSheaf _).obj
      H) (annihilatedUnderlyingMap I H hH)

private lemma annihilatedOverSheaf_smul (I : RingedSiteIdeal R)
    (H : SheafOfModules.{u} (siteModuleRings R))
    (hH : ∀ W : Cᵒᵖ, Module.IsTorsionBySet (R.obj.obj W) (H.val.obj W)
      (I.sections W.unop)) (W : Cᵒᵖ)
    (r : R.obj.obj W) (m : H.val.obj W) :
    (ringProjection I).hom.app W r • (show (annihilatedOverSheaf I H hH).val.obj W from m) =
      r • m := by
  have h := ((PresheafOfModules.toSheafify (quotientSheafificationMap I)
    (M₀ := annihilatedOverPresheaf I H hH) (A := (SheafOfModules.toSheaf _).obj
      H) (annihilatedUnderlyingMap I H hH)).app W).hom.map_smul
        (Ideal.Quotient.mk (I.sections W.unop) r) m
  exact h.symm

private noncomputable def annihilatedOverIso (I : RingedSiteIdeal R)
    (H : SheafOfModules.{u} (siteModuleRings R))
    (hH : ∀ W : Cᵒᵖ, Module.IsTorsionBySet (R.obj.obj W) (H.val.obj W)
      (I.sections W.unop)) :
    (SheafOfModules.RingedTensor.restriction (ringProjection I)).obj
      (annihilatedOverSheaf I H hH) ≅ H where
  hom :=
    { val :=
        { app W := ModuleCat.ofHom
            (X := ((SheafOfModules.RingedTensor.restriction (ringProjection I)).obj
              (annihilatedOverSheaf I H hH)).val.obj W)
            (Y := H.val.obj W)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun r m ↦ annihilatedOverSheaf_smul I H hH W r m }
          naturality := by intros; ext m; rfl } }
  inv :=
    { val :=
        { app W := ModuleCat.ofHom
            (X := H.val.obj W)
            (Y := ((SheafOfModules.RingedTensor.restriction (ringProjection I)).obj
              (annihilatedOverSheaf I H hH)).val.obj W)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun r m ↦ (annihilatedOverSheaf_smul I H hH W r m).symm }
          naturality := by intros; ext m; rfl } }
  hom_inv_id := by ext W m; rfl
  inv_hom_id := by ext W m; rfl

private noncomputable def quotientOverSheaf (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    SheafOfModules.{u} (siteModuleRings (ringQuotient I)) :=
  annihilatedOverSheaf I (moduleQuotient I F) (quotient_annihilated I F)

private lemma quotientOverSheaf_smul (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (r : R.obj.obj W) (m : (moduleQuotient I F).val.obj W) :
    (ringProjection I).hom.app W r • (show (quotientOverSheaf I F).val.obj W from m) =
      r • m :=
  annihilatedOverSheaf_smul I (moduleQuotient I F) (quotient_annihilated I F) W r m

private noncomputable def quotientOverIso (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    (SheafOfModules.RingedTensor.restriction (ringProjection I)).obj
      (quotientOverSheaf I F) ≅ moduleQuotient I F :=
  annihilatedOverIso I (moduleQuotient I F) (quotient_annihilated I F)

-- The balanced pairing and its extension to the sheaf tensor.

private noncomputable def annihilatedPairing (I : RingedSiteIdeal R)
    (F H : SheafOfModules.{u} (siteModuleRings R))
    (hH : ∀ W : Cᵒᵖ, Module.IsTorsionBySet (R.obj.obj W) (H.val.obj W)
      (I.sections W.unop)) (φ : F ⟶ H) (W : Cᵒᵖ) :
    F.val.obj W →ₗ[R.obj.obj W] (quotientCoefficient I).val.obj W →ₗ[R.obj.obj W]
      H.val.obj W := by
  let q := φ.val.app W
  let B (m : F.val.obj W) (s : (quotientCoefficient I).val.obj W) :
      H.val.obj W :=
    (show (ringQuotient I).obj.obj W from s) •
      (show (annihilatedOverSheaf I H hH).val.obj W from q m)
  refine LinearMap.mk₂ _ B ?_ ?_ ?_ ?_
  · intro m n s
    change (show (ringQuotient I).obj.obj W from s) •
      (show (annihilatedOverSheaf I H hH).val.obj W from q (m + n)) = _
    simp only [map_add, smul_add, B]
  · intro r m s
    change (show (ringQuotient I).obj.obj W from s) •
      (show (annihilatedOverSheaf I H hH).val.obj W from q (r • m)) = _
    rw [q.hom.map_smul]
    rw [← annihilatedOverSheaf_smul I H hH W r (q m),
      ← annihilatedOverSheaf_smul I H hH W r (B m s)]
    exact smul_comm (show (ringQuotient I).obj.obj W from s) ((ringProjection I).hom.app W r) _
  · intro m s t
    change ((show (ringQuotient I).obj.obj W from s) +
      (show (ringQuotient I).obj.obj W from t)) •
      (show (annihilatedOverSheaf I H hH).val.obj W from q m) = _
    exact add_smul _ _ _
  · intro r m s
    change (((ringProjection I).hom.app W r) *
      (show (ringQuotient I).obj.obj W from s)) •
      (show (annihilatedOverSheaf I H hH).val.obj W from q m) = _
    rw [← annihilatedOverSheaf_smul I H hH W r (B m s)]
    exact mul_smul _ _ _

private noncomputable def quotientPairing (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ) :
    F.val.obj W →ₗ[R.obj.obj W] (quotientCoefficient I).val.obj W →ₗ[R.obj.obj W]
      (moduleQuotient I F).val.obj W :=
  annihilatedPairing I F (moduleQuotient I F) (quotient_annihilated I F)
    (moduleProjection I F) W

private noncomputable def annihilatedTensorPresheafMap (I : RingedSiteIdeal R)
    (F H : SheafOfModules.{u} (siteModuleRings R))
    (hH : ∀ W : Cᵒᵖ, Module.IsTorsionBySet (R.obj.obj W) (H.val.obj W)
      (I.sections W.unop)) (φ : F ⟶ H) :
    (PresheafOfModules.Monoidal.tensorObj (R := R.obj) F.val (quotientCoefficient I).val) ⟶
      H.val where
  app W := ModuleCat.ofHom
    (X := (PresheafOfModules.Monoidal.tensorObj (R := R.obj) F.val
      (quotientCoefficient I).val).obj W)
    (Y := H.val.obj W)
    (TensorProduct.lift (annihilatedPairing I F H hH φ W))
  naturality {W V} g := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m s
    change (TensorProduct.lift (annihilatedPairing I F H hH φ V))
      ((PresheafOfModules.Monoidal.tensorObj (R := R.obj) F.val
        (quotientCoefficient I).val).map g (m ⊗ₜ[R.obj.obj W] s)) = _
    have ht := PresheafOfModules.Monoidal.tensorObj_map_tmul (R := R.obj)
      (M₁ := F.val) (M₂ := (quotientCoefficient I).val) g m s
    refine (congrArg (fun x ↦ (TensorProduct.lift
      (annihilatedPairing I F H hH φ V)) x) ht).trans ?_
    symm
    change (annihilatedOverSheaf I H hH).val.map g
      ((show (ringQuotient I).obj.obj W from s) • (show (annihilatedOverSheaf I H hH).val.obj W from
        φ.val.app W m)) = _
    rw [(annihilatedOverSheaf I H hH).val.map_smul]
    congr 1
    exact (PresheafOfModules.naturality_apply φ.val g m).symm

private noncomputable def quotientTensorPresheafMap (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    (PresheafOfModules.Monoidal.tensorObj (R := R.obj) F.val (quotientCoefficient I).val) ⟶
      (moduleQuotient I F).val :=
  annihilatedTensorPresheafMap I F (moduleQuotient I F) (quotient_annihilated I F)
    (moduleProjection I F)

private noncomputable def quotientTensorMap (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    quotientTensor I F ⟶ moduleQuotient I F :=
  (SheafOfModules.tensorObjIsoSheafification F (quotientCoefficient I)).hom ≫
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (siteModuleRings R).obj)
      (F := moduleQuotient I F)).symm (quotientTensorPresheafMap I F)

private lemma quotientTensorMap_pure (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (f : F.val.obj W) (s : (ringQuotient I).obj.obj W) :
    (quotientTensorMap I F).val.app W
      (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f s) =
      s • (show (quotientOverSheaf I F).val.obj W from
        (moduleProjection I F).val.app W f) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings R).obj)
  let T := PresheafOfModules.Monoidal.tensorObj (R := R.obj) F.val
    (quotientCoefficient I).val
  let η := (adj.unit.app T).app W (f ⊗ₜ[R.obj.obj W] s)
  let b := (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (siteModuleRings R).obj) (F := moduleQuotient I F)).symm
      (quotientTensorPresheafMap I F)
  have h := (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (siteModuleRings R).obj) (F := moduleQuotient I F)).apply_symm_apply
      (quotientTensorPresheafMap I F)
  have hh := congrArg ((PresheafOfModules.toPresheaf _).map) h
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at hh
  have hv := congrArg (fun k ↦ k.app W (f ⊗ₜ[R.obj.obj W] s)) hh
  change b.val.app W η = _ at hv
  have hi := congrArg (fun k ↦ k.val.app W η)
    (SheafOfModules.tensorObjIsoSheafification F (quotientCoefficient I)).inv_hom_id
  change (SheafOfModules.tensorObjIsoSheafification F (quotientCoefficient I)).hom.val.app W
    ((SheafOfModules.tensorObjIsoSheafification F (quotientCoefficient I)).inv.val.app W η) =
      η at hi
  change b.val.app W
    ((SheafOfModules.tensorObjIsoSheafification F (quotientCoefficient I)).hom.val.app W
      ((SheafOfModules.tensorObjIsoSheafification F (quotientCoefficient I)).inv.val.app W η)) = _
  rw [hi]
  exact hv

-- Descent of the pure unit map constructs the inverse comparison.

private noncomputable def tensorUnitMap (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) : F ⟶ quotientTensor I F where
  val :=
    { app W := ModuleCat.ofHom (X := F.val.obj W)
        (Y := (quotientTensor I F).val.obj W)
        ((SheafOfModules.RingedTensor.pureBilin R F (quotientCoefficient I) W).flip
          (1 : (ringQuotient I).obj.obj W))
      naturality {W V} g := by
        ext f
        change SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) V
          (F.val.map g f) (1 : (ringQuotient I).obj.obj V) = (quotientTensor I F).val.map g
            (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
              (1 : (ringQuotient I).obj.obj W))
        have hp := SheafOfModules.RingedTensor.pure_restrict R F
          (quotientCoefficient I) g f (1 : (ringQuotient I).obj.obj W)
        have h1 : (quotientCoefficient I).val.map g
            (1 : (ringQuotient I).obj.obj W) =
              (1 : (ringQuotient I).obj.obj V) :=
          map_one ((ringQuotient I).obj.map g).hom
        exact (hp.trans (congrArg (fun s : (ringQuotient I).obj.obj V ↦
          SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) V
            (F.val.map g f) s) h1)).symm }

private lemma tensorUnitMap_smul (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (r : R.obj.obj W) (f : F.val.obj W) :
    (tensorUnitMap I F).val.app W (r • f) =
      SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
        ((ringProjection I).hom.app W r) := by
  let B := SheafOfModules.RingedTensor.pureBilin R F (quotientCoefficient I) W
  change B (r • f) (1 : (ringQuotient I).obj.obj W) = B f ((ringProjection I).hom.app W r)
  calc
    B (r • f) (1 : (ringQuotient I).obj.obj W) =
        r • B f (1 : (ringQuotient I).obj.obj W) :=
      congrArg (fun k ↦ k (1 : (ringQuotient I).obj.obj W)) (B.map_smul r f)
    _ = _ := by
      have h := ((B f).map_smul r (1 : (ringQuotient I).obj.obj W)).symm
      have h1 : ((ModuleCat.isModule ((quotientCoefficient I).val.obj W)).smul r
          (1 : (ringQuotient I).obj.obj W)) = (ringProjection I).hom.app W r :=
        mul_one ((ringProjection I).hom.app W r)
      exact h.trans (congrArg (B f) h1)

private lemma ringProjection_ideal (I : RingedSiteIdeal R) (W : Cᵒᵖ)
    (r : R.obj.obj W) (hr : r ∈ I.sections W.unop) :
    (ringProjection I).hom.app W r = 0 := by
  change (toSheafify J (ringQuotientPresheaf I)).app W
    (Ideal.Quotient.mk (I.sections W.unop) r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

private lemma tensorUnitMap_ideal (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (r : R.obj.obj W) (hr : r ∈ I.sections W.unop) (f : F.val.obj W) :
    (tensorUnitMap I F).val.app W (r • f) = 0 := by
  rw [tensorUnitMap_smul, ringProjection_ideal I W r hr]
  exact (SheafOfModules.RingedTensor.pureBilin R F (quotientCoefficient I) W f).map_zero

private lemma tensorUnitMap_localProduct (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (f : F.val.obj W) (hf : f ∈ (localProduct I F).obj W) :
    (tensorUnitMap I F).val.app W f = 0 := by
  obtain ⟨S, hS, h⟩ := (localProduct_membership I F W.unop f).mp hf
  apply (quotientTensor I F).isSheaf.isSeparated _ _ hS
  intro V g hg
  change (quotientTensor I F).val.map g.op ((tensorUnitMap I F).val.app W f) =
    (quotientTensor I F).val.map g.op 0
  rw [← PresheafOfModules.naturality_apply, map_zero]
  obtain ⟨n, i, x, hx⟩ := h V g hg
  rw [hx, map_sum]
  apply Finset.sum_eq_zero
  intro k _
  exact tensorUnitMap_ideal I F _ (i k).val (i k).property (x k)

private noncomputable def quotientTensorInverse (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) : moduleQuotient I F ⟶ quotientTensor I F :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (siteModuleRings R).obj)
    (F := quotientTensor I F)).symm
    (cokernel.desc (localProduct I F).ι (tensorUnitMap I F).val (by
      ext W x
      exact tensorUnitMap_localProduct I F W x.val x.property))

private lemma projection_tensorInverse (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    moduleProjection I F ≫ quotientTensorInverse I F = tensorUnitMap I F := by
  let g := cokernel.desc (localProduct I F).ι (tensorUnitMap I F).val (by
    ext W x
    exact tensorUnitMap_localProduct I F W x.val x.property)
  have h := (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (siteModuleRings R).obj) (F := quotientTensor I F)).apply_symm_apply g
  apply SheafOfModules.hom_ext
  change (cokernel.π (localProduct I F).ι ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings R).obj)).unit.app
      (moduleQuotientPresheaf I F)) ≫ _ = _
  rw [Category.assoc]
  change cokernel.π (localProduct I F).ι ≫
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (siteModuleRings R).obj)
      (F := quotientTensor I F))
      ((PresheafOfModules.sheafificationHomEquiv (𝟙 (siteModuleRings R).obj)
        (F := quotientTensor I F)).symm g) = _
  rw [h]
  exact cokernel.π_desc _ _ _

private lemma tensorUnit_comparison (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    tensorUnitMap I F ≫ quotientTensorMap I F = moduleProjection I F := by
  ext W f
  change (quotientTensorMap I F).val.app W
    (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
              (1 : (ringQuotient I).obj.obj W)) = _
  rw [quotientTensorMap_pure, one_smul]

private lemma ringProjection_surj (I : RingedSiteIdeal R) :
    Presheaf.IsLocallySurjective J (ringProjection I).hom := by
  have : Presheaf.IsLocallySurjective J (ringQuotientPresheafProjection I) :=
    Presheaf.isLocallySurjective_of_surjective J _ fun W ↦ Ideal.Quotient.mk_surjective
  change Presheaf.IsLocallySurjective J
    (ringQuotientPresheafProjection I ≫ toSheafify J (ringQuotientPresheaf I))
  infer_instance

attribute [local instance] ringProjection_surj

private lemma quotientTensor_inverse_hom (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    quotientTensorInverse I F ≫ quotientTensorMap I F = 𝟙 _ := by
  have := projection_epi I F
  apply (cancel_epi (moduleProjection I F)).mp
  rw [← Category.assoc, projection_tensorInverse, tensorUnit_comparison, Category.comp_id]

private lemma quotientTensorMap_lift (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) (W : Cᵒᵖ)
    (f : F.val.obj W) (r : R.obj.obj W) :
    (quotientTensorMap I F).val.app W
      (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
        ((ringProjection I).hom.app W r)) =
      (moduleProjection I F).val.app W (r • f) :=
  (quotientTensorMap_pure I F W f ((ringProjection I).hom.app W r)).trans
    ((quotientOverSheaf_smul I F W r ((moduleProjection I F).val.app W f)).trans
      (((moduleProjection I F).val.app W).hom.map_smul r f).symm)

private lemma quotientTensor_hom_inverse (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    quotientTensorMap I F ≫ quotientTensorInverse I F = 𝟙 _ := by
  apply SheafOfModules.RingedTensor.pure_hom_ext R F (quotientCoefficient I)
  intro W f s
  let T := quotientTensor I F
  let c := quotientTensorMap I F ≫ quotientTensorInverse I F
  apply T.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J (ringProjection I).hom s)
  rintro V g ⟨r, hr⟩
  let fV : F.val.obj (op V) := F.val.map g.op f
  let sV : (ringQuotient I).obj.obj (op V) := (ringQuotient I).obj.map g.op s
  change (ringProjection I).hom.app (op V) r = sV at hr
  let p : (ringQuotient I).obj.obj (op V) → T.val.obj (op V) :=
    fun t ↦ SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) (op V) fV t
  have hp : T.val.map g.op
      (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f s) = p sV :=
    SheafOfModules.RingedTensor.pure_restrict R F (quotientCoefficient I) g.op f s
  have hq := congrArg (fun k : F ⟶ T ↦ k.val.app (op V) (r • fV))
    (projection_tensorInverse I F)
  have hlocal : c.val.app (op V) (p ((ringProjection I).hom.app (op V) r)) =
      p ((ringProjection I).hom.app (op V) r) :=
    (congrArg ((quotientTensorInverse I F).val.app (op V))
      (quotientTensorMap_lift I F (op V) fV r)).trans
        (hq.trans (tensorUnitMap_smul I F (op V) r fV))
  have hv : c.val.app (op V) (p sV) = p sV :=
    (congrArg (fun t ↦ c.val.app (op V) (p t)) hr).symm.trans
      (hlocal.trans (congrArg p hr))
  exact (PresheafOfModules.naturality_apply c.val g.op
    (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f s)).symm.trans
      ((congrArg (c.val.app (op V)) hp).trans (hv.trans hp.symm))

private noncomputable def quotientTensorIso (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    quotientTensor I F ≅ moduleQuotient I F where
  hom := quotientTensorMap I F
  inv := quotientTensorInverse I F
  hom_inv_id := quotientTensor_hom_inverse I F
  inv_hom_id := quotientTensor_inverse_hom I F

private lemma tensorUnit_comparison_iso (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    tensorUnitMap I F ≫ (quotientTensorIso I F).hom = moduleProjection I F :=
  tensorUnit_comparison I F

private lemma projection_tensorIso_inv (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    moduleProjection I F ≫ (quotientTensorIso I F).inv = tensorUnitMap I F :=
  projection_tensorInverse I F

-- Naturality is transported through the constructed comparison isomorphisms.

private lemma tensorUnit_natural (I : RingedSiteIdeal R)
    {F G : SheafOfModules.{u} (siteModuleRings R)} (h : F ⟶ G) :
    tensorUnitMap I F ≫ (SheafOfModules.monoidalCategory R).tensorHom h
      (𝟙 (quotientCoefficient I)) = h ≫ tensorUnitMap I G := by
  ext W f
  exact SheafOfModules.RingedTensor.pure_map R h (𝟙 (quotientCoefficient I)) W f
    (1 : (ringQuotient I).obj.obj W)

private lemma ringProjection_ring_surj (I : RingedSiteIdeal R) :
    Presheaf.IsLocallySurjective J
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map (ringProjection I)).hom where
  imageSieve_mem s := Presheaf.imageSieve_mem J (ringProjection I).hom s

attribute [local instance] ringProjection_ring_surj

private lemma quotient_morphism_lift (I : RingedSiteIdeal R)
    (F G : SheafOfModules.{u} (siteModuleRings R))
    (h : moduleQuotient I F ⟶ moduleQuotient I G) :
    ∃ hS : quotientOverSheaf I F ⟶ quotientOverSheaf I G,
      (quotientOverIso I F).hom ≫ h =
        (SheafOfModules.RingedTensor.restriction (ringProjection I)).map hS ≫
          (quotientOverIso I G).hom := by
  let hR := (quotientOverIso I F).hom ≫ h ≫ (quotientOverIso I G).inv
  let E := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map (ringProjection I)).hom
    (M₁ := (quotientOverSheaf I F).val) (quotientOverSheaf I G).isSheaf
  let hS : quotientOverSheaf I F ⟶ quotientOverSheaf I G := ⟨E.symm hR.val⟩
  have hh : (SheafOfModules.RingedTensor.restriction (ringProjection I)).map hS = hR :=
    SheafOfModules.hom_ext (E.apply_symm_apply hR.val)
  refine ⟨hS, ?_⟩
  rw [hh]
  simp only [hR, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma ringProjection_transition {I' I : RingedSiteIdeal R} (hI : IsContained I' I) :
    ringProjection I' ≫ ringTransition hI = ringProjection I := by
  apply Sheaf.hom_ext
  change (ringQuotientPresheafProjection I' ≫ toSheafify J (ringQuotientPresheaf I')) ≫
    ((presheafToSheaf J CommRingCat).map (ringQuotientPresheafTransition hI)).hom = _
  rw [Category.assoc]
  rw [← toSheafify_naturality]
  change ringQuotientPresheafProjection I' ≫
    (ringQuotientPresheafTransition hI ≫ toSheafify J (ringQuotientPresheaf I)) = _
  rw [← Category.assoc]
  congr 1

private noncomputable def quotientCoefficientTransition {I' I : RingedSiteIdeal R}
    (hI : IsContained I' I) : quotientCoefficient I' ⟶ quotientCoefficient I where
  val :=
    { app W := ModuleCat.ofHom
        (X := (quotientCoefficient I').val.obj W)
        (Y := (quotientCoefficient I).val.obj W)
        { toFun := (ringTransition hI).hom.app W
          map_add' := map_add _
          map_smul' := fun r s ↦ by
            change (ringTransition hI).hom.app W
              ((ringProjection I').hom.app W r *
                (show (ringQuotient I').obj.obj W from s)) =
              (ringProjection I).hom.app W r * (ringTransition hI).hom.app W s
            rw [map_mul]
            congr 1
            exact congrArg (fun k : R ⟶ ringQuotient I ↦ k.hom.app W r)
              (ringProjection_transition hI) }
      naturality {W V} g := by
        ext s
        exact (ringTransition hI).hom.naturality_apply g s }

private lemma tensorUnit_transition {I' I : RingedSiteIdeal R} (hI : IsContained I' I)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    tensorUnitMap I' F ≫ (SheafOfModules.monoidalCategory R).tensorHom (𝟙 F)
      (quotientCoefficientTransition hI) = tensorUnitMap I F := by
  ext W f
  change ((SheafOfModules.monoidalCategory R).tensorHom (𝟙 F)
    (quotientCoefficientTransition hI)).val.app W
      (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I') W f
        (1 : (ringQuotient I').obj.obj W)) = _
  rw [SheafOfModules.RingedTensor.pure_map]
  change SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
    ((ringTransition hI).hom.app W 1) = _
  rw [map_one]
  rfl

/-- Tensor with the quotient ring is the sheaf quotient by the local ideal product.
The S-module structure is recorded as an S-module Q with an R-linear identification e
with the already constructed quotient. Linearity of a for S is expressed on pure sections:
the S-action on the tensor is multiplication in its second factor. This determines the
entire action by pure-section extensionality. All tensor objects and pure sections are
those of the existing sheaf tensor, not sectionwise tensors substituted for sheaves.

Source: Stacks 03EK, 03CY (blueprint: lem-weil-pbc-sheaf-tensor-ideal-quotient).
Proof:
1. Mathlib's locally bijective sheafification maps give covering image and equalizer
   sieves. Quotient sections lift locally, and equality is checked after refinement.
2. The local hull of the sectionwise ideal product equals localProduct. Cover
   intersections prove closure under addition, and transitivity proves saturation.
   The saturated subfunctor is a sheaf. Ideal-product induction gives the finite-sum
   description. Evaluating the cokernel and using local injectivity proves ker(q)=IF;
   local representatives and separatedness prove that q is epic.
3. The ideal annihilates Q, by checking on local representatives. The quotient action
   of the ring presheaf S₀ on Q extends by module sheafification to an S-action on the
   same abelian sheaf. The canonical map supplies its R-linear identification e.
4. The pairing B(f,s)=s q(f) is R-bilinear. TensorProduct.lift and the module
   sheafification adjunction construct a with a(pure(f,s))=s q(f).
5. Define u(f)=pure(f,1). Balancing kills ideal multiples and hence locally finite sums.
   The cokernel universal property and sheafification give b with b(q(f))=u(f).
6. Cancel the epic q to check one inverse identity. Check the other on pure sections
   after locally lifting the scalar factor, then use separatedness and pure_hom_ext.
   The S-linearity formula follows from associativity of the constructed S-action.
7. The formula au=q gives u=qb, its epimorphy, and its asserted kernel.
8. Transport h tensor id across a to define qh. Naturality of u proves the projection
   square. Full faithfulness of restriction along the locally surjective ring
   projection lifts qh to the S-linear hS; inverse cancellation gives the tensor square.
9. The sheafified ring transition is R-linear by naturality of sheafification.
   Its value on 1 proves the unit-transition identity. Transport id tensor t across a
   to define v and deduce both remaining squares by the same inverse identities. -/
theorem sheaf_tensor_ideal_quotient
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    ∃ (a : ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
        quotientTensor I F ≅ moduleQuotient I F)
      (uMap : ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
        F ⟶ quotientTensor I F)
      (Q : ∀ (I : RingedSiteIdeal R) (_ : SheafOfModules.{u} (siteModuleRings R)),
        SheafOfModules.{u} (siteModuleRings (ringQuotient I)))
      (e : ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
        (SheafOfModules.RingedTensor.restriction (ringProjection I)).obj (Q I F) ≅
          moduleQuotient I F),
      ∀ (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)),
      Presheaf.IsSheaf J (localProduct I F).toPresheafOfModules.presheaf ∧
      (∀ (U : C) (f : F.val.obj (op U)), f ∈ (localProduct I F).obj (op U) ↔
        ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
          ∃ (n : ℕ) (i : Fin n → I.sections V) (x : Fin n → F.val.obj (op V)),
            F.val.map g.op f = ∑ k : Fin n, (i k).val • x k) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W),
        (uMap I F).val.app W f =
          SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
            (1 : (ringQuotient I).obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W) (r : R.obj.obj W),
        (a I F).hom.val.app W
          (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
            ((ringProjection I).hom.app W r)) =
          (moduleProjection I F).val.app W (r • f)) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W),
        (a I F).inv.val.app W ((moduleProjection I F).val.app W f) =
          SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f
            (1 : (ringQuotient I).obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W) (s t : (ringQuotient I).obj.obj W),
        (e I F).inv.val.app W ((a I F).hom.val.app W
          (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f (s * t))) =
        s • @id ((Q I F).val.obj W)
          ((e I F).inv.val.app W ((a I F).hom.val.app W
            (SheafOfModules.RingedTensor.pure R F (quotientCoefficient I) W f t)))) ∧
      uMap I F ≫ (a I F).hom = moduleProjection I F ∧
      Epi (uMap I F) ∧
      (∀ (W : Cᵒᵖ) (f : F.val.obj W),
        (uMap I F).val.app W f = 0 ↔ f ∈ (localProduct I F).obj W) ∧
      (∀ (G : SheafOfModules.{u} (siteModuleRings R)) (h : F ⟶ G),
        ∃ (qh : moduleQuotient I F ⟶ moduleQuotient I G) (hS : Q I F ⟶ Q I G),
          moduleProjection I F ≫ qh = h ≫ moduleProjection I G ∧
          (e I F).hom ≫ qh =
            (SheafOfModules.RingedTensor.restriction (ringProjection I)).map hS ≫
              (e I G).hom ∧
          (a I F).hom ≫ qh =
            (SheafOfModules.monoidalCategory R).tensorHom h (𝟙 (quotientCoefficient I)) ≫
              (a I G).hom) ∧
      (∀ (I' : RingedSiteIdeal R) (hI : IsContained I' I),
        ∃ (tM : quotientCoefficient I' ⟶ quotientCoefficient I)
          (v : moduleQuotient I' F ⟶ moduleQuotient I F),
          (∀ (W : Cᵒᵖ) (s : (ringQuotient I').obj.obj W),
            tM.val.app W s = (ringTransition hI).hom.app W s) ∧
          moduleProjection I' F ≫ v = moduleProjection I F ∧
          (a I' F).hom ≫ v =
            (SheafOfModules.monoidalCategory R).tensorHom (𝟙 F) tM ≫ (a I F).hom ∧
          uMap I' F ≫ (SheafOfModules.monoidalCategory R).tensorHom (𝟙 F) tM = uMap I F) := by
  refine ⟨quotientTensorIso, tensorUnitMap, quotientOverSheaf, quotientOverIso, ?_⟩
  intro I F
  refine ⟨saturated_isSheaf F _ (localProduct_saturated I F),
    localProduct_membership I F, ?_, ?_, ?_, ?_, tensorUnit_comparison I F, ?_, ?_, ?_, ?_⟩
  · intro W f
    rfl
  · intro W f r
    exact (quotientTensorMap_pure I F W f ((ringProjection I).hom.app W r)).trans
      ((quotientOverSheaf_smul I F W r ((moduleProjection I F).val.app W f)).trans
        (((moduleProjection I F).val.app W).hom.map_smul r f).symm)
  · intro W f
    exact congrArg (fun k : F ⟶ quotientTensor I F ↦ k.val.app W f)
      (projection_tensorInverse I F)
  · intro W f s t
    exact (quotientTensorMap_pure I F W f (s * t)).trans
      ((mul_smul s t (show (quotientOverSheaf I F).val.obj W from
        (moduleProjection I F).val.app W f)).trans
        (congrArg (fun x : (quotientOverSheaf I F).val.obj W ↦ s • x)
          (quotientTensorMap_pure I F W f t).symm))
  · have := projection_epi I F
    rw [← projection_tensorIso_inv]
    infer_instance
  · intro W f
    have h := congrArg (fun k : F ⟶ moduleQuotient I F ↦ k.val.app W f)
      (tensorUnit_comparison_iso I F)
    have h' := congrArg (fun k : F ⟶ quotientTensor I F ↦ k.val.app W f)
      (projection_tensorIso_inv I F)
    change (quotientTensorIso I F).hom.val.app W ((tensorUnitMap I F).val.app W f) =
      (moduleProjection I F).val.app W f at h
    change (quotientTensorIso I F).inv.val.app W
      ((moduleProjection I F).val.app W f) = (tensorUnitMap I F).val.app W f at h'
    rw [← projection_zero_iff I F W f]
    constructor
    · intro hz
      rw [← h, hz, map_zero]
    · intro hz
      rw [← h', hz, map_zero]
  · intro G h
    let t : quotientTensor I F ⟶ quotientTensor I G :=
      (SheafOfModules.monoidalCategory R).tensorHom h (𝟙 (quotientCoefficient I))
    let qh := (quotientTensorIso I F).inv ≫ t ≫ (quotientTensorIso I G).hom
    obtain ⟨hS, hhS⟩ := quotient_morphism_lift I F G qh
    refine ⟨qh, hS, ?_, hhS, ?_⟩
    · calc
        moduleProjection I F ≫ qh = tensorUnitMap I F ≫ t ≫
            (quotientTensorIso I G).hom := by
          simp only [qh, ← Category.assoc, projection_tensorIso_inv]
        _ = h ≫ moduleProjection I G := by
          rw [← Category.assoc, tensorUnit_natural, Category.assoc,
            tensorUnit_comparison_iso]
    · simp only [qh, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rfl
  · intro I' hI
    let tM := quotientCoefficientTransition hI
    let t : quotientTensor I' F ⟶ quotientTensor I F :=
      (SheafOfModules.monoidalCategory R).tensorHom (𝟙 F) tM
    let v := (quotientTensorIso I' F).inv ≫ t ≫ (quotientTensorIso I F).hom
    refine ⟨tM, v, fun _ _ ↦ rfl, ?_, ?_, tensorUnit_transition hI F⟩
    · calc
        moduleProjection I' F ≫ v = tensorUnitMap I' F ≫ t ≫
            (quotientTensorIso I F).hom := by
          simp only [v, ← Category.assoc, projection_tensorIso_inv]
        _ = moduleProjection I F := by
          rw [← Category.assoc, tensorUnit_transition, tensorUnit_comparison_iso]
    · simp only [v, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rfl

end CategoryTheory.RingedSiteIdeal
