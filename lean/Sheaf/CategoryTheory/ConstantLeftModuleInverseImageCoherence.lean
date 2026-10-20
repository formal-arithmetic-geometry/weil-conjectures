/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.ConstantLeftModuleTransport
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-! Coherence comparisons for constant left-module inverse images.
Source: Stacks Project, Sites, Tags 00YV and 00XZ (blueprint:
lem-pe-constant-left-module-inverse-image).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
open ConstantLeftModuleInverseImage
attribute [local instance] comp_preservesFiniteLimits

/-- The existence of composition, presentation, and localization comparisons for a transported
constant-coefficient module lift. Uniqueness is proved separately in the main construction
by faithfulness and cancellation.
Source: Stacks, Tags 00YV, 00XZ and 00Y0 (blueprint: lem-pe-constant-left-module-inverse-image). -/
structure ConstantLeftModuleInverseImageCoherence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) where
  composition_coherence :
    ∀ {E : Type u} [SmallCategory E] (H : GrothendieckTopology E)
      [HasWeakSheafify H RingCat.{u}]
      (L₂ : Sheaf K (Type u) ⥤ Sheaf H (Type u))
      (R₂ : Sheaf H (Type u) ⥤ Sheaf K (Type u))
      (adj₂ : L₂ ⊣ R₂) (hL₂ : PreservesFiniteLimits L₂)
      (d₂ : ConstantLeftModuleInverseImageLift K H Λ L₂ R₂ adj₂ hL₂)
      (d₃ : ConstantLeftModuleInverseImageLift J H Λ (L ⋙ L₂) (R₂ ⋙ R)
        (adj.comp adj₂) (@comp_preservesFiniteLimits _ _ _ _ _ _ L L₂ hL hL₂)),
      ∃ i : d₃.moduleFunctor ≅ d.moduleFunctor ⋙ d₂.moduleFunctor,
        ∀ M : Modules J Λ,
          (W H Λ).map (i.hom.app M) ≫ d₂.moduleSetIso.hom.app (d.moduleFunctor.obj M) ≫
            L₂.map (d.moduleSetIso.hom.app M) = d₃.moduleSetIso.hom.app M
  presentation_coherence :
    ∀ (L' : Sheaf J (Type u) ⥤ Sheaf K (Type u))
      (R' : Sheaf K (Type u) ⥤ Sheaf J (Type u))
      (adj' : L' ⊣ R') (hL' : PreservesFiniteLimits L')
      (d' : ConstantLeftModuleInverseImageLift J K Λ L' R' adj' hL') (e : L ≅ L'),
      ∃ i : d.moduleFunctor ≅ d'.moduleFunctor, ∀ M : Modules J Λ,
        (W K Λ).map (i.hom.app M) ≫ d'.moduleSetIso.hom.app M =
          d.moduleSetIso.hom.app M ≫ e.hom.app ((W J Λ).obj M)
  localization_coherence : ∀ X : C,
    ∃ (Rₓ : Sheaf (J.over X) (Type u) ⥤ Sheaf J (Type u))
      (adjₓ : J.overPullback (Type u) X ⊣ Rₓ)
      (hLₓ : PreservesFiniteLimits (J.overPullback (Type u) X))
      (dₓ : ConstantLeftModuleInverseImageLift J (J.over X) Λ
        (J.overPullback (Type u) X) Rₓ adjₓ hLₓ)
      (c : ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over X ≅
        (constantSheaf (J.over X) RingCat.{u}).obj (RingCat.of Λ)),
      (∀ (T : (Over X)ᵒᵖ) (r : Λ), c.hom.hom.app T
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app
          ((Over.forget X).op.obj T) r) =
        (toSheafify (J.over X)
          ((Functor.const (Over X)ᵒᵖ).obj (RingCat.of Λ))).app T r) ∧
      ∃ i : dₓ.moduleFunctor ≅
          SheafOfModules.overFunctor ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) X ⋙
            SheafOfModules.restrictScalars c.inv,
        ∀ (M : Modules J Λ) (T : (Over X)ᵒᵖ)
          (x : (dₓ.moduleFunctor.obj M).val.obj T),
          (i.hom.app M).val.app T x = (dₓ.moduleSetIso.hom.app M).hom.app T x

set_option backward.isDefEq.respectTransparency false in
private def scalarEndomorphism
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J Λ) (r : Λ) : (V J Λ).obj M ⟶ (V J Λ).obj M where
  hom :=
    { app := fun T ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦
            ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x
          map_zero' := smul_zero _
          map_add' := smul_add _ }
      naturality := by
        intro T S f
        ext x
        change M.val.obj T at x
        change
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app S r) •
              M.val.map f x =
            M.val.map f
              (((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app T r) • x)
        rw [M.val.map_smul]
        congr 1
        exact congrArg (fun g ↦ g r)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).naturality f) }

private theorem scalarEndomorphism_isScalar
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J Λ) (r : Λ) :
    IsScalar J Λ M r (scalarEndomorphism J Λ M r) := by
  intro T x
  rfl

private def linearHomOfConstantScalars
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    {M N : Modules J Λ} (f : (V J Λ).obj M ⟶ (V J Λ).obj N)
    (hf : ∀ r : Λ,
      scalarEndomorphism J Λ M r ≫ f = f ≫ scalarEndomorphism J Λ N r) : M ⟶ N := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
      (PresheafOfModules.restrictScalars α).obj N.val :=
    PresheafOfModules.homMk f.hom (by
      intro T r x
      exact congrArg (fun k ↦ k.hom.app T x) (hf r))
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    α N.isSheaf).symm g⟩


private def abelianLift
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) : F ⟶ G := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact (H.preimage (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G)
    (ObjectProperty.homMk α)).hom

private theorem abelianLift_forget
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) :
    Functor.whiskerRight (abelianLift F G α) (forget AddCommGrpCat) = α := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact congrArg (fun f ↦ f.hom) (H.map_preimage
    (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G) (ObjectProperty.homMk α))

private theorem linearHomOfConstantScalars_forget
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    {M N : Modules J Λ} (f : (V J Λ).obj M ⟶ (V J Λ).obj N)
    (hf : ∀ r : Λ,
      scalarEndomorphism J Λ M r ≫ f = f ≫ scalarEndomorphism J Λ N r) :
    (V J Λ).map (linearHomOfConstantScalars J Λ f hf) = f := by
  rfl

private theorem moduleNatTrans
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (F G : Modules J Λ ⥤ Modules K Λ)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ W K Λ ⟶ G ⋙ W K Λ)
    (hα : ∀ (M : Modules J Λ) (r : Λ),
      (U K).map (scalarEndomorphism K Λ (F.obj M) r) ≫ α.app M =
        α.app M ≫ (U K).map (scalarEndomorphism K Λ (G.obj M) r)) :
    ∃ a : F ⟶ G, Functor.whiskerRight a (W K Λ) = α := by
  let : HasFiniteBiproducts (Modules J Λ) := .of_hasFiniteProducts
  have : PreservesFiniteLimits (V K Λ) := inferInstance
  have : PreservesFiniteLimits (sheafToPresheaf K AddCommGrpCat.{u}) := inferInstance
  have (T : Dᵒᵖ) :
      PreservesFiniteLimits ((evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T) := inferInstance
  have (T : Dᵒᵖ) : PreservesFiniteLimits
      (F ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T) := inferInstance
  have (T : Dᵒᵖ) : PreservesFiniteLimits
      (G ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T) := inferInstance
  let b := fun T : Dᵒᵖ ↦ abelianLift
    (F ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    (G ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    { app := fun N ↦ (α.app N).hom.app T
      naturality := by
        intro M N f
        exact congrArg (fun k ↦ k.hom.app T) (α.naturality f) }
  have hb (T : Dᵒᵖ) (M : Modules J Λ) :
      (forget AddCommGrpCat).map ((b T).app M) = (α.app M).hom.app T := by
    dsimp only [b]
    exact congr_app (abelianLift_forget _ _ _) M
  let a : F ⋙ V K Λ ⟶ G ⋙ V K Λ :=
    { app := fun M ↦
        { hom :=
            { app := fun T ↦ (b T).app M
              naturality := by
                intro T S f
                apply (forget AddCommGrpCat).map_injective
                change (forget AddCommGrpCat).map (((F ⋙ V K Λ).obj M).obj.map f) ≫
                    (forget AddCommGrpCat).map ((b S).app M) =
                  (forget AddCommGrpCat).map ((b T).app M) ≫
                    (forget AddCommGrpCat).map (((G ⋙ V K Λ).obj M).obj.map f)
                rw [hb, hb]
                exact (α.app M).hom.naturality f } }
      naturality := by
        intro M N f
        ext T x
        exact congrArg (fun k ↦ k.hom x) ((b T).naturality f) }
  have ha (M : Modules J Λ) : (U K).map (a.app M) = α.app M := by
    ext T x
    exact congrArg (fun k ↦ k x) (hb T M)
  refine ⟨
    { app := fun M ↦ linearHomOfConstantScalars K Λ (a.app M) (fun r ↦ ?_)
      naturality := ?_ }, ?_⟩
  · apply (U K).map_injective
    simpa only [Functor.map_comp, ha] using hα M r
  · intro M N f
    apply (V K Λ).map_injective
    simpa only [Functor.map_comp, Functor.comp_map, linearHomOfConstantScalars_forget]
      using a.naturality f
  · ext M T x
    exact congrArg (fun k ↦ k.hom.app T x) (ha M)

private theorem liftScalarMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    (M : Modules J Λ) (r : Λ) :
    (U K).map (scalarEndomorphism K Λ (d.moduleFunctor.obj M) r) ≫
        d.moduleSetIso.hom.app M =
      d.moduleSetIso.hom.app M ≫ L.map ((U J).map (scalarEndomorphism J Λ M r)) := by
  have h := d.scalar_compatibility M r _ _
    (scalarEndomorphism_isScalar J Λ M r)
    (scalarEndomorphism_isScalar K Λ (d.moduleFunctor.obj M) r)
  rw [← d.moduleSetIso_compatibility]
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg ((U K).map (d.underlyingIso.hom.app M) ≫ ·)
      (d.abelianSetIso.hom.naturality (scalarEndomorphism J Λ M r))

private theorem moduleIsoOfScalars
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (F G : Modules J Λ ⥤ Modules K Λ)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (e : F ⋙ W K Λ ≅ G ⋙ W K Λ)
    (he : ∀ (M : Modules J Λ) (r : Λ),
      (U K).map (scalarEndomorphism K Λ (F.obj M) r) ≫ e.hom.app M =
        e.hom.app M ≫ (U K).map (scalarEndomorphism K Λ (G.obj M) r)) :
    ∃ i : F ≅ G, Functor.whiskerRight i.hom (W K Λ) = e.hom := by
  obtain ⟨a, ha⟩ := moduleNatTrans J K Λ F G e.hom he
  have : IsIso (Functor.whiskerRight a (W K Λ)) := by rw [ha]; infer_instance
  have : IsIso (((Functor.whiskeringRight _ _ _).obj (W K Λ)).map a) := by
    change IsIso (Functor.whiskerRight a (W K Λ))
    infer_instance
  have : IsIso a := isIso_of_reflects_iso a ((Functor.whiskeringRight _ _ _).obj (W K Λ))
  exact ⟨asIso a, ha⟩

set_option backward.isDefEq.respectTransparency false in
private theorem presentationComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L L' : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R R' : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (adj' : L' ⊣ R') (hL' : PreservesFiniteLimits L')
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    (d' : ConstantLeftModuleInverseImageLift J K Λ L' R' adj' hL') (e : L ≅ L') :
    ∃ i : d.moduleFunctor ≅ d'.moduleFunctor, ∀ M : Modules J Λ,
      (W K Λ).map (i.hom.app M) ≫ d'.moduleSetIso.hom.app M =
        d.moduleSetIso.hom.app M ≫ e.hom.app ((W J Λ).obj M) := by
  let := d.preservesFiniteLimits
  let := d'.preservesFiniteLimits
  let α : d.moduleFunctor ⋙ W K Λ ≅ d'.moduleFunctor ⋙ W K Λ :=
    d.moduleSetIso ≪≫ Functor.isoWhiskerLeft (W J Λ) e ≪≫ d'.moduleSetIso.symm
  obtain ⟨i, hi⟩ := moduleIsoOfScalars J K Λ _ _ α (by
    intro M r
    change (U K).map (scalarEndomorphism K Λ (d.moduleFunctor.obj M) r) ≫
        (d.moduleSetIso.hom.app M ≫ e.hom.app ((W J Λ).obj M) ≫
          d'.moduleSetIso.inv.app M) =
      (d.moduleSetIso.hom.app M ≫ e.hom.app ((W J Λ).obj M) ≫
          d'.moduleSetIso.inv.app M) ≫
        (U K).map (scalarEndomorphism K Λ (d'.moduleFunctor.obj M) r)
    apply (cancel_mono (d'.moduleSetIso.hom.app M)).mp
    have hs := liftScalarMap J K Λ L R adj hL d M r
    have hs' := liftScalarMap J K Λ L' R' adj' hL' d' M r
    have he := e.hom.naturality ((U J).map (scalarEndomorphism J Λ M r))
    simp only [Category.assoc, Iso.inv_hom_id_app] 
    erw [Category.comp_id]
    rw [← Category.assoc, hs, Category.assoc]
    dsimp only [W, Functor.comp_obj] at he ⊢
    rw [he, hs']
    simp only [← Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id])
  refine ⟨i, fun M ↦ ?_⟩
  have h := congr_app hi M
  change (W K Λ).map (i.hom.app M) =
    d.moduleSetIso.hom.app M ≫ e.hom.app ((W J Λ).obj M) ≫
      d'.moduleSetIso.inv.app M at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem compositionComparison
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (H : GrothendieckTopology E) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
    [HasWeakSheafify H RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (L₂ : Sheaf K (Type u) ⥤ Sheaf H (Type u))
    (R₂ : Sheaf H (Type u) ⥤ Sheaf K (Type u))
    (adj₂ : L₂ ⊣ R₂) (hL₂ : PreservesFiniteLimits L₂)
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL)
    (d₂ : ConstantLeftModuleInverseImageLift K H Λ L₂ R₂ adj₂ hL₂)
    (d₃ : ConstantLeftModuleInverseImageLift J H Λ (L ⋙ L₂) (R₂ ⋙ R)
      (adj.comp adj₂) (@comp_preservesFiniteLimits _ _ _ _ _ _ L L₂ hL hL₂)) :
    ∃ i : d₃.moduleFunctor ≅ d.moduleFunctor ⋙ d₂.moduleFunctor,
      ∀ M : Modules J Λ,
        (W H Λ).map (i.hom.app M) ≫ d₂.moduleSetIso.hom.app (d.moduleFunctor.obj M) ≫
          L₂.map (d.moduleSetIso.hom.app M) = d₃.moduleSetIso.hom.app M := by
  let := d.preservesFiniteLimits
  let := d₂.preservesFiniteLimits
  let := d₃.preservesFiniteLimits
  let β : (d.moduleFunctor ⋙ d₂.moduleFunctor) ⋙ W H Λ ≅ W J Λ ⋙ (L ⋙ L₂) :=
    Functor.isoWhiskerLeft d.moduleFunctor d₂.moduleSetIso ≪≫
      Functor.isoWhiskerRight d.moduleSetIso L₂
  let α : d₃.moduleFunctor ⋙ W H Λ ≅ (d.moduleFunctor ⋙ d₂.moduleFunctor) ⋙ W H Λ :=
    d₃.moduleSetIso ≪≫ β.symm
  obtain ⟨i, hi⟩ := moduleIsoOfScalars J H Λ _ _ α (by
    intro M r
    apply (cancel_mono (β.hom.app M)).mp
    change _ ≫ ((d₃.moduleSetIso.hom.app M ≫ β.inv.app M) ≫ β.hom.app M) =
      (d₃.moduleSetIso.hom.app M ≫ β.inv.app M) ≫
        (U H).map (scalarEndomorphism H Λ
          (d₂.moduleFunctor.obj (d.moduleFunctor.obj M)) r) ≫ β.hom.app M
    simp only [Iso.inv_hom_id_app, Category.comp_id, Category.assoc]
    rw [liftScalarMap J H Λ (L ⋙ L₂) (R₂ ⋙ R) (adj.comp adj₂) _ d₃ M r]
    have hb : (U H).map (scalarEndomorphism H Λ
          (d₂.moduleFunctor.obj (d.moduleFunctor.obj M)) r) ≫ β.hom.app M =
        β.hom.app M ≫ L₂.map (L.map ((U J).map (scalarEndomorphism J Λ M r))) := by
      change _ ≫ (d₂.moduleSetIso.hom.app (d.moduleFunctor.obj M) ≫
        L₂.map (d.moduleSetIso.hom.app M)) =
        (d₂.moduleSetIso.hom.app (d.moduleFunctor.obj M) ≫
          L₂.map (d.moduleSetIso.hom.app M)) ≫ _
      rw [← Category.assoc, liftScalarMap K H Λ L₂ R₂ adj₂ hL₂ d₂
        (d.moduleFunctor.obj M) r, Category.assoc, ← L₂.map_comp,
        liftScalarMap J K Λ L R adj hL d M r, L₂.map_comp, Category.assoc]
    rw [hb]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rfl)
  refine ⟨i, fun M ↦ ?_⟩
  have h := congr_app hi M
  change (W H Λ).map (i.hom.app M) =
    d₃.moduleSetIso.hom.app M ≫ β.inv.app M at h
  change (W H Λ).map (i.hom.app M) ≫ β.hom.app M = _
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem forgetAbelianSheavesPreservesFiniteLimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    PreservesFiniteLimits (U J) := by
  have : PreservesFiniteLimits (U J ⋙ sheafToPresheaf J (Type u)) := by
    change PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj
        (forget AddCommGrpCat.{u}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J (Type u))

set_option backward.isDefEq.respectTransparency false in
private theorem localizationComparison
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    (X : C) :
    ∃ (Rₓ : Sheaf (J.over X) (Type u) ⥤ Sheaf J (Type u))
      (adjₓ : J.overPullback (Type u) X ⊣ Rₓ)
      (hLₓ : PreservesFiniteLimits (J.overPullback (Type u) X))
      (dₓ : ConstantLeftModuleInverseImageLift J (J.over X) Λ
        (J.overPullback (Type u) X) Rₓ adjₓ hLₓ)
      (c : ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over X ≅
        (constantSheaf (J.over X) RingCat.{u}).obj (RingCat.of Λ)),
      (∀ (T : (Over X)ᵒᵖ) (r : Λ), c.hom.hom.app T
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app
          ((Over.forget X).op.obj T) r) =
        (toSheafify (J.over X)
          ((Functor.const (Over X)ᵒᵖ).obj (RingCat.of Λ))).app T r) ∧
      ∃ i : dₓ.moduleFunctor ≅
          SheafOfModules.overFunctor ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) X ⋙
            SheafOfModules.restrictScalars c.inv,
        ∀ (M : Modules J Λ) (T : (Over X)ᵒᵖ)
          (x : (dₓ.moduleFunctor.obj M).val.obj T),
          (i.hom.app M).val.app T x = (dₓ.moduleSetIso.hom.app M).hom.app T x := by
  let Rₓ := (Over.forget X).sheafPushforwardCocontinuous (Type u) (J.over X) J
  let adjₓ : J.overPullback (Type u) X ⊣ Rₓ :=
    (Over.forget X).sheafAdjunctionCocontinuous (Type u) (J.over X) J
  let hLₓ : PreservesFiniteLimits (J.overPullback (Type u) X) := inferInstance
  obtain ⟨dₓ⟩ := constantLeftModuleTransport J (J.over X) Λ _ Rₓ adjₓ hLₓ
  let e := ((Over.forget X).pushforwardContinuousSheafificationCompatibility
    RingCat.{u} (J.over X) J).app ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  let c : ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)).over X ≅
      (constantSheaf (J.over X) RingCat.{u}).obj (RingCat.of Λ) := e.symm
  have hc (T : (Over X)ᵒᵖ) (r : Λ) : c.hom.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app
        ((Over.forget X).op.obj T) r) =
      (toSheafify (J.over X)
        ((Functor.const (Over X)ᵒᵖ).obj (RingCat.of Λ))).app T r := by
    have h := congrArg (fun f ↦ f.app T r)
      ((Over.forget X).toSheafify_pullbackSheafificationCompatibility
        RingCat.{u} (J.over X) J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))
    change e.hom.hom.app T
      ((toSheafify (J.over X)
        ((Functor.const (Over X)ᵒᵖ).obj (RingCat.of Λ))).app T r) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app
        ((Over.forget X).op.obj T) r at h
    change e.inv.hom.app T _ = _
    exact (congrArg (fun z ↦ e.inv.hom.app T z) h).symm.trans (by
      exact congrArg (fun f ↦ f.hom.app T
      ((toSheafify (J.over X)
        ((Functor.const (Over X)ᵒᵖ).obj (RingCat.of Λ))).app T r)) e.hom_inv_id)
  let G := SheafOfModules.overFunctor
    ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) X ⋙
      SheafOfModules.restrictScalars c.inv
  have : PreservesFiniteLimits (V J Λ) := inferInstance
  have : PreservesFiniteLimits (U J) := forgetAbelianSheavesPreservesFiniteLimits J
  have : PreservesFiniteLimits (W J Λ) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (G ⋙ W (J.over X) Λ) := by
    change PreservesFiniteLimits (W J Λ ⋙ J.overPullback (Type u) X)
    infer_instance
  have : PreservesFiniteLimits (V (J.over X) Λ) := inferInstance
  have : PreservesFiniteLimits (U (J.over X)) :=
    forgetAbelianSheavesPreservesFiniteLimits (J.over X)
  have : PreservesFiniteLimits (W (J.over X) Λ) := comp_preservesFiniteLimits _ _
  have : ReflectsFiniteLimits (W (J.over X) Λ) := inferInstance
  have : PreservesFiniteLimits G :=
    preservesFiniteLimits_of_reflects_of_preserves G (W (J.over X) Λ)
  let := dₓ.preservesFiniteLimits
  let α : dₓ.moduleFunctor ⋙ W (J.over X) Λ ≅ G ⋙ W (J.over X) Λ := dₓ.moduleSetIso
  obtain ⟨i, hi⟩ := moduleIsoOfScalars J (J.over X) Λ _ G α (by
    intro M r
    have h := liftScalarMap J (J.over X) Λ _ Rₓ adjₓ hLₓ dₓ M r
    change _ ≫ dₓ.moduleSetIso.hom.app M = dₓ.moduleSetIso.hom.app M ≫ _
    rw [h]
    congr 1
    ext T x
    change ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app
        ((Over.forget X).op.obj T) r) • (show M.val.obj ((Over.forget X).op.obj T) from x) =
      (c.inv.hom.app T
        ((toSheafify (J.over X)
          ((Functor.const (Over X)ᵒᵖ).obj (RingCat.of Λ))).app T r)) •
            (show M.val.obj ((Over.forget X).op.obj T) from x)
    congr 1
    rw [← hc T r]
    exact (congrArg (fun f ↦ f.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app
        ((Over.forget X).op.obj T) r)) c.hom_inv_id).symm)
  refine ⟨Rₓ, adjₓ, hLₓ, dₓ, c, hc, i, ?_⟩
  intro M T x
  exact congrArg (fun f ↦ f.hom.app T x) (congr_app hi M)


/-- Existence of normalized composition, presentation, and localization comparisons.
Source: Stacks Project, Sites, Tags 00YV, 00XZ and 00Y0
(blueprint: lem-pe-constant-left-module-inverse-image-coherence).

Proof: For a composite, compose the two underlying-set comparisons. On abelian
sheaves the transported addition maps commute with this composite by naturality of
product comparisons. The constant scalar endomorphisms commute by the scalar
compatibility equations, first for the first inverse image and then for the second.
The abelian comparison is therefore linear on constant scalars. Every section of
the constant ring is locally a constant scalar; naturality and separatedness of the
target module sheaf upgrade this to linearity on all scalar sections. The inverse
set comparison satisfies the same equations. These maps are inverse module maps,
and their naturality follows after applying the faithful underlying-set functor.
For a change of presentation, insert the specified natural isomorphism between set
inverse images in place of the composite comparison. Naturality of that isomorphism
with respect to addition and each scalar endomorphism proves the same two equations,
so the preceding construction again gives the required normalized module isomorphism.
For localization, the forgetful functor from the over-site is continuous and
cocontinuous. Its sectionwise restriction has a right adjoint and preserves finite
limits. Apply constant-left-module transport to that adjunction. Restriction commutes
with sheafification by the continuous-cocontinuous sheafification comparison; on the
constant ring presheaf this gives the stated coefficient isomorphism and its equation
on constants. The transported addition is sectionwise addition, and its constant
scalar operations are the original ones. The same local linearity argument therefore
identifies the transported module with sectionwise restriction followed by scalar
restriction along the inverse coefficient isomorphism. Its underlying map is exactly
the supplied set comparison, which proves the last displayed equation. -/
theorem constantLeftModuleInverseImageCoherence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageLift J K Λ L R adj hL) :
    Nonempty (ConstantLeftModuleInverseImageCoherence J K Λ L R adj hL d) := by
  refine ⟨{
    composition_coherence := ?_
    presentation_coherence := ?_
    localization_coherence := ?_ }⟩
  · intro E _ H _ L₂ R₂ adj₂ hL₂ d₂ d₃
    exact compositionComparison J K H Λ L R adj hL L₂ R₂ adj₂ hL₂ d d₂ d₃
  · intro L' R' adj' hL' d' e
    exact presentationComparison J K Λ L L' R R' adj hL adj' hL' d d' e
  · exact localizationComparison J Λ

end CategoryTheory
