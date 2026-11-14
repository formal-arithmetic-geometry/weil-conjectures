/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.Topology.Sheaves.CechComparison

/-! # A correction cochain from local horseshoe lifts

## References

* Stacks Project, Tags 01EQ and 0B8S
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

local instance localInst_CechHorseshoeCorrectionCochain_1
    (R : Type u) [Ring R] (J : Type*) [Small.{u} J] :
    HasLimitsOfShape (Discrete J) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

private theorem cechMapπ {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (f : F ⟶ G) (n : ℕ) (y : Fin (n + 1) → ι)
    (v : ((cechComplexFunctor U).obj F.presheafModuleCat).X n) :
    TopCat.Presheaf.cechComplexFunctorπ U G.presheafModuleCat n y
      (((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          f.val)).f n v) =
      f.val.app (op (∏ᶜ fun k : Fin (n + 1) ↦ U (y k)))
        (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y v) := by
  exact congrArg (fun m ↦ m v)
    (TopCat.Presheaf.cechComplexFunctor_map_f_π U F.presheafModuleCat
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        f.val) n y)

private theorem moduleCechZero_naturality {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (f : F ⟶ G) :
    moduleCechZero U F ≫
        ((CategoryTheory.cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            f.val)).f 0 =
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map f ≫ moduleCechZero U G := by
  apply Pi.hom_ext
  intro y
  dsimp [moduleCechZero, CategoryTheory.cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor, FormalCoproduct.cosimplicialObjectFunctor,
    FormalCoproduct.evalOp, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.map]
  simp only [Category.assoc]
  erw [Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
  ext x
  simp only [ModuleCat.comp_apply]
  exact PresheafOfModules.naturality_apply f.val _ x

/-- The two restrictions of a global section to each pairwise intersection agree (Stacks, Tag 01EQ).
-/
private theorem moduleCechZero_d {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) :
    moduleCechZero U F ≫
      ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).d 0 1 = 0 := by
  change moduleCechZero U F ≫
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
      ((FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj F.presheafModuleCat) 0 = 0
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Fin.sum_univ_two]
  simp only [
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  rw [← sub_eq_add_neg]
  apply sub_eq_zero.mpr
  apply Pi.hom_ext
  intro y
  dsimp [moduleCechZero, FormalCoproduct.cosimplicialObjectFunctor,
    FormalCoproduct.evalOp, CosimplicialObject.δ]
  simp only [Category.assoc]
  erw [Pi.lift_comp_π, Pi.lift_comp_π]
  erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π_assoc]
  congr 1
  erw [← F.presheafModuleCat.map_comp, ← F.presheafModuleCat.map_comp]
  congr 1

private theorem cechMap_injective {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : X.Modules} (f : F ⟶ G) [Mono f] (n : ℕ) :
    Function.Injective (((cechComplexFunctor U).map
      ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
        f.val)).f n) := by
  intro v w h
  apply TopCat.Presheaf.cechComplexFunctor_ext U F.presheafModuleCat
  intro y
  let E := SheafOfModules.evaluation.{u} X.ringCatSheaf
    (op (∏ᶜ fun k : Fin (n + 1) ↦ U (y k)))
  apply (ModuleCat.mono_iff_injective (E.map f)).mp inferInstance
  change f.val.app _ _ = f.val.app _ _
  rw [← cechMapπ, ← cechMapπ, h]

private theorem cechZeroπ {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : X.Modules) (v : F.val.obj (op ⊤)) (y : Fin 1 → ι) :
    TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat 0 y
      (moduleCechZero U F v) =
      F.val.presheaf.map (homOfLE (le_top : (∏ᶜ fun k : Fin 1 ↦ U (y k)) ≤ ⊤)).op v := by
  change ((moduleCechZero U F ≫
    TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat 0 y) v) = _
  dsimp only [moduleCechZero, TopCat.Presheaf.cechComplexFunctorπ]
  rw [Category.assoc]
  have hh := Pi.lift_comp_π (fun w : Fin 1 → ι ↦
    F.presheafModuleCat.map (homOfLE (le_top (a := ∏ᶜ fun l ↦ U (w l)))).op) y
  erw [hh]
  rfl

set_option maxHeartbeats 400000 in
-- The sectionwise and two cochain calculations repeatedly compare categorical product modules.
set_option backward.isDefEq.respectTransparency false in
/-- A Cech zero cochain with prescribed resolution and Cech differentials
(Stacks, Tags 01EQ, 0B8S). -/
theorem cech_horseshoe_correction_cochain (X : Scheme.{u})
    (S : ShortComplex X.Modules)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ X.Modules).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ X.Modules).map S.g ≫ IC.ι)
    (hrows : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) k)).ShortExact)
    {ι : Type u} (U : ι → X.Opens)
    (q : S.X₃.val.obj (op ⊤)) (x : ∀ i : ι, S.X₂.val.obj (op (U i)))
    (hx : ∀ i : ι, S.g.val.app (op (U i)) (x i) =
      S.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op q)
    (b : (IB.cocomplex.X 0).val.obj (op ⊤))
    (a : (RingedSpace.globalSectionsComplex IA).cycles 1)
    (hb : (β.f 0).val.app (op ⊤) b = (IC.ι.f 0).val.app (op ⊤) q)
    (ha : (α.f 1).val.app (op ⊤)
      ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) =
        (IB.cocomplex.d 0 1).val.app (op ⊤) b)
    (z : ((cechComplexFunctor U).obj S.X₁.presheafModuleCat).cycles 1)
    (hz : ∀ y : Fin 2 → ι,
      S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
        ((Pi.π (fun w : Fin 2 → ι ↦
          S.X₁.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
          (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) =
        S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0))) :
    ∃ t : ((moduleCechDouble U IA).X 0).X 0,
      (((moduleCechDouble U IA).d 0 1).f 0) t =
        -(moduleCechZero U (IA.cocomplex.X 1))
          ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) ∧
      (((moduleCechDouble U IA).X 0).d 0 1) t =
        ((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (IA.ι.f 0).val)).f 1
          (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z) := by
  classical
  let jA : S.X₁ ⟶ IA.cocomplex.X 0 := IA.ι.f 0
  let jB : S.X₂ ⟶ IB.cocomplex.X 0 := IB.ι.f 0
  let F : X.Modules ⥤ CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℕ :=
    SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op ⋙
      cechComplexFunctor U
  let : F.Additive := cechComplexFunctor_presheafModuleCat_additive X U
  let A₀ := (cechComplexFunctor U).obj (IA.cocomplex.X 0).presheafModuleCat
  let B₀ := (cechComplexFunctor U).obj (IB.cocomplex.X 0).presheafModuleCat
  let B := (cechComplexFunctor U).obj S.X₂.presheafModuleCat
  let x₀ : B.X 0 := (ModuleCat.piIsoPi
    (fun y : Fin 1 → ι ↦ S.X₂.presheafModuleCat.obj
      (op (∏ᶜ fun k : Fin 1 ↦ U (y k))))).inv
    (fun y ↦ S.X₂.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op (x (y 0)))
  have hx₀ (y : Fin 2 → ι) :
      TopCat.Presheaf.cechComplexFunctorπ U (S.X₂.presheafModuleCat) 1 y (B.d 0 1 x₀) =
        S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0)) := by
    rw [TopCat.Presheaf.cechComplexFunctorπ_d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_zsmul]
    dsimp only [x₀]
    rw [TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv,
      TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv]
    have h₁ := TopCat.Presheaf.map_map_apply
      (S.X₂.presheafModuleCat)
      (Pi.π (fun k : Fin 1 ↦ U ((y ∘ (0 : Fin 2).succAbove) k)) 0).op
      (Pi.lift fun l ↦ Pi.π (fun l : Fin 2 ↦ U (y l))
        ((0 : Fin 2).succAbove l)).op (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1))
    have h₀ := TopCat.Presheaf.map_map_apply
      (S.X₂.presheafModuleCat)
      (Pi.π (fun k : Fin 1 ↦ U ((y ∘ (1 : Fin 2).succAbove) k)) 0).op
      (Pi.lift fun l ↦ Pi.π (fun l : Fin 2 ↦ U (y l))
        ((1 : Fin 2).succAbove l)).op (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0))
    have h := congrArg₂ (fun a b ↦ a + -b) h₁ h₀
    dsimp [presheafModuleCat, PresheafOfModules.forgetToPresheafModuleCat,
      PresheafOfModules.forgetToPresheafModuleCatObj,
      PresheafOfModules.forgetToPresheafModuleCatObjMap,
      PresheafOfModules.presheaf] at h ⊢
    simp only [AddMonoidHom.mk'_apply,
      sub_eq_add_neg] at h ⊢
    convert h using 1
    rfl
  have hdx : B.d 0 1 x₀ = (F.map S.f).f 1
      (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z) := by
    apply TopCat.Presheaf.cechComplexFunctor_ext U S.X₂.presheafModuleCat
    intro y
    change TopCat.Presheaf.cechComplexFunctorπ U S.X₂.presheafModuleCat 1 y
      (B.d 0 1 x₀) = TopCat.Presheaf.cechComplexFunctorπ U S.X₂.presheafModuleCat 1 y
      (((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          S.f.val)).f 1 _)
    rw [hx₀, cechMapπ]
    exact (hz y).symm
  let v : B₀.X 0 := (show B₀.X 0 from (F.map jB).f 0 x₀) -
    (show B₀.X 0 from moduleCechZero U (IB.cocomplex.X 0) b)
  have hιB₀ : jB ≫ β.f 0 = S.g ≫ IC.ι.f 0 := by
    simpa [jB] using congrArg (fun f ↦ f.f 0) hιB
  have hvπ (y : Fin 1 → ι) :
      TopCat.Presheaf.cechComplexFunctorπ U (IB.cocomplex.X 0).presheafModuleCat 0 y v =
      jB.val.app _
        (S.X₂.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op (x (y 0))) -
      (show (IB.cocomplex.X 0).val.obj (op (∏ᶜ fun k : Fin 1 ↦ U (y k))) from
        (IB.cocomplex.X 0).val.presheaf.map
          (homOfLE (le_top : (∏ᶜ fun k : Fin 1 ↦ U (y k)) ≤ ⊤)).op b) := by
    dsimp only [v]
    rw [map_sub]
    apply congrArg₂ (fun v w : (IB.cocomplex.X 0).val.obj
      (op (∏ᶜ fun k : Fin 1 ↦ U (y k))) ↦ v - w)
    · have hπx : TopCat.Presheaf.cechComplexFunctorπ U S.X₂.presheafModuleCat 0 y x₀ =
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op (x (y 0)) := by
        dsimp only [x₀]
        rw [TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv]
      exact (cechMapπ U jB 0 y x₀).trans (congrArg (jB.val.app _) hπx)
    · exact cechZeroπ U (IB.cocomplex.X 0) b y
  have hvβ (y : Fin 1 → ι) :
      (β.f 0).val.app (op (∏ᶜ fun k : Fin 1 ↦ U (y k)))
        (TopCat.Presheaf.cechComplexFunctorπ
          U (IB.cocomplex.X 0).presheafModuleCat 0 y v) = 0 := by
    rw [hvπ, map_sub]
    have hi := congrArg (fun f ↦ f.val.app (op (∏ᶜ fun k : Fin 1 ↦ U (y k)))) hιB₀
    have hi' := ConcreteCategory.congr_hom hi
      (S.X₂.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op (x (y 0)))
    change (β.f 0).val.app _ (jB.val.app _ _) =
      (IC.ι.f 0).val.app _ (S.g.val.app _ _) at hi'
    rw [hi']
    erw [PresheafOfModules.naturality_apply S.g.val,
      PresheafOfModules.naturality_apply (β.f 0).val, hx, hb]
    erw [← PresheafOfModules.naturality_apply (IC.ι.f 0).val]
    have hm := S.X₃.val.map_comp_apply
      (homOfLE (le_top : U (y 0) ≤ ⊤)).op
      (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op q
    erw [← hm]
    apply sub_eq_zero.mpr
    congr 2
  have he (W : X.Opens) := by
    let E := SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)
    let : E.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} X.ringCatSheaf ⋙
        PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op W)).Additive)
    let : PreservesLimits E := inferInstanceAs
      (PreservesLimits (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
        PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op W)))
    exact (hrows 0).exact.map_of_mono_of_preservesKernel E (hrows 0).mono_f inferInstance
  choose c hc using fun y : Fin 1 → ι ↦
    (ShortComplex.moduleCat_exact_iff _).mp (he (∏ᶜ fun k : Fin 1 ↦ U (y k)))
      (TopCat.Presheaf.cechComplexFunctorπ
        U (IB.cocomplex.X 0).presheafModuleCat 0 y v) (hvβ y)
  let t : A₀.X 0 := (ModuleCat.piIsoPi
    (fun y : Fin 1 → ι ↦ (IA.cocomplex.X 0).presheafModuleCat.obj
      (op (∏ᶜ fun k : Fin 1 ↦ U (y k))))).inv c
  have hαt : (F.map (α.f 0)).f 0 t = v := by
    apply TopCat.Presheaf.cechComplexFunctor_ext
      U (IB.cocomplex.X 0).presheafModuleCat
    intro y
    change TopCat.Presheaf.cechComplexFunctorπ
      U (IB.cocomplex.X 0).presheafModuleCat 0 y
      (((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (α.f 0).val)).f 0 t) = _
    rw [cechMapπ]
    dsimp only [t]
    rw [TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv]
    exact hc y
  refine ⟨t, ?_, ?_⟩
  · have : Mono (α.f 1) := (hrows 1).mono_f
    apply cechMap_injective U (α.f 1) 0
    change (F.map (α.f 1)).f 0 ((F.map (IA.cocomplex.d 0 1)).f 0 t) =
      (F.map (α.f 1)).f 0 (-(moduleCechZero U (IA.cocomplex.X 1))
        ((RingedSpace.globalSectionsComplex IA).iCycles 1 a))
    have hcomm := congrArg (fun f ↦ (F.map f).f 0) (α.comm 0 1)
    rw [F.map_comp, F.map_comp, HomologicalComplex.comp_f,
      HomologicalComplex.comp_f] at hcomm
    have hcomm' := ConcreteCategory.congr_hom hcomm t
    change (F.map (IB.cocomplex.d 0 1)).f 0 ((F.map (α.f 0)).f 0 t) =
      (F.map (α.f 1)).f 0 ((F.map (IA.cocomplex.d 0 1)).f 0 t) at hcomm'
    rw [← hcomm', hαt]
    dsimp only [v]
    rw [map_sub, map_neg]
    have haug : (F.map jB).f 0 ≫
        (F.map (IB.cocomplex.d 0 1)).f 0 = 0 := by
      have h : jB ≫ IB.cocomplex.d 0 1 = 0 := by
        dsimp only [jB]
        simp
      rw [← HomologicalComplex.comp_f, ← F.map_comp, h, F.map_zero]
      rfl
    have haug' := ConcreteCategory.congr_hom haug x₀
    change (F.map (IB.cocomplex.d 0 1)).f 0 ((F.map jB).f 0 x₀) = 0 at haug'
    rw [haug', zero_sub]
    have hd := ConcreteCategory.congr_hom
      (moduleCechZero_naturality U (IB.cocomplex.d 0 1)) b
    change (F.map (IB.cocomplex.d 0 1)).f 0 (moduleCechZero U (IB.cocomplex.X 0) b) =
      moduleCechZero U (IB.cocomplex.X 1) ((IB.cocomplex.d 0 1).val.app (op ⊤) b) at hd
    have hα := ConcreteCategory.congr_hom (moduleCechZero_naturality U (α.f 1))
      ((RingedSpace.globalSectionsComplex IA).iCycles 1 a)
    change (F.map (α.f 1)).f 0 (moduleCechZero U (IA.cocomplex.X 1) _) =
      moduleCechZero U (IB.cocomplex.X 1) ((α.f 1).val.app (op ⊤) _) at hα
    rw [hd, ← ha, ← hα]
  · have : Mono (α.f 0) := (hrows 0).mono_f
    apply cechMap_injective U (α.f 0) 1
    change (F.map (α.f 0)).f 1 (A₀.d 0 1 t) =
      (F.map (α.f 0)).f 1 ((F.map jA).f 1
        (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z))
    have hcomm := ConcreteCategory.congr_hom ((F.map (α.f 0)).comm 0 1) t
    change B₀.d 0 1 ((F.map (α.f 0)).f 0 t) =
      (F.map (α.f 0)).f 1 (A₀.d 0 1 t) at hcomm
    rw [← hcomm, hαt]
    dsimp only [v]
    rw [map_sub]
    have hzero := ConcreteCategory.congr_hom
      (moduleCechZero_d U (IB.cocomplex.X 0)) b
    change B₀.d 0 1 (moduleCechZero U (IB.cocomplex.X 0) b) = 0 at hzero
    rw [hzero, sub_zero]
    have haug := ConcreteCategory.congr_hom ((F.map jB).comm 0 1) x₀
    change B₀.d 0 1 ((F.map jB).f 0 x₀) =
      (F.map jB).f 1 (B.d 0 1 x₀) at haug
    rw [haug, hdx]
    have hιA₀ : jA ≫ α.f 0 = S.f ≫ jB := by
      simpa [jA, jB] using congrArg (fun f ↦ f.f 0) hιA
    have hι := congrArg (fun f ↦ (F.map f).f 1) hιA₀
    rw [F.map_comp, F.map_comp, HomologicalComplex.comp_f,
      HomologicalComplex.comp_f] at hι
    exact (ConcreteCategory.congr_hom hι
      (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)).symm

end AlgebraicGeometry.Scheme.Modules
