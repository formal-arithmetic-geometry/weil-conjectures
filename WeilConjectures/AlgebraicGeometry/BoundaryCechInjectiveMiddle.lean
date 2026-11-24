/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeRepresentative
import WeilConjectures.AlgebraicGeometry.CechHorseshoeLiftClass
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Injective middle term: the Čech local-lift cocycle is the connecting class

## References

* Stacks Project, Tags 01EQ, 01EP and 0B8S
-/

@[expose] public section

universe u v wC wD

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private local instance boundaryCechModuleProducts (R : Type u) [Ring R] (J : Type v)
    [Small.{u} J] : HasLimitsOfShape (Discrete J) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_lift_cocycle (X : Scheme.{u})
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)) (hS : S.ShortExact)
    {ι : Type u} (U : ι → X.Opens)
    (q : S.X₃.val.obj (op ⊤)) (x : ∀ i : ι, S.X₂.val.obj (op (U i)))
    (hx : ∀ i : ι, S.g.val.app (op (U i)) (x i) =
      S.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op q) :
    ∃ z : ((cechComplexFunctor U).obj (presheafModuleCat (X := X) S.X₁)).cycles 1,
      ∀ y : Fin 2 → ι,
        S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
          ((Pi.π (fun w : Fin 2 → ι ↦
            (presheafModuleCat (X := X) S.X₁).obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
            (((cechComplexFunctor U).obj (presheafModuleCat (X := X) S.X₁)).iCycles 1 z)) =
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
            S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0)) := by
  classical
  let A := (cechComplexFunctor U).obj (presheafModuleCat (X := X) S.X₁)
  let B := (cechComplexFunctor U).obj (presheafModuleCat (X := X) S.X₂)
  let f := (cechComplexFunctor U).map
    ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map S.f.val)
  have hf (n : ℕ) (y : Fin (n + 1) → ι) (a : A.X n) :
      TopCat.Presheaf.cechComplexFunctorπ U
        (presheafModuleCat (X := X) S.X₂) n y (f.f n a) =
        S.f.val.app (op (∏ᶜ fun k : Fin (n + 1) ↦ U (y k)))
          (TopCat.Presheaf.cechComplexFunctorπ
          U (presheafModuleCat (X := X) S.X₁) n y a) := by
    exact congrArg (fun m ↦ m a)
      (TopCat.Presheaf.cechComplexFunctor_map_f_π U (presheafModuleCat (X := X) S.X₁)
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          S.f.val) n y)
  let b : B.X 0 := (ModuleCat.piIsoPi
    (fun y : Fin 1 → ι ↦ (presheafModuleCat (X := X) S.X₂).obj
      (op (∏ᶜ fun k : Fin 1 ↦ U (y k))))).inv
    (fun y ↦ S.X₂.val.presheaf.map (Pi.π (fun k : Fin 1 ↦ U (y k)) 0).op (x (y 0)))
  have hb (y : Fin 2 → ι) :
      TopCat.Presheaf.cechComplexFunctorπ U (presheafModuleCat (X := X) S.X₂) 1 y (B.d 0 1 b) =
        S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0)) := by
    rw [TopCat.Presheaf.cechComplexFunctorπ_d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_zsmul]
    dsimp only [b]
    rw [TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv,
      TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv]
    have h₁ := TopCat.Presheaf.map_map_apply
      (presheafModuleCat (X := X) S.X₂)
      (Pi.π (fun k : Fin 1 ↦ U ((y ∘ (0 : Fin 2).succAbove) k)) 0).op
      (Pi.lift fun l ↦ Pi.π (fun l : Fin 2 ↦ U (y l))
        ((0 : Fin 2).succAbove l)).op (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1))
    have h₀ := TopCat.Presheaf.map_map_apply
      (presheafModuleCat (X := X) S.X₂)
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
  have he (W : X.Opens) := by
    let E := SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)
    let : E.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} X.ringCatSheaf ⋙
        PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op W)).Additive)
    exact hS.exact.map_of_mono_of_preservesKernel E hS.mono_f inferInstance
  have hz (y : Fin 2 → ι) :
      S.g.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
        (TopCat.Presheaf.cechComplexFunctorπ
        U (presheafModuleCat (X := X) S.X₂) 1 y (B.d 0 1 b)) = 0 := by
    rw [hb, map_sub]
    erw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hx, hx]
    have h₁ := S.X₃.val.map_comp_apply
      (homOfLE (le_top : U (y 1) ≤ ⊤)).op
      (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op q
    have h₀ := S.X₃.val.map_comp_apply
      (homOfLE (le_top : U (y 0) ≤ ⊤)).op
      (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op q
    erw [← h₁, ← h₀]
    have hi : (homOfLE (le_top : U (y 1) ≤ ⊤)).op ≫
        (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op =
        (homOfLE (le_top : U (y 0) ≤ ⊤)).op ≫
          (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op := Subsingleton.elim _ _
    rw [hi, sub_self]
  choose a ha using fun y : Fin 2 → ι ↦
    (ShortComplex.moduleCat_exact_iff _).mp (he (∏ᶜ fun k : Fin 2 ↦ U (y k)))
      (TopCat.Presheaf.cechComplexFunctorπ U (presheafModuleCat (X := X) S.X₂) 1 y (B.d 0 1 b))
      (hz y)
  let a' : A.X 1 := (ModuleCat.piIsoPi
    (fun y : Fin 2 → ι ↦ (presheafModuleCat (X := X) S.X₁).obj
      (op (∏ᶜ fun k : Fin 2 ↦ U (y k))))).inv a
  have hfa : f.f 1 a' = B.d 0 1 b := by
    apply TopCat.Presheaf.cechComplexFunctor_ext U (presheafModuleCat (X := X) S.X₂)
    intro y
    rw [hf]
    dsimp only [a']
    rw [TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv]
    exact ha y
  have hda : A.d 1 2 a' = 0 := by
    apply TopCat.Presheaf.cechComplexFunctor_ext U (presheafModuleCat (X := X) S.X₁)
    intro y
    let E := SheafOfModules.evaluation X.ringCatSheaf
      (op (∏ᶜ fun k : Fin 3 ↦ U (y k)))
    have : Mono S.f := hS.mono_f
    apply (ModuleCat.mono_iff_injective (E.map S.f)).mp inferInstance
    change S.f.val.app _ _ = S.f.val.app _ _
    rw [← hf]
    have hd : f.f 2 (A.d 1 2 a') = 0 := by
      have hc := congrArg (fun m ↦ m a') (f.comm 1 2)
      change B.d 1 2 (f.f 1 a') = f.f 2 (A.d 1 2 a') at hc
      rw [← hc, hfa]
      exact congrArg (fun m ↦ m b) (B.d_comp_d 0 1 2)
    rw [hd]
    simp only [map_zero]
  refine ⟨A.cyclesMk a' 2 (by simp) hda, ?_⟩
  intro y
  change S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
    (TopCat.Presheaf.cechComplexFunctorπ U (presheafModuleCat (X := X) S.X₁) 1 y
      (A.iCycles 1 (A.cyclesMk a' 2 (by simp) hda))) = _
  have hi : A.iCycles 1 (A.cyclesMk a' 2 (by simp) hda) = a' :=
    HomologicalComplex.i_cyclesMk A a' 2 (by simp) hda
  rw [hi, ← hf, hfa, hb]

set_option backward.isDefEq.respectTransparency false in
/-- For a short exact sequence `0 → A → I → Q → 0` of `O_X`-modules with `I` injective, an
open covering `U`, a global section `q` of `Q` and local lifts `x i ∈ I(U i)` of `q|_{U i}`,
the differences of the lifts form a Čech `1`-cocycle `z` with values in `A`, and the Čech
comparison map sends the class of `z` to the connecting class `∂(q)`
(Stacks, Tags 01EQ, 01EP and 0B8S). -/
theorem boundary_cech_injective_middle (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) [Injective S.X₂]
    {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (c : ((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).homology 1 ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace 1).obj S.X₁)
    (hc : IsModuleCechComparison U S.X₁ 1 c)
    (q : S.X₃.val.obj (op ⊤)) (x : ∀ i : ι, S.X₂.val.obj (op (U i)))
    (hx : ∀ i : ι, S.g.val.app (op (U i)) (x i) =
      S.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op q) :
    ∃ z : ((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).cycles 1,
      (∀ y : Fin 2 → ι,
        S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
          ((Pi.π (fun w : Fin 2 → ι ↦
            S.X₁.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
            (((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) =
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (x (y 1)) -
            S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (x (y 0))) ∧
      c (((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).homologyπ 1 z) =
        RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ q)  := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  obtain ⟨z, hz⟩ := local_lift_cocycle X S hS U q x hx
  refine ⟨z, hz, ?_⟩
  obtain ⟨IA, IB, IC, α, β, hιA, hιB, hαβ, hrows⟩ :=
    InjectiveResolution.exists_horseshoe_resolutions S hS
  have hr k := (hrows k).1
  obtain ⟨b, a, hb, ha, hboundary⟩ :=
    boundary_horseshoe_representative X S IA IB IC α β hαβ hιA hιB hr hS q
  have htotal := cech_horseshoe_lift_class X S IA IB IC α β hαβ hιA hιB hr
    U q x hx b a hb ha z hz
  let e := IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1
  let αH := HomologicalComplex.homologyMap (moduleCechAlpha U IA) 1
  let : IsIso αH := moduleCechAlpha_isIso U hcover IA 1
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  apply (ModuleCat.mono_iff_injective αH).mp inferInstance
  have hcomparison := congrArg
    (fun f ↦ f (((cechComplexFunctor U).obj S.X₁.presheafModuleCat).homologyπ 1 z))
    (hc IA)
  change αH (e.hom (c _)) =
    HomologicalComplex.homologyMap (moduleCechBeta U IA) 1 _ at hcomparison
  rw [hcomparison, hboundary]
  exact htotal

end AlgebraicGeometry.Scheme.Modules
