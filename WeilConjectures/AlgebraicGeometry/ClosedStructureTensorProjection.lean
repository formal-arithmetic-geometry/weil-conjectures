/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.ClosedStructureTensorProjectionStalk

/-! # The ordinary projection formula for a closed structure sheaf

## References

* Stacks Project, Tags 08KS, 01CB and 0098
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 512
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Opposite TopologicalSpace Scheme.Modules in
private noncomputable def projectionPairing {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) →ₗ[Γ(Y, U)]
      Γ((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf), U) →ₗ[Γ(Y, U)]
      Γ((pushforward i).obj ((tensorPullback i).obj M), U) :=
  LinearMap.mk₂ Γ(Y, U)
    (fun s r ↦ (show Γ(Z, i ⁻¹ᵁ U) from r) •
      (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ U) from
        ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app M).app U s))
    (by intros; rw [map_add, smul_add])
    (by
      intro a s r
      rw [Hom.app_smul]
      change (show Γ(Z, i ⁻¹ᵁ U) from r) •
        (i.app U a • (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ U) from _)) =
        i.app U a • ((show Γ(Z, i ⁻¹ᵁ U) from r) •
          (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ U) from _))
      exact smul_comm _ _ _)
    (by
      intro s r r'
      change ((show Γ(Z, i ⁻¹ᵁ U) from r) + (show Γ(Z, i ⁻¹ᵁ U) from r')) •
        (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ U) from _) = _
      exact add_smul _ _ _)
    (by
      intro a s r
      change (i.app U a * (show Γ(Z, i ⁻¹ᵁ U) from r)) •
        (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ U) from _) =
        i.app U a • ((show Γ(Z, i ⁻¹ᵁ U) from r) •
          (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ U) from _))
      exact mul_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Opposite TopologicalSpace Scheme.Modules in
private theorem projectionPairing_natural {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (M : Y.Modules) {U V : Y.Opensᵒᵖ} (f : U ⟶ V)
    (s : M.val.obj U)
    (r : ((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).val.obj U) :
    projectionPairing i M V.unop (M.val.map f s)
        (((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).val.map f r) =
      ((pushforward i).obj ((tensorPullback i).obj M)).val.map f
        (projectionPairing i M U.unop s r) := by
  have hn := PresheafOfModules.naturality_apply
    ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app M).val f s
  change (show Γ(Z, i ⁻¹ᵁ V.unop) from
    ((SheafOfModules.unit Z.ringCatSheaf).val.map ((Opens.map i.base).op.map f) r)) •
      (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ V.unop) from
        ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app M).val.app V
          (M.val.map f s)) =
    ((tensorPullback i).obj M).val.map ((Opens.map i.base).op.map f)
      ((show Γ(Z, i ⁻¹ᵁ U.unop) from r) •
        (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ U.unop) from
          ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app M).val.app U s))
  exact (congrArg (fun m : Γ((tensorPullback i).obj M, i ⁻¹ᵁ V.unop) ↦
    (show Γ(Z, i ⁻¹ᵁ V.unop) from
      Z.presheaf.map ((Opens.map i.base).op.map f) r) • m) hn).trans
    (PresheafOfModules.map_smul ((tensorPullback i).obj M).val
      ((Opens.map i.base).op.map f) r _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Opposite TopologicalSpace Scheme.Modules in
private theorem exists_projectionComponent {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (M : Y.Modules) :
    ∃! α : M ⊗ (pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
        (pushforward i).obj ((tensorPullback i).obj M),
      ∀ (U : Y.Opens) (s : Γ(M, U))
        (r : Γ((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf), U)),
        α.app U (tmulSection s r) = projectionPairing i M U s r := by
  obtain ⟨α, hα, huniq⟩ := SheafOfModules.tensor_bilinear_universal Y.sheaf M
    ((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    ((pushforward i).obj ((tensorPullback i).obj M))
    (fun U ↦ projectionPairing i M U.unop) (projectionPairing_natural i M)
  refine ⟨α, ?_, ?_⟩
  · intro U s r
    exact hα (op U) s r
  · intro β hβ
    apply huniq
    intro U s r
    exact hβ U.unop s r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The closed-immersion ordinary projection formula, natural in the module
(Stacks, Tags 08KS, 01CB and 0098). -/
theorem nonempty_closedStructure_tensor_projection
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    Nonempty ((tensorRight B : SheafOfModules.{u} Y.ringCatSheaf ⥤
      SheafOfModules.{u} Y.ringCatSheaf) ≅
      Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.pushforward i) := by
  classical
  let _ := SheafOfModules.monoidalCategory Y.sheaf
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)
  let a (M : Y.Modules) := (exists_projectionComponent i M).choose
  have ha (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (r : Γ(B, U)) :
      (a M).app U (Scheme.Modules.tmulSection s r) = projectionPairing i M U s r :=
    (exists_projectionComponent i M).choose_spec.1 U s r
  let α : tensorRight B ⟶ Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.pushforward i :=
    { app := a
      naturality := by
        intro M N f
        have hpure : ∀ (U : Y.Opens) (s : Γ(M, U)) (r : Γ(B, U)),
            ((f ▷ B) ≫ a N).app U (Scheme.Modules.tmulSection s r) =
              (a M ≫ (Scheme.Modules.pushforward i).map
                ((Scheme.Modules.tensorPullback i).map f)).app U
                (Scheme.Modules.tmulSection s r) := by
          intro U s r
          rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
          change (a N).app U ((f ▷ B).app U (Scheme.Modules.tmulSection s r)) =
            ((Scheme.Modules.pushforward i).map ((Scheme.Modules.tensorPullback i).map f)).app U
              ((a M).app U (Scheme.Modules.tmulSection s r))
          rw [Scheme.Modules.whiskerRight_app_tmulSection, ha, ha]
          have hn := congrArg (fun g ↦ g.val.app (Opposite.op U) s)
            (adj.unit_naturality f)
          change (show Γ(Z, i ⁻¹ᵁ U) from r) •
              (show Γ((Scheme.Modules.tensorPullback i).obj N, i ⁻¹ᵁ U) from
                (adj.unit.app N).app U
                  (f.app U s)) =
            ((Scheme.Modules.tensorPullback i).map f).app (i ⁻¹ᵁ U)
              ((show Γ(Z, i ⁻¹ᵁ U) from r) •
                (show Γ((Scheme.Modules.tensorPullback i).obj M, i ⁻¹ᵁ U) from
                  (adj.unit.app M).app U s))
          exact (congrArg (fun m : Γ((Scheme.Modules.tensorPullback i).obj N, i ⁻¹ᵁ U) ↦
            (show Γ(Z, i ⁻¹ᵁ U) from r) • m) hn).symm.trans
              (Scheme.Modules.Hom.app_smul ((Scheme.Modules.tensorPullback i).map f)
                (U := i ⁻¹ᵁ U) r _).symm
        let e := SheafOfModules.tensorObjIsoSheafification M B
        apply (cancel_epi e.inv).mp
        apply ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).injective
        ext U z
        induction z using TensorProduct.inductionOn with
        | tmul s r => exact hpure U.unop s r
        | add z w hz hw => simp only [map_add, hz, hw] }
  have hi (M : Y.Modules) : IsIso (α.app M) := by
    let b := (SheafOfModules.toSheaf Y.ringCatSheaf).map (α.app M)
    have hs (x : Y) :
        IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map b.hom) :=
      closedStructure_projection_stalk_isIso i M (a M) (ha M) x
    let := hs
    have := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso b
    have : IsIso ((Scheme.Modules.toPresheaf Y).map (α.app M)) :=
      (TopCat.Sheaf.forget AddCommGrpCat Y.toTopCat).map_isIso b
    exact isIso_of_reflects_iso (α.app M) (Scheme.Modules.toPresheaf Y)
  let := hi
  exact ⟨NatIso.ofComponents (fun M ↦ asIso (α.app M)) (by
    intro M N f
    simpa [asIso] using α.naturality f)⟩

end AlgebraicGeometry
