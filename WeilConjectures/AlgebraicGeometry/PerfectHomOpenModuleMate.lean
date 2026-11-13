/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The ordinary direct-image mate in the cartesian open square

## References

* Stacks Project, Cohomology, Tag 08FE.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

/-- The cartesian open inclusion. -/
abbrev perfectHomOpenMap {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S) :=
  pullback.map (B.ι ≫ s) r s r B.ι (𝟙 T) (𝟙 S) (by simp) (by simp)

/-- The square of open inclusions is cartesian. -/
theorem perfectHomOpenSquare {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens)
    (r : T ⟶ S) :
    IsPullback (pullback.fst (B.ι ≫ s) r) (perfectHomOpenMap s B r) B.ι
      (pullback.fst s r) := by
  have H : IsPullback (pullback.fst (B.ι ≫ s) r)
      (perfectHomOpenMap s B r ≫ pullback.snd s r) (B.ι ≫ s) r := by
    simpa [perfectHomOpenMap, pullback.map] using
      (IsPullback.of_hasPullback (B.ι ≫ s) r)
  apply H.of_bot (v₂₁ := pullback.snd s r) (v₂₂ := s) ?_
    (IsPullback.of_hasPullback s r)
  simp [perfectHomOpenMap, pullback.map]

/-- Base change preserves open immersions. -/
instance perfectHomOpenMap_isOpenImmersion {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S) :
    IsOpenImmersion (perfectHomOpenMap s B r) :=
  MorphismProperty.of_isPullback (perfectHomOpenSquare s B r) inferInstance

/-- The ordinary composition comparison, with its sectionwise normalization. -/
def perfectHomOpenModuleComposition {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S) :
    Scheme.Modules.pushforward (perfectHomOpenMap s B r) ⋙
        Scheme.Modules.pushforward (pullback.fst s r) ≅
      Scheme.Modules.pushforward (pullback.fst (B.ι ≫ s) r) ⋙
        Scheme.Modules.pushforward B.ι :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (perfectHomOpenSquare s B r).w.symm ≪≫
    (Scheme.Modules.pushforwardComp _ _).symm

/-- Transpose the ordinary composition comparison under the two open adjunctions. -/
def perfectHomOpenModuleMate {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S) :
    Scheme.Modules.pushforward (pullback.fst s r) ⋙ schemeOpenRestriction Y B ⟶
      Scheme.Modules.restrictFunctor (perfectHomOpenMap s B r) ⋙
        Scheme.Modules.pushforward (pullback.fst (B.ι ≫ s) r) :=
  ((mateEquiv (Scheme.Modules.restrictAdjunction (perfectHomOpenMap s B r))
    (schemeOpenModuleAdjunction Y B)).symm
      (TwoSquare.mk _ _ _ _ (perfectHomOpenModuleComposition s B r).hom))

private theorem isIso_open_module_mate_of_isPullback
    {X X' Y : Scheme.{u}} (B : Y.Opens) (p : X ⟶ Y) (p' : X' ⟶ B.toScheme)
    (i : X' ⟶ X) [IsOpenImmersion i] (h : IsPullback p' i B.ι p) :
    let c := Scheme.Modules.pushforwardComp i p ≪≫
      Scheme.Modules.pushforwardCongr h.w.symm ≪≫
      (Scheme.Modules.pushforwardComp p' B.ι).symm
    IsIso ((mateEquiv (Scheme.Modules.restrictAdjunction i)
      (schemeOpenModuleAdjunction Y B)).symm (TwoSquare.mk _ _ _ _ c.hom)) := by
  let c := Scheme.Modules.pushforwardComp i p ≪≫
    Scheme.Modules.pushforwardCongr h.w.symm ≪≫
    (Scheme.Modules.pushforwardComp p' B.ι).symm
  let α := (mateEquiv (Scheme.Modules.restrictAdjunction i)
    (schemeOpenModuleAdjunction Y B)).symm (TwoSquare.mk _ _ _ _ c.hom)
  change IsIso α
  have (M : X.Modules) : IsIso (α.app M) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro W
    have hW := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h W
    have hh : Scheme.Modules.Hom.app (α.app M) W =
        M.val.presheaf.map (eqToHom hW).op := by
      -- Name the restriction arrows before unfolding the mate on sections.
      let V := B.ι ''ᵁ W
      let U := p ⁻¹ᵁ V
      have hc : p' ⁻¹ᵁ (B.ι ⁻¹ᵁ V) = i ⁻¹ᵁ U :=
        congrArg (fun k : X' ⟶ Y ↦ k ⁻¹ᵁ V) h.w
      let a := (homOfLE (i.image_preimage_le U)).op
      let b := (i.opensFunctor.map (eqToHom hc)).op
      let d := (i.opensFunctor.map ((TopologicalSpace.Opens.map p'.base).map
        (eqToHom (B.ι.preimage_image_eq W).symm))).op
      have hm : M.val.presheaf.map a ≫ M.val.presheaf.map b ≫ M.val.presheaf.map d =
          M.val.presheaf.map (eqToHom hW).op := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
      ext x
      change M.val.presheaf.map d
        (M.val.presheaf.map b (M.val.presheaf.map a x)) = _
      exact ConcreteCategory.congr_hom hm x
    rw [hh]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The ordinary open-square mate is the sectionwise direct-image/restriction identity
(Stacks, Tag 08FE). -/
theorem perfectHomOpenModuleMate_isIso {S Y T : Scheme.{u}}
    (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S) :
    IsIso (perfectHomOpenModuleMate s B r) := by
  exact isIso_open_module_mate_of_isPullback B (pullback.fst s r)
    (pullback.fst (B.ι ≫ s) r) (perfectHomOpenMap s B r) (perfectHomOpenSquare s B r)

end
end AlgebraicGeometry
