/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# Sections of a kernel of `𝒪_X`-modules, and the pullback of the structure sheaf

Limits in `X.Modules` are computed section-wise, because evaluation at an open subset
preserves finite limits (`SheafOfModules.Finite.evaluationPreservesFiniteLimits`). This file
records the resulting concrete description of the sections of a categorical kernel: over any
open `U`, the sections of `kernel f` are exactly the sections of the source that `f` kills.

This is the tool that turns a sheaf of modules defined as a kernel — as the ideal sheaf of a
`Scheme.IdealSheafData` is in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` —
into a computable object.

The file also records that the pullback of the structure sheaf along any morphism of schemes
is the structure sheaf, and the presheaf of `Γ(X, ⊤)`-modules underlying a sheaf of modules.

## Main results

- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`
- `AlgebraicGeometry.Scheme.Modules.pullbackObjUnitIso`: `f^* 𝒪_Y ≅ 𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.pullbackIsoPushforwardInv`: `e^* ≅ (e⁻¹)_*` for an
  isomorphism `e`.
- `AlgebraicGeometry.Scheme.Modules.exists_mem_over_iso_unit`: an invertible module is locally
  trivial.
- `AlgebraicGeometry.Scheme.Modules.isZero_of_forall_affineOpens`: a module whose sections over
  every affine open vanish is zero.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.unit`: the structure sheaf as an object of `X.Modules`.
- `AlgebraicGeometry.Scheme.Modules.presheafModuleCat`: the presheaf of `Γ(X, ⊤)`-modules
  underlying a sheaf of modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)
  {M N : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N)

/-- **The sections of a kernel are the kernel of the sections.** Over any open `U`, the image
of `kernel.ι f` on sections is the set of sections of `M` killed by `f`.

This is stated for `SheafOfModules X.ringCatSheaf` rather than for the definitionally equal
`X.Modules`, because instance search for `PreservesLimit` does not see through the latter. -/
lemma range_map_kernelι :
    Set.range ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) =
      { x | (SheafOfModules.evaluation X.ringCatSheaf (op U)).map f x = 0 } := by
  set G := SheafOfModules.evaluation X.ringCatSheaf (op U) with hG
  have key : ((PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv ≫
      G.map (kernel.ι f)) = ModuleCat.ofHom (LinearMap.ker (G.map f).hom).subtype := by
    simp [ModuleCat.kernelIsoKer_inv_kernel_ι]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change G.map f (G.map (kernel.ι f) y) = 0
    rw [← ConcreteCategory.comp_apply, ← G.map_comp, kernel.condition, G.map_zero]
    rfl
  · intro hx
    refine ⟨(PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv ⟨x, hx⟩, ?_⟩
    have h2 := ConcreteCategory.congr_hom key ⟨x, hx⟩
    simp only [Iso.trans_inv, ConcreteCategory.comp_apply] at h2
    exact h2

lemma map_kernelι_eq :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f) =
      (PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) f).hom ≫
        kernel.ι _ := by
  rw [← PreservesKernel.iso_inv_ι]
  simp

instance : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) := by
  rw [map_kernelι_eq]
  infer_instance

/-- `kernel.ι f` is injective on sections over any open, not merely a monomorphism. -/
lemma injective_map_kernelι :
    Function.Injective ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The pullback of the structure sheaf along a morphism of schemes is the structure sheaf. -/
noncomputable def pullbackObjUnitIso {Y : Scheme.{u}} (g : X ⟶ Y) :
    (Modules.pullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  -- The `IsIso` instance has to be introduced by hand: elaborating `asIso` directly leaves the
  -- universe metavariables of `pullbackObjUnitToUnit` undetermined when the instance is sought.
  haveI : IsIso (C := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance
  asIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)

/-- Pulling back sheaves of modules along an isomorphism of schemes `e` is pushing forward along
its inverse: both are left adjoint to the pushforward along `e`, which is an equivalence with
inverse the pushforward along `inv e`. -/
noncomputable def pullbackIsoPushforwardInv {Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    Modules.pullback e ≅ pushforward (inv e) :=
  let E : Y.Modules ≌ X.Modules :=
    CategoryTheory.Equivalence.mk (pushforward (inv e)) (pushforward e)
      ((pushforwardId Y).symm ≪≫ pushforwardCongr (by simp) ≪≫ (pushforwardComp _ _).symm)
      (pushforwardComp _ _ ≪≫ pushforwardCongr (by simp) ≪≫ pushforwardId X)
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction e) E.toAdjunction

end Modules

/-- The structure sheaf `𝒪_X` of a scheme `X`, as an object of `X.Modules`. -/
noncomputable abbrev Modules.unit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

namespace Modules

variable {X : Scheme.{u}}

/-- The presheaf of `Γ(X, ⊤)`-modules underlying a sheaf of modules `ℱ`: its value on an open
`U` is `Γ(U, ℱ)`, a `Γ(X, ⊤)`-module by restriction of scalars along `Γ(X, ⊤) ⟶ Γ(X, U)`.
It is the image of `ℱ` under `PresheafOfModules.forgetToPresheafModuleCat`. -/
noncomputable def presheafModuleCat (ℱ : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj ℱ.val

@[simp]
lemma presheafModuleCat_obj (ℱ : X.Modules) (V : X.Opensᵒᵖ) :
    ℱ.presheafModuleCat.obj V = (ModuleCat.restrictScalars
      (X.ringCatSheaf.obj.map (homOfLE le_top : V.unop ⟶ ⊤).op).hom).obj (ℱ.val.obj V) :=
  rfl

-- Not a `simp` lemma, for the same reason as
-- `PresheafOfModules.forgetToPresheafModuleCatObjObj_coe`.
lemma presheafModuleCat_obj_coe (ℱ : X.Modules) (V : X.Opensᵒᵖ) :
    (ℱ.presheafModuleCat.obj V : Type u) = ℱ.val.obj V :=
  rfl

/-- An invertible `𝒪_X`-module is trivial on a neighbourhood of every point: every `x : X` lies
in an open `Y` over which `M` is isomorphic to the unit sheaf of modules. -/
lemma exists_mem_over_iso_unit (M : X.Modules) [M.IsInvertible] (x : X) :
    ∃ (Y : X.Opens), x ∈ Y ∧
      Nonempty (M.over Y ≅ SheafOfModules.unit (X.ringCatSheaf.over Y)) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsInvertible.exists_isInvertibleData (M := M)
  obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hx⟩ := q.coversTop ⊤ x trivial
  have := (hq.nonempty_unique i).some
  exact ⟨q.X i, g.le hx, ⟨(asIso (q.generators i).π).symm ≪≫ SheafOfModules.freeUniqueIso _⟩⟩

/-- A trivialisation `M.over Y ≅ 𝒪_Y` of an `𝒪_X`-module over an open `Y` gives, for every open
`W ≤ Y`, a `Γ(X, W)`-linear isomorphism between the sections `Γ(M, W)` and `Γ(X, W)`. -/
noncomputable def sectionsLinearEquivOfOverIsoUnit {M : X.Modules} {Y : X.Opens}
    (e : M.over Y ≅ SheafOfModules.unit (X.ringCatSheaf.over Y)) {W : X.Opens} (h : W ≤ Y) :
    Γ(M, W) ≃ₗ[Γ(X, W)] Γ(X, W) where
  toFun := (e.hom.val.app (op (Over.mk (homOfLE h)))).hom
  invFun := (e.inv.val.app (op (Over.mk (homOfLE h)))).hom
  map_add' := map_add _
  map_smul' := (e.hom.val.app (op (Over.mk (homOfLE h)))).hom.map_smul
  left_inv x := by
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
      e.hom_inv_id]
    rfl
  right_inv x := by
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
      e.inv_hom_id]
    rfl

/-- **A sheaf of modules vanishing on affine opens is zero.** If `Γ(M, V) = 0` for every affine
open `V`, then `M = 0`: the affine opens form a basis, so every section is locally zero. -/
lemma isZero_of_forall_affineOpens (M : X.Modules)
    (h : ∀ V : X.affineOpens, Subsingleton Γ(M, V.1)) : IsZero M := by
  refine (IsZero.iff_id_eq_zero M).2 (hom_ext _ _ fun U ↦ ?_)
  ext x
  change x = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ U} ↦ i.1.1) U (fun i ↦ homOfLE i.2) ?_ x 0
    fun i ↦ @Subsingleton.elim _ (h i.1) _ _
  intro y hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩

/-- Every sheaf of modules on an empty scheme is zero. -/
lemma isZero_of_isEmpty [IsEmpty X] (M : X.Modules) : IsZero M := by
  refine (IsZero.iff_id_eq_zero M).2 (hom_ext _ _ fun U ↦ ?_)
  ext x
  change x = 0
  exact TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun i : Empty ↦ i.elim) U
    (fun i ↦ i.elim) (fun y _ ↦ isEmptyElim y) x 0 (fun i ↦ i.elim)

end AlgebraicGeometry.Scheme.Modules
