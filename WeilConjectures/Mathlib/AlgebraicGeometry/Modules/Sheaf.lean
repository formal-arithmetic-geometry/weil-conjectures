/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

/-- Conjugating the pullback of an endomorphism `f` of `𝒪_X` by `h^* 𝒪_X ≅ 𝒪_Y` gives the
endomorphism of `𝒪_Y` whose value at `1` is `h^♯ (f 1)`. -/
lemma pullbackObjUnitIso_conj_app_top {Y : Scheme.{u}} (h : Y ⟶ X)
    (f : Modules.unit X ⟶ Modules.unit X) :
    ((pullbackObjUnitIso h).inv ≫ (pullback h).map f ≫ (pullbackObjUnitIso h).hom).app ⊤
      (1 : Γ(Y, ⊤)) = h.appTop (f.app ⊤ (1 : Γ(X, ⊤))) := by
  set F := (pullbackObjUnitIso h).inv ≫ (pullback h).map f ≫ (pullbackObjUnitIso h).hom
  have hF : (pullback h).map f ≫ (pullbackObjUnitIso h).hom =
      (pullbackObjUnitIso h).hom ≫ F := by
    simp [F]
  have key := congrArg ((pullbackPushforwardAdjunction h).homEquiv _ _) hF
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at key
  have h2 : (pullbackPushforwardAdjunction h).homEquiv _ _ (pullbackObjUnitIso h).hom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [h2] at key
  have := congrArg (fun (φ : Modules.unit X ⟶ (pushforward h).obj (Modules.unit Y)) ↦
    (Hom.app φ ⊤) (1 : Γ(X, ⊤))) key
  dsimp only at this
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at this
  have e1 : (Hom.app (SheafOfModules.unitToPushforwardObjUnit (Hom.toRingCatSheafHom h)) ⊤)
      (1 : Γ(X, ⊤)) = (1 : Γ(Y, ⊤)) :=
    map_one h.appTop.hom
  exact (this.trans (congrArg (Hom.app F (h ⁻¹ᵁ ⊤)) e1)).symm

section Free

open SheafOfModules Matrix

variable {Y : Scheme.{u}}

/-- The `j`-th coordinate projection `𝒪_X^{(J)} ⟶ 𝒪_X` of a free module. -/
noncomputable def freeπ {J : Type u} [DecidableEq J] (j : J) :
    free (R := X.ringCatSheaf) J ⟶ Modules.unit X :=
  Sigma.desc fun i ↦ if i = j then 𝟙 _ else 0

@[reassoc (attr := simp)]
lemma ιFree_freeπ {J : Type u} [DecidableEq J] (i j : J) :
    ιFree i ≫ (freeπ j : free (R := X.ringCatSheaf) J ⟶ _) = if i = j then 𝟙 _ else 0 :=
  Sigma.ι_desc _ _

lemma free_hom_ext {I : Type u} {M : X.Modules} {f g : free (R := X.ringCatSheaf) I ⟶ M}
    (h : ∀ i, ιFree i ≫ f = ιFree i ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _ h

lemma sum_freeπ_ιFree {J : Type u} [Fintype J] [DecidableEq J] :
    ∑ j : J, freeπ j ≫ ιFree j = 𝟙 (free (R := X.ringCatSheaf) J) :=
  free_hom_ext fun i ↦ by
    rw [Preadditive.comp_sum, Finset.sum_eq_single i (fun j _ hj ↦ by simp [Ne.symm hj])
      (by simp)]
    simp

/-- The matrix `(φ_{ji})` of a morphism `φ : 𝒪_X^{(I)} ⟶ 𝒪_X^{(J)}` of free modules: `φ_{ji}` is
the global function by which the component `𝒪_X ⟶ 𝒪_X` of `φ` from `i` to `j` multiplies. -/
noncomputable def freeMatrix {I J : Type u} [DecidableEq J]
    (φ : free (R := X.ringCatSheaf) I ⟶ free J) : Matrix J I Γ(X, ⊤) :=
  Matrix.of fun j i ↦ Hom.app (ιFree i ≫ φ ≫ freeπ j) ⊤ (1 : Γ(X, ⊤))

/-- The pullback of a free module is free. -/
noncomputable def pullbackFreeIso (g : Y ⟶ X) (I : Type u) :
    (pullback g).obj (free (R := X.ringCatSheaf) I) ≅ free I :=
  SheafOfModules.pullbackObjFreeIso g.toRingCatSheafHom I

@[reassoc (attr := simp)]
lemma pullback_map_ιFree_pullbackFreeIso_hom (g : Y ⟶ X) {I : Type u} (i : I) :
    (pullback g).map (ιFree i) ≫ (pullbackFreeIso g I).hom =
      (pullbackObjUnitIso g).hom ≫ ιFree i :=
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ i

lemma ιFree_pullbackFreeIso_inv (g : Y ⟶ X) {I : Type u} (i : I) :
    ιFree i ≫ (pullbackFreeIso g I).inv =
      (pullbackObjUnitIso g).inv ≫ (pullback g).map (ιFree i) := by
  rw [Iso.comp_inv_eq, Category.assoc, pullback_map_ιFree_pullbackFreeIso_hom,
    Iso.inv_hom_id_assoc]

@[reassoc]
lemma pullbackFreeIso_hom_freeπ (g : Y ⟶ X) {I : Type u} [DecidableEq I] (i : I) :
    (pullbackFreeIso g I).hom ≫ freeπ i =
      (pullback g).map (freeπ i) ≫ (pullbackObjUnitIso g).hom := by
  rw [← cancel_epi (pullbackFreeIso g I).inv, Iso.inv_hom_id_assoc]
  refine free_hom_ext fun k ↦ ?_
  rw [ιFree_freeπ, reassoc_of% (ιFree_pullbackFreeIso_inv g k), ← Functor.map_comp_assoc,
    ιFree_freeπ]
  split_ifs
  · rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  · have hz : (pullback g).map (0 : Modules.unit X ⟶ Modules.unit X) = 0 :=
      (pullback g).map_zero _ _
    rw [hz, zero_comp, comp_zero]

/-- The matrix of the pullback `g^* φ` of a morphism `φ` of free modules is the image of the matrix
of `φ` under `g^♯ : Γ(X, ⊤) → Γ(Y, ⊤)`. -/
lemma freeMatrix_pullback (g : Y ⟶ X) {I J : Type u} [DecidableEq J]
    (φ : free (R := X.ringCatSheaf) I ⟶ free J) :
    freeMatrix ((pullbackFreeIso g I).inv ≫ (pullback g).map φ ≫ (pullbackFreeIso g J).hom) =
      (freeMatrix φ).map g.appTop := by
  ext j i
  simp only [freeMatrix, Matrix.of_apply, Matrix.map_apply, Category.assoc,
    pullbackFreeIso_hom_freeπ, reassoc_of% (ιFree_pullbackFreeIso_inv g i)]
  simp only [← Functor.map_comp_assoc]
  exact pullbackObjUnitIso_conj_app_top g _

lemma Hom.sum_app_apply {M N : X.Modules} {ι : Type*} (s : Finset ι) (φ : ι → (M ⟶ N))
    (U : X.Opens) (x : Γ(M, U)) : (∑ i ∈ s, φ i).app U x = ∑ i ∈ s, (φ i).app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma freeπ_app_ιFree_app {I : Type u} [DecidableEq I] (i j : I) (a : Γ(X, ⊤)) :
    Hom.app (freeπ j) ⊤ (Hom.app (ιFree (R := X.ringCatSheaf) (I := I) i) ⊤ a) =
      if i = j then a else 0 := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, ιFree_freeπ]
  split_ifs <;> rfl

/-- The `Γ(X, ⊤)`-linear coordinates `Γ(X, 𝒪_X^{(I)}) ≃ Γ(X, ⊤)^I` of the global sections of a
free module of finite rank. -/
noncomputable def freeSectionsEquiv (I : Type u) [Fintype I] [DecidableEq I] :
    Γ(free (R := X.ringCatSheaf) I, ⊤) ≃ₗ[Γ(X, ⊤)] (I → Γ(X, ⊤)) where
  toFun x i := Hom.app (freeπ i) ⊤ x
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp
  invFun c := ∑ i, Hom.app (ιFree (R := X.ringCatSheaf) i) ⊤ (c i)
  left_inv x := by
    dsimp only
    simp_rw [← ConcreteCategory.comp_apply, ← Hom.comp_app]
    rw [← Hom.sum_app_apply, sum_freeπ_ιFree]
    rfl
  right_inv c := by
    ext j
    dsimp only
    rw [map_sum, Finset.sum_eq_single j (fun i _ hi ↦ ?_) (by simp)]
    · rw [freeπ_app_ιFree_app, if_pos rfl]
    · rw [freeπ_app_ιFree_app, if_neg hi]

/-- The application `Γ(M, U) → Γ(N, U)` of a morphism of `𝒪_X`-modules, as a `Γ(X, U)`-linear
map. -/
noncomputable def Hom.appₗ {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := Hom.app_smul φ

@[simp]
lemma Hom.appₗ_apply {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    Hom.appₗ φ U x = φ.app U x :=
  rfl

/-- The `Γ(X, U)`-linear isomorphism `Γ(M, U) ≃ Γ(N, U)` induced by an isomorphism `M ≅ N` of
`𝒪_X`-modules. -/
noncomputable def appLinearEquivOfIso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) where
  __ := Hom.appₗ e.hom U
  invFun := e.inv.app U
  left_inv x := by
    change Hom.app (e.hom ≫ e.inv) U x = x
    rw [e.hom_inv_id]
    rfl
  right_inv x := by
    change Hom.app (e.inv ≫ e.hom) U x = x
    rw [e.inv_hom_id]
    rfl

/-- An endomorphism of `𝒪_X` multiplies global sections by its value at `1`. -/
lemma unit_hom_app_top (e : Modules.unit X ⟶ Modules.unit X) (c : Γ(X, ⊤)) :
    Hom.app e ⊤ c = c • Hom.app e ⊤ (1 : Γ(X, ⊤)) := by
  rw [← Hom.app_smul]
  congr 1
  exact (mul_one c).symm

/-- In the coordinates `freeSectionsEquiv`, a morphism of free modules acts on global sections as
multiplication by its matrix. -/
lemma freeSectionsEquiv_app {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (φ : free (R := X.ringCatSheaf) I ⟶ free J) (x : Γ(free I, ⊤)) :
    freeSectionsEquiv J (Hom.app φ ⊤ x) = freeMatrix φ *ᵥ freeSectionsEquiv I x := by
  obtain ⟨c, rfl⟩ := (freeSectionsEquiv (X := X) I).symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  ext j
  change Hom.app (freeπ j) ⊤ (Hom.app φ ⊤
    (∑ i, Hom.app (ιFree (R := X.ringCatSheaf) i) ⊤ (c i))) = _
  rw [map_sum, map_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Hom.comp_app,
    ← Hom.comp_app]
  exact (unit_hom_app_top _ _).trans (mul_comm (c i) _)

/-- The rank of the matrix of a morphism of free modules of finite rank is the dimension of the
image of the global sections. -/
lemma rank_freeMatrix {I J : Type u} [Fintype I] [Finite J] [DecidableEq J]
    (φ : free (R := X.ringCatSheaf) I ⟶ free J) :
    (freeMatrix φ).rank = Module.finrank Γ(X, ⊤) (LinearMap.range (Hom.appₗ φ ⊤)) := by
  classical
  have := Fintype.ofFinite J
  have h : (freeMatrix φ).mulVecLin = (freeSectionsEquiv J).toLinearMap ∘ₗ Hom.appₗ φ ⊤ ∘ₗ
      (freeSectionsEquiv I).symm.toLinearMap := by
    refine LinearMap.ext fun c ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Hom.appₗ_apply,
      freeSectionsEquiv_app, LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply]
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]

end Free

end AlgebraicGeometry.Scheme.Modules
