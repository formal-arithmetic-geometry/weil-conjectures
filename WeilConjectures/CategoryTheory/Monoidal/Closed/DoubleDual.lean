/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The double-dual morphism in a braided monoidal closed category

For an object `W` of a braided monoidal closed category, this file records the formal
properties of the double-dual morphism `δ_X : X ⟶ [[X, W], W]`
(`CategoryTheory.MonoidalClosed.toIhomIhom`) used in the dévissage proofs of Verdier biduality
(blueprint `lem-weil-duality-pairing`, `lem-weil-delta-restriction`,
`lem-weil-delta-proper-pushforward`). They were split off from
`WeilConjectures.SixFunctors.Etale.Derived.DoubleDual`, which applies them to the étale
dualizing complex.

## Main statements

- `CategoryTheory.MonoidalClosed.ihomFlipSelfAdjunction`: `[-, W]` is adjoint to itself on the
  right, with unit `δ` (`CategoryTheory.MonoidalClosed.ihomFlipSelfAdjunction_unit_app`);
- `CategoryTheory.MonoidalClosed.isIso_toIhomIhom_tensor_iff`: `δ_{X ⊗ L}` is an isomorphism
  if and only if `δ_X` is, for `L` invertible;
- `CategoryTheory.MonoidalClosed.isIso_map_toIhomIhom_iff`: `δ` is compatible with lax braided
  functors whose dual comparisons are isomorphisms;
- `CategoryTheory.Pretriangulated.isIso_app_obj₂_of_distTriang`: a five lemma for a natural
  transformation `𝟭 ⟶ F` to an endofunctor that sends distinguished triangles to triangles
  distinguished for *some* third morphism;
- `CategoryTheory.ObjectProperty.isIso_toIhomIhom_fullSubcategory`: in a monoidal closed full
  subcategory (`CategoryTheory.ObjectProperty.fullMonoidalClosedSubcategory`), `δ` is an
  isomorphism as soon as it is one in the ambient category.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]

/-- Blueprint `lem-weil-duality-pairing` (auxiliary): whether the unit of an adjunction is an
isomorphism at an object only depends on the left adjoint up to isomorphism. -/
lemma isIso_unit_app_iff_of_iso {F₁ F₂ : C ⥤ D} {G₁ G₂ : D ⥤ C} (adj₁ : F₁ ⊣ G₁)
    (adj₂ : F₂ ⊣ G₂) (e : F₁ ≅ F₂) (X : C) :
    IsIso (adj₁.unit.app X) ↔ IsIso (adj₂.unit.app X) := by
  rw [← unit_rightAdjointUniq_hom_app (adj₁.ofNatIsoLeft e) adj₂ X]
  have h : (adj₁.ofNatIsoLeft e).unit.app X = adj₁.unit.app X ≫ G₁.map (e.hom.app X) := rfl
  rw [h]
  constructor
  · intro
    infer_instance
  · intro
    have : IsIso (adj₁.unit.app X ≫ G₁.map (e.hom.app X)) :=
      IsIso.of_isIso_comp_right _ ((rightAdjointUniq (adj₁.ofNatIsoLeft e) adj₂).hom.app _)
    exact IsIso.of_isIso_comp_right _ (G₁.map (e.hom.app X))

end Adjunction

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- Blueprint `lem-weil-duality-pairing`: the double-dual morphism as a unit. The contravariant
functor `[-, W]` is adjoint to itself on the right: maps `M ⟶ [X, W]`
correspond to maps `X ⊗ M ⟶ W`, hence through the braiding to maps `M ⊗ X ⟶ W`, hence to maps
`X ⟶ [M, W]`. Its unit is the double-dual map `CategoryTheory.MonoidalClosed.toIhomIhom`
(`CategoryTheory.MonoidalClosed.ihomFlipSelfAdjunction_unit_app`). -/
noncomputable def ihomFlipSelfAdjunction (W : C) :
    (internalHom.flip.obj W).rightOp ⊣ internalHom.flip.obj W :=
  Adjunction.mkOfHomEquiv
    { homEquiv X M :=
        { toFun f := curry ((β_ M.unop X).hom ≫ uncurry f.unop)
          invFun g := (curry ((β_ M.unop X).inv ≫ uncurry g)).op
          left_inv f := by simp
          right_inv g := by simp }
      homEquiv_naturality_left_symm := by
        intro X X' M f g
        apply Quiver.Hom.unop_inj
        apply uncurry_injective
        dsimp only [Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Functor.rightOp_map,
          Functor.flip_obj_map]
        simp only [internalHom_map, Quiver.Hom.unop_op, unop_comp]
        rw [uncurry_pre_app, uncurry_curry, uncurry_curry, uncurry_natural_left,
          BraidedCategory.braiding_inv_naturality_left_assoc]
      homEquiv_naturality_right := by
        intro X M M' f g
        apply uncurry_injective
        dsimp only [Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Functor.rightOp_map,
          Functor.flip_obj_map]
        simp only [internalHom_map, unop_comp]
        rw [uncurry_pre_app, uncurry_curry, uncurry_curry, uncurry_natural_left,
          BraidedCategory.braiding_naturality_left_assoc] }

/-- Blueprint `lem-weil-duality-pairing`: the unit of the self-adjunction of `[-, W]` is the
double-dual map `X ⟶ [[X, W], W]`. -/
lemma ihomFlipSelfAdjunction_unit_app (W X : C) :
    (ihomFlipSelfAdjunction W).unit.app X = toIhomIhom W X := by
  change curry ((β_ _ X).hom ≫ uncurry (𝟙 _)) = _
  rw [uncurry_id_eq_ev]
  rfl

/-- Blueprint `lem-weil-duality-pairing`, compatibility with shifts (formal core). Biduality
relative to `W` is invariant under twisting by an invertible object: for `L`
invertible, the double-dual map of `X ⊗ L` is an isomorphism if and only if that of `X` is.

The functor `- ⊗ L` is an autoequivalence of `C`, `[-, L]` one of `Cᵒᵖ`, and internal currying
`[X ⊗ L, W] ≅ [L, [X, W]]` intertwines them with `[-, W]`; the units of the two composite
adjunctions are then isomorphisms at the same objects. -/
theorem isIso_toIhomIhom_tensor_iff (W X : C) {L : C} (hL : IsInvertible L) :
    IsIso (toIhomIhom W (X ⊗ L)) ↔ IsIso (toIhomIhom W X) := by
  obtain ⟨L', ⟨e⟩, ⟨e'⟩⟩ := hL
  let E₁ : C ≌ C := Equivalence.mk (tensorRight L) (tensorRight L')
    ((rightUnitorNatIso C).symm ≪≫ (tensoringRight C).mapIso e.symm ≪≫ tensorRightTensor L L')
    ((tensorRightTensor L' L).symm ≪≫ (tensoringRight C).mapIso e' ≪≫ rightUnitorNatIso C)
  let E₀ : C ≌ C := Equivalence.mk (tensorLeft L) (tensorLeft L')
    ((leftUnitorNatIso C).symm ≪≫ (tensoringLeft C).mapIso e'.symm ≪≫ tensorLeftTensor L' L)
    ((tensorLeftTensor L L').symm ≪≫ (tensoringLeft C).mapIso e ≪≫ leftUnitorNatIso C)
  have : (tensorLeft L).IsEquivalence := E₀.isEquivalence_functor
  have : (ihom L).IsEquivalence := (ihom.adjunction L).isEquivalence_right_of_isEquivalence_left
  let E₂ : Cᵒᵖ ≌ Cᵒᵖ := (ihom L).asEquivalence.op
  let adj := ihomFlipSelfAdjunction W
  let iso : E₁.functor ⋙ (internalHom.flip.obj W).rightOp ≅
      (internalHom.flip.obj W).rightOp ⋙ E₂.functor :=
    NatIso.ofComponents (fun X ↦ (ihomCurryIso X L W).symm.op) (fun {X Y} f ↦ by
      apply Quiver.Hom.unop_inj
      dsimp
      simp only [Iso.op_inv, Quiver.Hom.unop_op, internalHom_map]
      rw [Iso.inv_comp_eq, <- Category.assoc, Iso.eq_comp_inv]
      exact pre_whiskerRight_app_comp_ihomCurryIso_hom f L W)
  have h := Adjunction.isIso_unit_app_iff_of_iso (E₁.toAdjunction.comp adj)
    (adj.comp E₂.toAdjunction) iso X
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  rwa [Equivalence.toAdjunction_unit, Equivalence.toAdjunction_unit, isIso_comp_left_iff,
    isIso_comp_right_iff, isIso_iff_of_reflects_iso _ E₁.inverse,
    ihomFlipSelfAdjunction_unit_app, ihomFlipSelfAdjunction_unit_app] at h

section Functor

variable {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D] [MonoidalClosed D]
  (G : C ⥤ D) [G.LaxBraided] {W : C} {W' : D} (e : G.obj W ⟶ W')

/-- Blueprints `lem-weil-delta-restriction` and `lem-weil-delta-proper-pushforward`: the
comparison `G [X, W] ⟶ [G X, G W] ⟶ [G X, W']` of duals along a lax monoidal functor
`G` and a map `e : G W ⟶ W'`. For the derived direct image along a proper morphism and the
trace `Rf_* ω_X ⟶ ω_Y` it is the Verdier exchange `Rf_* 𝔻_X ⟶ 𝔻_Y Rf_*`; for the restriction
to an open subscheme and `j^* ω_Y ≅ ω_W` it is `j^* 𝔻_Y ⟶ 𝔻_W j^*`. -/
noncomputable def dualComparison (X : C) : G.obj ((ihom X).obj W) ⟶ (ihom (G.obj X)).obj W' :=
  (Functor.LaxMonoidal.ihomComparison G X).natTrans.app W ≫ (ihom (G.obj X)).map e

/-- Blueprints `lem-weil-delta-restriction` and `lem-weil-delta-proper-pushforward` (formal
core): the double-dual map is compatible with lax braided functors: for `G` lax braided and
`e : G W ⟶ W'`, the square
```
       G X ─────────── G δ_X ──────────→ G [[X, W], W]
        │                                     │
   δ_{G X}                          dualComparison [X, W]
        ↓                                     ↓
  [[G X, W'], W'] ─[dualComparison X, W']─→ [G [X, W], W']
```
commutes. -/
@[reassoc]
lemma map_toIhomIhom_comp_dualComparison (X : C) :
    G.map (toIhomIhom W X) ≫ dualComparison G e ((ihom X).obj W) =
      toIhomIhom W' (G.obj X) ≫ (pre (dualComparison G e X)).app W' := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_left, dualComparison, dualComparison,
    uncurry_natural_right, uncurry_eq]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.ihomComparison_ev_assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
    ← G.map_comp_assoc, ← uncurry_eq, uncurry_toIhomIhom, G.map_comp_assoc,
    Functor.LaxBraided.braided_assoc, uncurry_toIhomIhom,
    BraidedCategory.braiding_naturality_left_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
    ihom.ev_naturality, Functor.LaxMonoidal.ihomComparison_ev_assoc]

/-- Blueprints `lem-weil-delta-restriction` and `lem-weil-delta-proper-pushforward`: if the
dual comparisons of `X` and of `[X, W]` along a lax braided functor `G` are isomorphisms, then
`G δ_X` is isomorphic, as an arrow, to the double-dual map of `G X` relative
to `W'`. -/
noncomputable def mapToIhomIhomArrowIso (X : C) [IsIso (dualComparison G e X)]
    [IsIso (dualComparison G e ((ihom X).obj W))] :
    Arrow.mk (G.map (toIhomIhom W X)) ≅ Arrow.mk (toIhomIhom W' (G.obj X)) :=
  haveI := isIso_pre_app (dualComparison G e X) W'
  Arrow.isoMk (Iso.refl _)
    (asIso (dualComparison G e ((ihom X).obj W)) ≪≫
      (asIso ((pre (dualComparison G e X)).app W')).symm)
    (by simp [map_toIhomIhom_comp_dualComparison_assoc])

/-- Blueprints `lem-weil-delta-restriction` and `lem-weil-delta-proper-pushforward`: if the
dual comparisons of `X` and of `[X, W]` along a lax braided functor `G` are isomorphisms, then
`G δ_X` is an isomorphism if and only if the double-dual map of `G X`
relative to `W'` is. -/
theorem isIso_map_toIhomIhom_iff (X : C) [IsIso (dualComparison G e X)]
    [IsIso (dualComparison G e ((ihom X).obj W))] :
    IsIso (G.map (toIhomIhom W X)) ↔ IsIso (toIhomIhom W' (G.obj X)) :=
  (MorphismProperty.isomorphisms D).arrow_mk_iso_iff (mapToIhomIhomArrowIso G e X)

end Functor

end MonoidalClosed

namespace Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Blueprint `lem-weil-duality-pairing` (formal core): a five lemma for a natural
transformation `δ : 𝟭 ⟶ F` to an endofunctor `F` which sends distinguished triangles to
triangles that are distinguished for *some* third morphism. If `δ` is an isomorphism at `T.obj₁`,
`T.obj₃`, `T.obj₁⟦1⟧` and `T.obj₃⟦-1⟧` for a distinguished triangle `T`, then it is an
isomorphism at `T.obj₂`.

No compatibility of `δ` with the third morphisms is needed: the argument only uses the
exactness of `Hom(Y, F -)` at the middle terms of the images of `T` and of its rotations, the
connecting maps being `F` applied to those of `T`. -/
theorem isIso_app_obj₂_of_distTriang (F : C ⥤ C) (δ : 𝟭 C ⟶ F)
    (hF : ∀ T ∈ distTriang C, ∃ w, Triangle.mk (F.map T.mor₁) (F.map T.mor₂) w ∈ distTriang C)
    (T : Triangle C) (hT : T ∈ distTriang C) [IsIso (δ.app T.obj₁)] [IsIso (δ.app T.obj₃)]
    [IsIso (δ.app (T.obj₁⟦(1 : ℤ)⟧))] [IsIso (δ.app (T.obj₃⟦(-1 : ℤ)⟧))] :
    IsIso (δ.app T.obj₂) := by
  have nat : ∀ {X Y : C} (f : X ⟶ Y), f ≫ δ.app Y = δ.app X ≫ F.map f := fun f ↦ δ.naturality f
  have inj : ∀ {Y : C} (g : Y ⟶ T.obj₂), g ≫ δ.app T.obj₂ = 0 → g = 0 := by
    intro Y g hg
    have h₁ : g ≫ T.mor₂ = 0 := by
      rw [← cancel_mono (δ.app T.obj₃), Category.assoc, nat T.mor₂, reassoc_of% hg, zero_comp,
        zero_comp]
    obtain ⟨g₁, rfl⟩ := Triangle.coyoneda_exact₂ T hT g h₁
    obtain ⟨w, hw⟩ := hF _ (inv_rot_of_distTriang T hT)
    have h₂ : (g₁ ≫ δ.app T.obj₁) ≫ F.map T.invRotate.mor₂ = 0 := by
      change (g₁ ≫ δ.app T.obj₁) ≫ F.map T.mor₁ = 0
      rw [Category.assoc, ← nat T.mor₁, ← Category.assoc, hg]
    obtain ⟨h₀, hh₀⟩ := Triangle.coyoneda_exact₂ _ hw (g₁ ≫ δ.app T.obj₁) h₂
    replace hh₀ : g₁ ≫ δ.app T.obj₁ = h₀ ≫ F.map T.invRotate.mor₁ := hh₀
    have : IsIso (δ.app T.invRotate.obj₁) := ‹IsIso (δ.app (T.obj₃⟦(-1 : ℤ)⟧))›
    have : g₁ = (h₀ ≫ inv (δ.app T.invRotate.obj₁)) ≫ T.invRotate.mor₁ := by
      rw [← cancel_mono (δ.app T.obj₁), hh₀, Category.assoc, Category.assoc]
      erw [nat T.invRotate.mor₁]
      rw [IsIso.inv_hom_id_assoc]
    rw [this, Category.assoc, Category.assoc]
    erw [comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang T hT)]
    rw [comp_zero, comp_zero]
  have surj : ∀ {Y : C} (f : Y ⟶ F.obj T.obj₂), ∃ g, g ≫ δ.app T.obj₂ = f := by
    intro Y f
    obtain ⟨w, hw⟩ := hF _ (rot_of_distTriang T hT)
    obtain ⟨w', hw'⟩ := hF T hT
    have hc : (f ≫ F.map T.mor₂ ≫ inv (δ.app T.obj₃)) ≫ T.mor₃ = 0 := by
      rw [← cancel_mono (δ.app (T.obj₁⟦(1 : ℤ)⟧)), zero_comp, Category.assoc, Category.assoc,
        Category.assoc, nat T.mor₃, IsIso.inv_hom_id_assoc]
      erw [comp_distTriang_mor_zero₁₂ _ hw]
      rw [comp_zero]
    obtain ⟨d, hd⟩ := Triangle.coyoneda_exact₃ T hT _ hc
    have h₃ : (f - d ≫ δ.app T.obj₂) ≫ F.map T.mor₂ = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, ← nat T.mor₂, ← Category.assoc, ← hd]
      simp
    obtain ⟨e, he⟩ := Triangle.coyoneda_exact₂ _ hw' _ h₃
    replace he : f - d ≫ δ.app T.obj₂ = e ≫ F.map T.mor₁ := he
    refine ⟨d + e ≫ inv (δ.app T.obj₁) ≫ T.mor₁, ?_⟩
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, nat T.mor₁,
      IsIso.inv_hom_id_assoc, ← he]
    abel
  have : Mono (δ.app T.obj₂) := Preadditive.mono_of_cancel_zero _ fun g hg ↦ inj g hg
  obtain ⟨s, hs⟩ := surj (𝟙 _)
  have : IsSplitEpi (δ.app T.obj₂) := IsSplitEpi.mk' ⟨s, hs⟩
  exact isIso_of_mono_of_isSplitEpi _

end Pretriangulated

end CategoryTheory

namespace CategoryTheory.ObjectProperty

open MonoidalClosed

/-- The double-dual morphism of a monoidal closed full subcategory is an isomorphism when the
double-dual morphism of the underlying objects is one: the inclusion is fully faithful and
carries the internal Hom of the subcategory to that of the ambient category. -/
theorem isIso_toIhomIhom_fullSubcategory {C : Type*} [Category* C] [MonoidalCategory C]
    [MonoidalClosed C] [BraidedCategory C] (P : ObjectProperty C) [P.IsMonoidal]
    [P.IsMonoidalClosed] (W K : P.FullSubcategory)
    (h : IsIso (toIhomIhom W.obj K.obj)) : IsIso (toIhomIhom W K) := by
  have : IsIso (P.ι.map (toIhomIhom W K)) := h
  exact isIso_of_reflects_iso (toIhomIhom W K) P.ι

end CategoryTheory.ObjectProperty
