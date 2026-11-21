/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The double-dual morphism: shifts, triangles, restriction and push-forward

Let `a : X ⟶ S` admit a compactification, `ω_X = Ra^! Λ_S` and `𝔻_X = RHom(-, ω_X)`. This file
records the formal properties of the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`
(`AlgebraicGeometry.Etale.verdierDualDoubleDual`) used in the dévissage proof of Verdier
biduality.

## Main statements

- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_shift_iff`: `δ_{K⟦n⟧}` is an
  isomorphism if and only if `δ_K` is;
- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_obj₂`: for a distinguished triangle
  `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁⟦1⟧`, if `δ_{K₁}` and `δ_{K₃}` are isomorphisms, so is `δ_{K₂}`;
- `AlgebraicGeometry.Etale.verdierBidualityLocus_isTriangulated`: the complexes `K` with `δ_K`
  an isomorphism form a triangulated subcategory of `D(X_ét)`.
- `CategoryTheory.MonoidalClosed.map_toIhomIhom_comp_dualComparison`: for a lax braided functor
  `G` and `e : G W ⟶ W'`, the comparison `G [X, W] ⟶ [G X, W']` carries `G δ_X` to `δ_{G X}`;
- `CategoryTheory.MonoidalClosed.mapToIhomIhomArrowIso`: hence, when the comparisons are
  isomorphisms, `G δ_X` and `δ_{G X}` are isomorphic arrows;
- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_surjective`: biduality descends
  along a surjective étale morphism once `Lj^* δ_K` is identified with `δ_{Lj^* K}`.

## Implementation details

The exactness of `RHom(-, ω_X)` (`AlgebraicGeometry.Etale.exists_distTriang_derivedHom_left`)
only provides *some* third morphism for the image of a distinguished triangle, so `δ` is not
directly a morphism of triangles. The triangulated five lemma is therefore proved in the form
`CategoryTheory.Pretriangulated.isIso_app_obj₂_of_distTriang`, which only uses the exactness of
`Hom(Y, 𝔻𝔻 -)` at the middle terms of the images of a triangle and of its rotations. It needs
`δ` to be invertible at `K₁⟦1⟧` and `K₃⟦-1⟧`, supplied by the shift compatibility.

The shift compatibility uses `K⟦n⟧ ≅ K ⊗ᴸ Λ_X⟦n⟧` with `Λ_X⟦n⟧` invertible, and the fact that
`[-, W]` is self-adjoint on the right with unit `δ`
(`CategoryTheory.MonoidalClosed.ihomFlipSelfAdjunction`). No sign bookkeeping is needed, since
the unit of an adjunction is invertible at an object independently of the chosen adjunction
(`CategoryTheory.Adjunction.isIso_unit_app_iff_of_iso`).

## TODO

To deduce the Verdier exchange formulas for the restriction to an open subscheme and for the
direct image along a proper morphism from `CategoryTheory.MonoidalClosed.mapToIhomIhomArrowIso`,
two inputs are missing:

- the derived pullback `Lg^*`, with its monoidal structure
  `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`, is not known to be braided for the
  derived braiding `AlgebraicGeometry.Etale.derivedBraidedCategory`, and no lax
  braided monoidal structure on `Rf_*` is available;
- the comparison maps `Lj^* RHom(K, N) ⟶ RHom(Lj^* K, Lj^* N)` for an open immersion `j` and
  `Rf_* RHom(K, Rf^! N) ⟶ RHom(Rf_* K, N)` for a proper `f` are not known to be isomorphisms:
  the isomorphisms `AlgebraicGeometry.Etale.nonempty_iso_mapDerivedCategory_upperStar_derivedHom`
  and `AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso` are built by uniqueness of
  adjoints and are not identified with them.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]

/-- Whether the unit of an adjunction is an isomorphism at an object only depends on the left
adjoint up to isomorphism. -/
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

/-- The double-dual morphism as a unit: the contravariant functor `[-, W]` is adjoint to itself on
the right, with unit the double-dual map `CategoryTheory.MonoidalClosed.toIhomIhom`. -/
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

/-- The unit of the self-adjunction of `[-, W]` is the double-dual map `X ⟶ [[X, W], W]`. -/
lemma ihomFlipSelfAdjunction_unit_app (W X : C) :
    (ihomFlipSelfAdjunction W).unit.app X = toIhomIhom W X := by
  change curry ((β_ _ X).hom ≫ uncurry (𝟙 _)) = _
  rw [uncurry_id_eq_ev]
  rfl

/-- Biduality relative to `W` is invariant under twisting by an invertible object: for `L`
invertible, the double-dual map of `X ⊗ L` is an isomorphism if and only if that of `X` is. -/
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

/-- The comparison `G [X, W] ⟶ [G X, G W] ⟶ [G X, W']` of duals along a lax monoidal functor `G`
and a map `e : G W ⟶ W'`. For the derived direct image along a proper morphism and the trace
`Rf_* ω_X ⟶ ω_Y` it is the Verdier exchange `Rf_* 𝔻_X ⟶ 𝔻_Y Rf_*`; for the restriction to an
open subscheme and `j^* ω_Y ≅ ω_W` it is `j^* 𝔻_Y ⟶ 𝔻_W j^*`. -/
noncomputable def dualComparison (X : C) : G.obj ((ihom X).obj W) ⟶ (ihom (G.obj X)).obj W' :=
  (Functor.LaxMonoidal.ihomComparison G X).app W ≫ (ihom (G.obj X)).map e

/-- The double-dual map is compatible with lax braided functors: for `G` lax braided and
`e : G W ⟶ W'`, the square
```
       G X ─────────── G δ_X ──────────→ G [[X, W], W]
        │ │
   δ_{G X} dualComparison [X, W]
        ↓ ↓
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

/-- If the dual comparisons of `X` and of `[X, W]` along a lax braided functor `G` are
isomorphisms, then `G δ_X` is isomorphic, as an arrow, to the double-dual map of `G X` relative
to `W'`. -/
noncomputable def mapToIhomIhomArrowIso (X : C) [IsIso (dualComparison G e X)]
    [IsIso (dualComparison G e ((ihom X).obj W))] :
    Arrow.mk (G.map (toIhomIhom W X)) ≅ Arrow.mk (toIhomIhom W' (G.obj X)) :=
  haveI := isIso_pre_app (dualComparison G e X) W'
  Arrow.isoMk (Iso.refl _)
    (asIso (dualComparison G e ((ihom X).obj W)) ≪≫
      (asIso ((pre (dualComparison G e X)).app W')).symm)
    (by simp [map_toIhomIhom_comp_dualComparison_assoc])

/-- If the dual comparisons of `X` and of `[X, W]` along a lax braided functor `G` are
isomorphisms, then `G δ_X` is an isomorphism if and only if the double-dual map of `G X` relative
to `W'` is. -/
theorem isIso_map_toIhomIhom_iff (X : C) [IsIso (dualComparison G e X)]
    [IsIso (dualComparison G e ((ihom X).obj W))] :
    IsIso (G.map (toIhomIhom W X)) ↔ IsIso (toIhomIhom W' (G.obj X)) :=
  (MorphismProperty.isomorphisms D).arrow_mk_iso_iff (mapToIhomIhomArrowIso G e X)

end Functor

end MonoidalClosed

namespace Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A five lemma for a natural transformation `δ : 𝟭 ⟶ F` to an endofunctor `F` which sends
distinguished triangles to triangles that are distinguished for *some* third morphism. If `δ` is
an isomorphism at `T.obj₁`, `T.obj₃`, `T.obj₁⟦1⟧` and `T.obj₃⟦-1⟧` for a distinguished triangle
`T`, then it is an isomorphism at `T.obj₂`. -/
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

namespace AlgebraicGeometry

open Scheme CategoryTheory.Pretriangulated

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- The Verdier dual on morphisms is `RHom(-, ω_X)`. -/
lemma verdierDual_map
    {K K' : (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))ᵒᵖ}
    (f : K ⟶ K') :
    (verdierDual Λ a).map f = ((RHom(X)[ModuleCat.{u + 1} Λ]).map f).app (dualizingComplex Λ a) :=
  rfl

/-- The double internal hom `RHom(RHom(-, ω), ω)` into an object `ω` carries a distinguished
triangle to a triangle whose first two maps are induced by those of the given triangle and which
is distinguished for a suitable third map. It is stated for a general coefficient category `A`.
-/
theorem exists_distTriang_derivedHom_flip_derivedHom_flip
    (ω : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)))
    (hT : T ∈ distTriang _) :
    ∃ w, Triangle.mk ((((RHom(X)[A]).flip.obj ω).rightOp ⋙ (RHom(X)[A]).flip.obj ω).map T.mor₁)
      ((((RHom(X)[A]).flip.obj ω).rightOp ⋙ (RHom(X)[A]).flip.obj ω).map T.mor₂) w ∈
        distTriang _ := by
  obtain ⟨w, hw⟩ := exists_distTriang_derivedHom_left ω T hT
  obtain ⟨w', hw'⟩ := exists_distTriang_derivedHom_left ω _ hw
  exact ⟨w', hw'⟩

/-- The double dual `𝔻_X 𝔻_X` carries a distinguished triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁⟦1⟧` to a
triangle `𝔻𝔻K₁ ⟶ 𝔻𝔻K₂ ⟶ 𝔻𝔻K₃ ⟶ 𝔻𝔻K₁⟦1⟧` whose first two maps are induced by those of the given
triangle and which is distinguished for a suitable third map. -/
theorem exists_distTriang_verdierDual_verdierDual
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _) :
    ∃ w, Triangle.mk (((verdierDual Λ a).rightOp ⋙ verdierDual Λ a).map T.mor₁)
      (((verdierDual Λ a).rightOp ⋙ verdierDual Λ a).map T.mor₂) w ∈ distTriang _ := by
  rw [show verdierDual Λ a =
    (RHom(X)[ModuleCat.{u + 1} Λ]).flip.obj (dualizingComplex Λ a) from rfl]
  exact exists_distTriang_derivedHom_flip_derivedHom_flip _ (dualizingComplex Λ a) T hT

/-- Whether the double-dual morphism `δ_K` is an isomorphism only depends on `K` up to
isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_iff_of_iso
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') :
    IsIso ((verdierDualDoubleDual Λ a).app K) ↔ IsIso ((verdierDualDoubleDual Λ a).app K') :=
  NatTrans.isIso_app_iff_of_iso _ e

/-- The double-dual morphism is compatible with shifts: `δ_{K⟦n⟧}` is an isomorphism if and only
if `δ_K` is. -/
theorem isIso_verdierDualDoubleDual_app_shift_iff
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    IsIso ((verdierDualDoubleDual Λ a).app (K⟦n⟧)) ↔
      IsIso ((verdierDualDoubleDual Λ a).app K) := by
  let e : K⟦n⟧ ≅ K ⊗ (𝟙_ _)⟦n⟧ :=
    ((((curriedTensor _).obj K).commShiftIso n).app (𝟙_ _) ≪≫
      (shiftFunctor _ n).mapIso (ρ_ K)).symm
  rw [isIso_verdierDualDoubleDual_app_iff_of_iso Λ a e, verdierDualDoubleDual_app,
    verdierDualDoubleDual_app]
  exact MonoidalClosed.isIso_toIhomIhom_tensor_iff _ _
    (AlgebraicGeometry.Etale.DerivedCategory.isInvertible_shift isInvertible_unit n)

/-- The double-dual morphism is compatible with distinguished triangles: for a distinguished
triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁⟦1⟧` of `D(X_ét)`, if `δ_{K₁}` and `δ_{K₃}` are isomorphisms, then so
is `δ_{K₂}`. -/
theorem isIso_verdierDualDoubleDual_app_obj₂
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _) (h₁ : IsIso ((verdierDualDoubleDual Λ a).app T.obj₁))
    (h₃ : IsIso ((verdierDualDoubleDual Λ a).app T.obj₃)) :
    IsIso ((verdierDualDoubleDual Λ a).app T.obj₂) := by
  have := (isIso_verdierDualDoubleDual_app_shift_iff Λ a T.obj₁ 1).2 h₁
  have := (isIso_verdierDualDoubleDual_app_shift_iff Λ a T.obj₃ (-1)).2 h₃
  exact isIso_app_obj₂_of_distTriang _ _ (exists_distTriang_verdierDual_verdierDual Λ a) T hT

/-- The *biduality locus*, the complexes `K` of `D(X_ét)` whose double-dual morphism
`δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism. -/
def verdierBidualityLocus :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ IsIso ((verdierDualDoubleDual Λ a).app K)

/-- The biduality locus is closed under isomorphisms. -/
instance verdierBidualityLocus_isClosedUnderIsomorphisms :
    (verdierBidualityLocus Λ a).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ (isIso_verdierDualDoubleDual_app_iff_of_iso Λ a e).1 h⟩

/-- The biduality locus is stable under shifts. -/
instance verdierBidualityLocus_isStableUnderShift :
    (verdierBidualityLocus Λ a).IsStableUnderShift ℤ :=
  ⟨fun n ↦ ⟨fun K hK ↦ (isIso_verdierDualDoubleDual_app_shift_iff Λ a K n).2 hK⟩⟩

/-- The biduality locus is closed under extensions. -/
instance verdierBidualityLocus_isTriangulatedClosed₂ :
    (verdierBidualityLocus Λ a).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ ↦ isIso_verdierDualDoubleDual_app_obj₂ Λ a T hT h₁ h₃

open ZeroObject in
/-- The biduality locus contains the zero object. -/
instance verdierBidualityLocus_containsZero : (verdierBidualityLocus Λ a).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    have h : IsZero ((verdierDual Λ a).obj (op ((verdierDual Λ a).obj
        (op (0 : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))))) :=
      isZero_ihom_obj_of_isZero (isZero_ihom_obj_of_isZero (isZero_zero _) _) _
    exact ⟨⟨0, (isZero_zero _).eq_of_src _ _, h.eq_of_src _ _⟩⟩

/-- The complexes `K` for which `δ_K` is an isomorphism form a triangulated subcategory of
`D(X_ét)`. -/
instance verdierBidualityLocus_isTriangulated :
    (verdierBidualityLocus Λ a).IsTriangulated where

section Localization

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X U S : Scheme.{u}} (a : X ⟶ S) (b : U ⟶ S)
  [HasCompactification a] [HasCompactification b] (j : U ⟶ X) [Etale j] [Surjective j]

/-- Biduality descends along a surjective étale morphism `j : U ⟶ X`: if `Lj^* δ_K` is
identified, as an arrow, with the double-dual morphism `δ_{Lj^* K}` of `U` and the latter is an
isomorphism, then `δ_K` is an isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_of_surjective
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : Arrow.mk ((L((j)^*[ModuleCat.{u + 1} Λ])).map
        ((verdierDualDoubleDual Λ a).app K)) ≅
      Arrow.mk ((verdierDualDoubleDual Λ b).app
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)))
    (h : IsIso ((verdierDualDoubleDual Λ b).app
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))) :
    IsIso ((verdierDualDoubleDual Λ a).app K) :=
  isIso_of_isIso_leftDerivedUpperStar_map_of_surjective Λ j _
    (((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).2 h)

end Localization

end Etale

end AlgebraicGeometry
