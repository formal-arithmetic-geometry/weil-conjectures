/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.HomTriangulated
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The double-dual morphism: shifts, triangles, restriction and push-forward

Let `a : X ⟶ S` admit a compactification, `ω_X = Ra^! Λ_S` and `𝔻_X = RHom(-, ω_X)`. This file
records the formal properties of the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`
(`AlgebraicGeometry.Etale.verdierDualDoubleDual`) used in the dévissage proof of Verdier
biduality (blueprint subsection `sk-prop-sf-biduality-general`).

## Main statements

Blueprint `lem-weil-duality-pairing` (`δ` commutes with shifts and is a morphism of
distinguished triangles), for a general coefficient category `A`:

- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_shift_iff`: `δ_{K⟦n⟧}` is an
  isomorphism if and only if `δ_K` is;
- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_obj₂`: for a distinguished triangle
  `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁⟦1⟧`, if `δ_{K₁}` and `δ_{K₃}` are isomorphisms, so is `δ_{K₂}`;
- `AlgebraicGeometry.Etale.verdierBidualityLocus_isTriangulated`: the complexes `K` with `δ_K`
  an isomorphism form a triangulated subcategory of `D(X_ét)`.

Blueprints `lem-weil-delta-restriction` and `lem-weil-delta-proper-pushforward`, formal core:

- `CategoryTheory.MonoidalClosed.map_toIhomIhom_comp_dualComparison`: for a lax braided functor
  `G` and `e : G W ⟶ W'`, the comparison `G [X, W] ⟶ [G X, W']` carries `G δ_X` to `δ_{G X}`;
- `CategoryTheory.MonoidalClosed.mapToIhomIhomArrowIso`: hence, when the comparisons are
  isomorphisms, `G δ_X` and `δ_{G X}` are isomorphic arrows;
- `AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_of_surjective`: biduality descends
  along a surjective étale morphism once `Lj^* δ_K` is identified with `δ_{Lj^* K}`.

## Implementation notes

The exactness of `RHom(-, ω_X)` available in the repository
(`AlgebraicGeometry.Etale.exists_distTriang_derivedHom_left`) only provides *some* third
morphism for the image of a distinguished triangle, so `δ` is not directly a morphism of
triangles. The triangulated five lemma is therefore proved in the form
`CategoryTheory.Pretriangulated.isIso_app_obj₂_of_distTriang`, which only uses the exactness of
`Hom(Y, 𝔻𝔻 -)` at the middle terms of the images of a triangle and of its rotations; the
connecting maps there are `𝔻𝔻` of those of the triangle, and naturality of `δ` replaces the
compatibility with the third morphisms. It needs `δ` to be invertible at `K₁⟦1⟧` and
`K₃⟦-1⟧`, supplied by the shift compatibility.

The shift compatibility uses `K⟦n⟧ ≅ K ⊗ᴸ Λ_X⟦n⟧` with `Λ_X⟦n⟧` invertible: in a braided
monoidal closed category, `[-, W]` is self-adjoint on the right with unit `δ`
(`CategoryTheory.MonoidalClosed.ihomFlipSelfAdjunction`), and conjugating this adjunction by the
autoequivalences `- ⊗ L` and `[L, -]` shows that `δ_{X ⊗ L}` is invertible if and only if `δ_X`
is (`CategoryTheory.MonoidalClosed.isIso_toIhomIhom_tensor_iff`). No sign bookkeeping is needed,
since the unit of an adjunction is invertible at an object independently of the chosen
adjunction (`CategoryTheory.Adjunction.isIso_unit_app_iff_of_iso`).

## TODO

To deduce `lem-weil-delta-restriction` and `lem-weil-delta-proper-pushforward` from
`CategoryTheory.MonoidalClosed.mapToIhomIhomArrowIso`, two inputs are missing from the
repository:

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

/-- The double internal hom `RHom(RHom(-, ω), ω)` into an object `ω` carries a distinguished
triangle to a triangle whose first two maps are induced by those of the given triangle and which
is distinguished for a suitable third map: `RHom(-, ω)` is exact
(`AlgebraicGeometry.Etale.exists_distTriang_derivedHom_left`), applied twice. It is stated for a
general coefficient category `A`, where the kernel checks it without unfolding the derived
categories of `ModuleCat Λ`. -/
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

/-- Blueprint `lem-weil-duality-pairing`: the double-dual morphism `δ_K` is natural, so whether
it is an isomorphism only depends on `K` up to isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_iff_of_iso
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') :
    IsIso ((verdierDualDoubleDual Λ a).app K) ↔ IsIso ((verdierDualDoubleDual Λ a).app K') :=
  NatTrans.isIso_app_iff_of_iso _ e

section Localization

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X U S : Scheme.{u}} (a : X ⟶ S) (b : U ⟶ S)
  [HasCompactification a] [HasCompactification b] (j : U ⟶ X) [Etale j] [Surjective j]

end Localization

end Etale

end AlgebraicGeometry
