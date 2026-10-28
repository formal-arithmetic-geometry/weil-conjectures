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
public import WeilConjectures.CategoryTheory.Monoidal.Closed.DoubleDual

/-!
# The double-dual morphism: shifts, triangles, restriction and push-forward

Let `a : X ⟶ S` admit a compactification, `ω_X = Ra^! Λ_S` and `𝔻_X = RHom(-, ω_X)`. This file
records the formal properties of the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`
(`AlgebraicGeometry.Etale.verdierDualDoubleDual`) used in the dévissage proof of Verdier
biduality (blueprint subsection `sk-prop-sf-biduality-general`).
The category-theoretic parts (the self-adjunction of `[-, W]`, twisting by invertible objects,
lax braided functors and the five lemma below) are in
`WeilConjectures.CategoryTheory.Monoidal.Closed.DoubleDual`.

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

namespace AlgebraicGeometry

open Scheme CategoryTheory.Pretriangulated

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- Blueprint `lem-weil-duality-pairing` (auxiliary): the Verdier dual on morphisms is
`RHom(-, ω_X)`. -/
lemma verdierDual_map
    {K K' : (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))ᵒᵖ}
    (f : K ⟶ K') :
    (verdierDual Λ a).map f = ((RHom(X)[ModuleCat.{u + 1} Λ]).map f).app (dualizingComplex Λ a) :=
  rfl

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

/-- Blueprint `lem-weil-duality-pairing`: the double dual `𝔻_X 𝔻_X` carries a distinguished
triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁⟦1⟧` to a triangle `𝔻𝔻K₁ ⟶ 𝔻𝔻K₂ ⟶ 𝔻𝔻K₃ ⟶ 𝔻𝔻K₁⟦1⟧` whose first
two maps are induced by those of the given triangle and which is distinguished for a suitable
third map: `RHom(-, ω_X)` is exact (`AlgebraicGeometry.Etale.exists_distTriang_derivedHom_left`,
blueprint `lem-sf-hom-triangulated`), applied twice. -/
theorem exists_distTriang_verdierDual_verdierDual
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _) :
    ∃ w, Triangle.mk (((verdierDual Λ a).rightOp ⋙ verdierDual Λ a).map T.mor₁)
      (((verdierDual Λ a).rightOp ⋙ verdierDual Λ a).map T.mor₂) w ∈ distTriang _ := by
  rw [show verdierDual Λ a =
    (RHom(X)[ModuleCat.{u + 1} Λ]).flip.obj (dualizingComplex Λ a) from rfl]
  exact exists_distTriang_derivedHom_flip_derivedHom_flip _ (dualizingComplex Λ a) T hT

/-- Blueprint `lem-weil-duality-pairing`: the double-dual morphism `δ_K` is natural, so whether
it is an isomorphism only depends on `K` up to isomorphism. -/
theorem isIso_verdierDualDoubleDual_app_iff_of_iso
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : K ≅ K') :
    IsIso ((verdierDualDoubleDual Λ a).app K) ↔ IsIso ((verdierDualDoubleDual Λ a).app K') :=
  NatTrans.isIso_app_iff_of_iso _ e

/-- Blueprint `lem-weil-duality-pairing`: the double-dual morphism is compatible with shifts,
`δ_{K⟦n⟧}` is an isomorphism if and only if `δ_K` is.

As `K⟦n⟧ ≅ K ⊗ᴸ Λ_X⟦n⟧` with `Λ_X⟦n⟧` invertible, this is the invariance of biduality under
twisting by an invertible object, `CategoryTheory.MonoidalClosed.isIso_toIhomIhom_tensor_iff`. -/
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

/-- Blueprint `lem-weil-duality-pairing`: the double-dual morphism is compatible with
distinguished triangles. For a distinguished triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁⟦1⟧` of `D(X_ét)`, if
`δ_{K₁}` and `δ_{K₃}` are isomorphisms, then so is `δ_{K₂}`.

This is the triangulated five lemma
(`CategoryTheory.Pretriangulated.isIso_app_obj₂_of_distTriang`) for the natural
transformation `δ : 𝟭 ⟶ 𝔻_X 𝔻_X`, using the exactness of `𝔻_X 𝔻_X`
(`AlgebraicGeometry.Etale.exists_distTriang_verdierDual_verdierDual`) and the compatibility of
`δ` with shifts (`AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app_shift_iff`). -/
theorem isIso_verdierDualDoubleDual_app_obj₂
    (T : Triangle (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hT : T ∈ distTriang _) (h₁ : IsIso ((verdierDualDoubleDual Λ a).app T.obj₁))
    (h₃ : IsIso ((verdierDualDoubleDual Λ a).app T.obj₃)) :
    IsIso ((verdierDualDoubleDual Λ a).app T.obj₂) := by
  have := (isIso_verdierDualDoubleDual_app_shift_iff Λ a T.obj₁ 1).2 h₁
  have := (isIso_verdierDualDoubleDual_app_shift_iff Λ a T.obj₃ (-1)).2 h₃
  exact isIso_app_obj₂_of_distTriang _ _ (exists_distTriang_verdierDual_verdierDual Λ a) T hT

/-- Blueprint `lem-weil-duality-pairing`: the *biduality locus*, the complexes `K` of `D(X_ét)`
whose double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism. It is a triangulated
subcategory (`AlgebraicGeometry.Etale.verdierBidualityLocus_isTriangulated`). -/
def verdierBidualityLocus :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ IsIso ((verdierDualDoubleDual Λ a).app K)

/-- Blueprint `lem-weil-duality-pairing`: the biduality locus is closed under isomorphisms. -/
instance verdierBidualityLocus_isClosedUnderIsomorphisms :
    (verdierBidualityLocus Λ a).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ (isIso_verdierDualDoubleDual_app_iff_of_iso Λ a e).1 h⟩

/-- Blueprint `lem-weil-duality-pairing`: the biduality locus is stable under shifts. -/
instance verdierBidualityLocus_isStableUnderShift :
    (verdierBidualityLocus Λ a).IsStableUnderShift ℤ :=
  ⟨fun n ↦ ⟨fun K hK ↦ (isIso_verdierDualDoubleDual_app_shift_iff Λ a K n).2 hK⟩⟩

/-- Blueprint `lem-weil-duality-pairing`: the biduality locus is closed under extensions. -/
instance verdierBidualityLocus_isTriangulatedClosed₂ :
    (verdierBidualityLocus Λ a).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ ↦ isIso_verdierDualDoubleDual_app_obj₂ Λ a T hT h₁ h₃

open ZeroObject in
/-- Blueprint `lem-weil-duality-pairing`: the biduality locus contains the zero object, whose
double dual is zero. -/
instance verdierBidualityLocus_containsZero : (verdierBidualityLocus Λ a).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    have h : IsZero ((verdierDual Λ a).obj (op ((verdierDual Λ a).obj
        (op (0 : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))))) :=
      isZero_ihom_obj_of_isZero (isZero_ihom_obj_of_isZero (isZero_zero _) _) _
    exact ⟨⟨0, (isZero_zero _).eq_of_src _ _, h.eq_of_src _ _⟩⟩

/-- Blueprint `lem-weil-duality-pairing`: since the double-dual morphism commutes with shifts
and is a morphism of distinguished triangles, the complexes `K` for which `δ_K` is an
isomorphism form a triangulated subcategory of `D(X_ét)`. -/
instance verdierBidualityLocus_isTriangulated :
    (verdierBidualityLocus Λ a).IsTriangulated where

section Localization

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X U S : Scheme.{u}} (a : X ⟶ S) (b : U ⟶ S)
  [HasCompactification a] [HasCompactification b] (j : U ⟶ X) [Etale j] [Surjective j]

/-- Blueprint `lem-weil-delta-restriction`: biduality is local for the étale topology, the
descent step. Let `j : U ⟶ X` be étale and surjective (for instance the disjoint union of the
members of an open cover). If `Lj^* δ_K` is identified, as an arrow, with the double-dual
morphism `δ_{Lj^* K}` of `U` and the latter is an isomorphism, then `δ_K` is an isomorphism,
isomorphisms descending along `j`
(`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`).

The identification of `Lj^* δ_K` with `δ_{Lj^* K}` is the content of the blueprint lemma; its
formal core is `CategoryTheory.MonoidalClosed.mapToIhomIhomArrowIso`, see the module
docstring for what remains to apply it to `Lj^*`. -/
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
