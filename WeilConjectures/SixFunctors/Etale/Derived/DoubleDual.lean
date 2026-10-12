/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapClosed
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-!
# The double-dual morphism under proper push-forward

Let `f : X ⟶ Y` be a proper morphism over a base `S`. This file compares the double-dual
morphisms `δ_K : K ⟶ 𝔻 𝔻 K` (`AlgebraicGeometry.Etale.verdierDualDoubleDual`) on `X` and on
`Y` (blueprint `lem-weil-delta-proper-pushforward`).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStarVerdierDualHom`: the ambient exchange
  `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_* K`, the adjoint of the pairing
  `Rf_* K ⊗ᴸ Rf_* 𝔻_X K ⟶ Rf_*(K ⊗ᴸ 𝔻_X K) ⟶ Rf_* ω_X ⟶ ω_Y`.

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedLowerStar_map_verdierDualDoubleDual_app_comp`: the exchange
  carries `Rf_* δ_K` to `δ_{Rf_* K}`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff`: in
  particular `Rf_* δ_K` is an isomorphism if and only if `δ_{Rf_* K}` is.

## Implementation notes

The exchange map is the comparison map `G [K, W] ⟶ [G K, G W]` of the lax monoidal right
adjoint `G = Rf_*` of the oplax monoidal functor `Lf^*`, followed by the counit
`Rf_* ω_X ≅ Rf_* f^! ω_Y ⟶ ω_Y`. It is an isomorphism by the proper projection formula
(`CategoryTheory.Adjunction.isIso_internalAdjunctionHom`), and its compatibility with the
double-dual morphisms is the general
`CategoryTheory.MonoidalClosed.map_toIhomIhom_comp_ihomComparison_comp_ihom_map`, `Rf_*` being
lax braided as the right adjoint of the braided functor `Lf^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_braiding_comp_tensorComparison`).

The statements are made for a general coefficient category `A`: elaborating them directly at
`ModuleCat Λ` makes the kernel unfold the monoidal structures and time out.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [(R(f)_![A]).IsLeftAdjoint]

/-- The adjunction `Rf_* ⊣ Rf^!` of a proper morphism `f`, obtained from `Rf_! ⊣ Rf^!` and the
proper coincidence `Rf_! ≅ Rf_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`). -/
noncomputable def rightDerivedLowerStarUpperShriekAdjunction :
    R((f)_*[A]) ⊣ R(f)^![A] :=
  (rightDerivedUpperShriekAdjunction A f).ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar A f)

attribute [local instance] leftDerivedUpperStarOplaxMonoidal derivedBraidedCategory

instance isIso_projectionHom_derivedUpperStarLowerStarAdjunction
    [IsIso (rightDerivedLowerStarProjectionMap A f)]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso ((derivedUpperStarLowerStarAdjunction A f).projectionHom M L) := by
  rw [Adjunction.projectionHom_eq_rightAdjointProjectionMap _
    (leftDerivedUpperStarTensorComparison A f) (fun _ _ ↦ rfl)]
  exact inferInstanceAs (IsIso (((rightDerivedLowerStarProjectionMap A f).app M).app L))

/-- The derived direct image `Rf_*` is lax braided, as the right adjoint of the derived pullback
`Lf^*`, which is compatible with the braidings. Its lax monoidal structure is
`CategoryTheory.Adjunction.rightAdjointLaxMonoidal` for `Lf^* ⊣ Rf_*`. -/
@[instance_reducible]
noncomputable def rightDerivedLowerStarLaxBraided {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R((f)_*[A]).LaxBraided :=
  (derivedUpperStarLowerStarAdjunction A f).rightAdjointLaxBraidedOfMapBraidingCompδ
    (leftDerivedUpperStar_map_braiding_comp_tensorComparison A f)

variable (aY : Y ⟶ S) [HasCompactification aY] [(R(aY)_![A]).IsLeftAdjoint]
  [HasCompactification (f ≫ aY)] [(R(f ≫ aY)_![A]).IsLeftAdjoint]
  (e : dualizingComplex A (f ≫ aY) ≅ R(f)^![A].obj (dualizingComplex A aY))

/-- The map `Rf_* ω_X ≅ Rf_* f^! ω_Y ⟶ ω_Y` of a proper morphism `f`, for an identification
`e : ω_X ≅ f^! ω_Y`, the second map being the counit of `Rf_* ⊣ Rf^!`. -/
noncomputable def rightDerivedLowerStarDualizingComplexHom :
    R((f)_*[A]).obj (dualizingComplex A (f ≫ aY)) ⟶ dualizingComplex A aY :=
  R((f)_*[A]).map e.hom ≫ (rightDerivedLowerStarUpperShriekAdjunction A f).counit.app _

/-- Blueprint `lem-weil-delta-proper-pushforward`: the ambient exchange
`Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_* K` of a proper morphism `f`, for an identification `e : ω_X ≅ f^! ω_Y`:
the adjoint of the pairing
`Rf_* K ⊗ᴸ Rf_* 𝔻_X K ⟶ Rf_*(K ⊗ᴸ 𝔻_X K) ⟶ Rf_* ω_X ⟶ ω_Y`, that is, the comparison map of the
lax monoidal functor `Rf_*` followed by
`AlgebraicGeometry.Etale.rightDerivedLowerStarDualizingComplexHom`. -/
noncomputable def rightDerivedLowerStarVerdierDualHom
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    R((f)_*[A]).obj ((verdierDual A (f ≫ aY)).obj (op K)) ⟶
      (verdierDual A aY).obj (op (R((f)_*[A]).obj K)) :=
  letI := rightDerivedLowerStarLaxBraided A f
  (ihomComparison R((f)_*[A]) K).natTrans.app _ ≫
    (ihom _).map (rightDerivedLowerStarDualizingComplexHom A f aY e)

/-- The exchange map `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_* K` is the internal adjunction map
`Rf_* RHom(K, f^! ω_Y) ⟶ RHom(Rf_* K, ω_Y)` (`CategoryTheory.Adjunction.internalAdjunctionHom`)
up to the identification `e`. -/
lemma rightDerivedLowerStarVerdierDualHom_eq
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    rightDerivedLowerStarVerdierDualHom A f aY e K =
      R((f)_*[A]).map ((ihom K).map e.hom) ≫
        (derivedUpperStarLowerStarAdjunction A f).internalAdjunctionHom
          (rightDerivedLowerStarUpperShriekAdjunction A f) K (dualizingComplex A aY) := by
  let := rightDerivedLowerStarLaxBraided A f
  dsimp only [rightDerivedLowerStarVerdierDualHom, Adjunction.internalAdjunctionHom,
    rightDerivedLowerStarDualizingComplexHom]
  have h := (ihomComparison R((f)_*[A]) K).natTrans.naturality e.hom
  dsimp only [Functor.comp_map] at h
  rw [Functor.map_comp, ← Category.assoc, ← h, Category.assoc]

instance isIso_rightDerivedLowerStarVerdierDualHom [IsIso (rightDerivedLowerStarProjectionMap A f)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (rightDerivedLowerStarVerdierDualHom A f aY e K) := by
  rw [rightDerivedLowerStarVerdierDualHom_eq]
  have := Adjunction.isIso_internalAdjunctionHom (derivedUpperStarLowerStarAdjunction A f)
    (rightDerivedLowerStarUpperShriekAdjunction A f) K (dualizingComplex A aY)
  infer_instance

/-- The exchange map `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_* K` is natural in `K`. -/
@[reassoc]
lemma rightDerivedLowerStar_map_verdierDual_map_comp_verdierDualHom
    {K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (g : K ⟶ K') :
    R((f)_*[A]).map ((verdierDual A (f ≫ aY)).map g.op) ≫
        rightDerivedLowerStarVerdierDualHom A f aY e K =
      rightDerivedLowerStarVerdierDualHom A f aY e K' ≫
        (verdierDual A aY).map (R((f)_*[A]).map g).op := by
  let := rightDerivedLowerStarLaxBraided A f
  dsimp only [rightDerivedLowerStarVerdierDualHom]
  rw [← Category.assoc]
  erw [map_pre_app_comp_ihomComparison]
  rw [Category.assoc, Category.assoc]
  congr 1
  exact pre_comm_ihom_map _ _

/-- Blueprint `lem-weil-delta-proper-pushforward`: The double-dual morphism under a proper
push-forward.

For `f : X ⟶ Y` proper over `S`, the ambient exchange `Rf_* 𝔻_X ⟶ 𝔻_Y Rf_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarVerdierDualHom`) identifies `Rf_* δ_K` with
`δ_{Rf_* K}`: the square
```
  Rf_* K ──────── Rf_* δ_K ────────→ Rf_* 𝔻_X 𝔻_X K
     │                                     │
  δ_{Rf_* K}                            exchange
     ↓                                     ↓
  𝔻_Y 𝔻_Y Rf_* K ──𝔻_Y(exchange)──→ 𝔻_Y Rf_* 𝔻_X K
```
commutes, for every complex `K`. -/
theorem rightDerivedLowerStar_map_verdierDualDoubleDual_app_comp
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    R((f)_*[A]).map ((verdierDualDoubleDual A (f ≫ aY)).app K) ≫
        rightDerivedLowerStarVerdierDualHom A f aY e ((verdierDual A (f ≫ aY)).obj (op K)) =
      (verdierDualDoubleDual A aY).app (R((f)_*[A]).obj K) ≫
        (verdierDual A aY).map (rightDerivedLowerStarVerdierDualHom A f aY e K).op := by
  let := rightDerivedLowerStarLaxBraided A f
  exact map_toIhomIhom_comp_ihomComparison_comp_ihom_map R((f)_*[A]) _ K
    (rightDerivedLowerStarDualizingComplexHom A f aY e)

include e in
/-- Blueprint `lem-weil-delta-proper-pushforward`: if the projection formula holds for the proper
morphism `f`, then `Rf_* δ_K` is an isomorphism if and only if `δ_{Rf_* K}` is. -/
theorem isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff
    [IsIso (rightDerivedLowerStarProjectionMap A f)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (R((f)_*[A]).map ((verdierDualDoubleDual A (f ≫ aY)).app K)) ↔
      IsIso ((verdierDualDoubleDual A aY).app (R((f)_*[A]).obj K)) := by
  have h := rightDerivedLowerStar_map_verdierDualDoubleDual_app_comp A f aY e K
  constructor
  · intro
    have : IsIso ((verdierDualDoubleDual A aY).app (R((f)_*[A]).obj K) ≫
        (verdierDual A aY).map (rightDerivedLowerStarVerdierDualHom A f aY e K).op) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((verdierDual A aY).map (rightDerivedLowerStarVerdierDualHom A f aY e K).op)
  · intro
    have : IsIso (R((f)_*[A]).map ((verdierDualDoubleDual A (f ≫ aY)).app K) ≫
        rightDerivedLowerStarVerdierDualHom A f aY e ((verdierDual A (f ≫ aY)).obj (op K))) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (rightDerivedLowerStarVerdierDualHom A f aY e _)

end General

end AlgebraicGeometry.Etale
