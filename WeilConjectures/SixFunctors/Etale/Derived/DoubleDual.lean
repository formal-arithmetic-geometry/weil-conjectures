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
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

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


section Restriction

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

attribute [local instance] derivedBraidedCategory

variable {Z Y S S' : Scheme.{u}} (g : Z ⟶ Y) (aY : Y ⟶ S) [HasCompactification aY]
  [(R(aY)_![A]).IsLeftAdjoint] (aZ : Z ⟶ S') [HasCompactification aZ]
  [(R(aZ)_![A]).IsLeftAdjoint]
  (e : L((g)^*[A]).obj (dualizingComplex A aY) ⟶ dualizingComplex A aZ)

/-- Blueprint `lem-weil-delta-restriction`: the comparison `Lg^* 𝔻_Y K ⟶ 𝔻_Z Lg^* K` of the
derived pullback along `g : Z ⟶ Y` with the Verdier duals, for a map
`e : Lg^* ω_Y ⟶ ω_Z`: the comparison map `Lg^* RHom(K, ω_Y) ⟶ RHom(Lg^* K, Lg^* ω_Y)` of the
monoidal functor `Lg^*`, followed by `e`. -/
noncomputable def leftDerivedUpperStarVerdierDualHom
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).obj ((verdierDual A aY).obj (op K)) ⟶
      (verdierDual A aZ).obj (op (L((g)^*[A]).obj K)) :=
  letI := leftDerivedUpperStarBraided A g
  (ihomComparison L((g)^*[A]) K).natTrans.app _ ≫ (ihom _).map e

/-- Blueprint `lem-weil-delta-restriction`: The double-dual morphism restricts.

For `g : Z ⟶ Y` and a map `e : Lg^* ω_Y ⟶ ω_Z`, the comparison
`Lg^* 𝔻_Y ⟶ 𝔻_Z Lg^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarVerdierDualHom`) identifies
`Lg^* δ_K` with `δ_{Lg^* K}`: the square
```
  Lg^* K ──────── Lg^* δ_K ────────→ Lg^* 𝔻_Y 𝔻_Y K
     │                                     │
  δ_{Lg^* K}                          comparison
     ↓                                     ↓
  𝔻_Z 𝔻_Z Lg^* K ──𝔻_Z(comparison)──→ 𝔻_Z Lg^* 𝔻_Y K
```
commutes. For `g` an open immersion, the comparison is an isomorphism
(`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStarVerdierDualHom`). -/
theorem leftDerivedUpperStar_map_verdierDualDoubleDual_app_comp
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map ((verdierDualDoubleDual A aY).app K) ≫
        leftDerivedUpperStarVerdierDualHom A g aY aZ e ((verdierDual A aY).obj (op K)) =
      (verdierDualDoubleDual A aZ).app (L((g)^*[A]).obj K) ≫
        (verdierDual A aZ).map (leftDerivedUpperStarVerdierDualHom A g aY aZ e K).op := by
  letI := leftDerivedUpperStarBraided A g
  exact map_toIhomIhom_comp_ihomComparison_comp_ihom_map L((g)^*[A]) _ K e

section OpenImmersion

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- The adjunction `D(j_!) ⊣ Lj^*` along an open immersion `j`, from `D(j_!) ⊣ D(j^*)` and
`Lj^* ≅ D(j^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction :
    D((j)_!open[A]) ⊣ L((j)^*[A]) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory A j).symm

instance isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_unit :
    IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).unit := by
  have : (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).unit =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit ≫
        Functor.whiskerLeft D((j)_!open[A]) (leftDerivedUpperStarIsoMapDerivedCategory A j).inv := by
    ext K
    simp [derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
      Adjunction.ofNatIsoRight, Adjunction.homEquiv_unit]
  rw [this]
  infer_instance

include hJ in
/-- The left projection map `D(j_!)(Lj^* K ⊗ᴸ N) ⟶ K ⊗ᴸ D(j_!) N` of an open immersion `j`
(`CategoryTheory.Adjunction.leftProjectionHom`) is an isomorphism: after `Lj^*` it is an
isomorphism since the unit of `D(j_!) ⊣ Lj^*` is, and after restriction to the closed complement
of `j` both sides vanish. -/
lemma isIso_leftProjectionHom_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarBraided A j
    IsIso ((derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).leftProjectionHom
      K N) := by
  letI := leftDerivedUpperStarBraided A j
  let adj := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j
  refine isIso_of_isIso_leftDerivedUpperStar_closedComplement_map A j _ ?_ ?_
  · have h : adj.unit.app _ ≫ L((j)^*[A]).map (adj.leftProjectionHom K N) =
        L((j)^*[A]).obj K ◁ adj.unit.app N ≫ μ L((j)^*[A]) K (D((j)_!open[A]).obj N) := by
      rw [Adjunction.leftProjectionHom]
      exact (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
    have : IsIso (adj.unit.app _ ≫ L((j)^*[A]).map (adj.leftProjectionHom K N)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left (adj.unit.app _) _
  · exact isIso_of_source_target_iso_zero _
      (isZero_leftDerivedUpperStar_closedComplement_obj_openImmersionLowerShriek A j _).isoZero
      ((isZero_derivedTensor_obj_obj_of_isZero_right (L((j.closedComplement)^*[A]).obj K)
        (isZero_leftDerivedUpperStar_closedComplement_obj_openImmersionLowerShriek A j N)).of_iso
          (leftDerivedUpperStarTensorIso A j.closedComplement K _)).isoZero

include hJ in
/-- **Restriction to an open commutes with the internal hom.** For an open immersion `j`, the
comparison map `Lj^* RHom(K, L) ⟶ RHom(Lj^* K, Lj^* L)` of the monoidal functor `Lj^*` is an
isomorphism, by the projection formula for `j_!`. -/
lemma isIso_ihomComparison_leftDerivedUpperStar_of_isOpenImmersion
    (K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarBraided A j
    IsIso ((ihomComparison L((j)^*[A]) K).natTrans.app L) := by
  letI := leftDerivedUpperStarBraided A j
  have := isIso_leftProjectionHom_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction
    A j K
  exact (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction A j
    ).isIso_ihomComparison_of_isIso_leftProjectionHom K L

variable (aU : U ⟶ S') [HasCompactification aU] [(R(aU)_![A]).IsLeftAdjoint]
  (e : L((j)^*[A]).obj (dualizingComplex A aY) ⟶ dualizingComplex A aU)

include hJ in
lemma isIso_leftDerivedUpperStarVerdierDualHom [IsIso e]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (leftDerivedUpperStarVerdierDualHom A j aY aU e K) := by
  letI := leftDerivedUpperStarBraided A j
  have := isIso_ihomComparison_leftDerivedUpperStar_of_isOpenImmersion A j K
    (dualizingComplex A aY)
  dsimp only [leftDerivedUpperStarVerdierDualHom]
  infer_instance

include hJ in
/-- Blueprint `lem-weil-delta-restriction`: biduality restricts to opens. For an open immersion
`j : U ⟶ Y` and an isomorphism `e : Lj^* ω_Y ≅ ω_U`, the restriction `Lj^* δ_K` of the
double-dual morphism is an isomorphism if and only if the double-dual morphism `δ_{Lj^* K}` of
the restriction is. -/
theorem isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff [IsIso e]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (L((j)^*[A]).map ((verdierDualDoubleDual A aY).app K)) ↔
      IsIso ((verdierDualDoubleDual A aU).app (L((j)^*[A]).obj K)) := by
  have h := leftDerivedUpperStar_map_verdierDualDoubleDual_app_comp A j aY aU e K
  have := isIso_leftDerivedUpperStarVerdierDualHom A aY j aU e K
  have := isIso_leftDerivedUpperStarVerdierDualHom A aY j aU e ((verdierDual A aY).obj (op K))
  constructor
  · intro
    have : IsIso ((verdierDualDoubleDual A aU).app (L((j)^*[A]).obj K) ≫
        (verdierDual A aU).map (leftDerivedUpperStarVerdierDualHom A j aY aU e K).op) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((verdierDual A aU).map (leftDerivedUpperStarVerdierDualHom A j aY aU e K).op)
  · intro
    have : IsIso (L((j)^*[A]).map ((verdierDualDoubleDual A aY).app K) ≫
        leftDerivedUpperStarVerdierDualHom A j aY aU e ((verdierDual A aY).obj (op K))) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (leftDerivedUpperStarVerdierDualHom A j aY aU e ((verdierDual A aY).obj (op K)))

end OpenImmersion

end Restriction

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-weil-delta-proper-pushforward`, at a finite coefficient ring `Λ`: for
`f : X ⟶ Y` proper over `S`, `Rf_* δ_K` is an isomorphism if and only if `δ_{Rf_* K}` is. -/
theorem isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff_of_finite
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (aY : Y ⟶ S) [HasCompactification aY]
    [HasCompactification (f ≫ aY)] [QuasiCompact (f ≫ aY)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (R((f)_*[ModuleCat.{u + 1} Λ]).map
        ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) (f ≫ aY)).app K)) ↔
      IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aY).app
        (R((f)_*[ModuleCat.{u + 1} Λ]).obj K)) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ f aY
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite Λ f
  exact isIso_rightDerivedLowerStar_map_verdierDualDoubleDual_app_iff _ f aY (e.app (𝟙_ _)) K

/-- Blueprint `lem-weil-delta-restriction`, at a finite coefficient ring `Λ`: for a
quasi-compact open immersion `j : U ⟶ Y` and `Y` over `S`, the restriction `Lj^* δ_K` of the
double-dual morphism of `Y` is an isomorphism if and only if the double-dual morphism
`δ_{Lj^* K}` of `U` is. The dualizing complexes are identified by
`Lj^* ω_Y ≅ Rj^! ω_Y ≅ ω_U` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion`,
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`). -/
theorem isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff_of_finite
    {U Y S : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [HasCompactification j]
    [QuasiCompact j] (aY : Y ⟶ S) [HasCompactification aY] [HasCompactification (j ≫ aY)]
    [QuasiCompact (j ≫ aY)]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (L((j)^*[ModuleCat.{u + 1} Λ]).map
        ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) aY).app K)) ↔
      IsIso ((verdierDualDoubleDual (ModuleCat.{u + 1} Λ) (j ≫ aY)).app
        (L((j)^*[ModuleCat.{u + 1} Λ]).obj K)) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ j aY
  let e' : L((j)^*[ModuleCat.{u + 1} Λ]).obj (dualizingComplex _ aY) ≅
      dualizingComplex _ (j ≫ aY) :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
      (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).symm.app _ ≪≫ (e.app (𝟙_ _)).symm
  exact isIso_leftDerivedUpperStar_map_verdierDualDoubleDual_app_iff _ aY j (j ≫ aY) e'.hom K

end Finite

end AlgebraicGeometry.Etale
