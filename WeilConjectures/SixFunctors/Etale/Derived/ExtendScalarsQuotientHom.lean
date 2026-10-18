/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsQuotientDerived
public import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# Internal adjunction for the derived extension of scalars along a quotient ring

Let `J` be an ideal of a commutative ring `Λ`. The derived extension of scalars
`LE : D(X_ét, Λ) ⥤ D(X_ét, Λ ⧸ J)` is monoidal and left adjoint to restriction of scalars `Res`
(`AlgebraicGeometry.Etale.derivedExtendScalarsAdjunction`), so that it satisfies the internal
adjunction `RHom_Λ(K, Res N) ≅ Res RHom_{Λ ⧸ J}(LE K, N)`
(`AlgebraicGeometry.Etale.derivedHomCompIsoOfAdjunction`). For a derived base change
`η : K ⟶ Res K'` this gives `RHom_Λ(K, Res N) ≅ Res RHom_{Λ ⧸ J}(K', N)`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedHom_restrictScalars_of_isDerivedBaseChange`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

open Scheme

-- The derived tensor product of étale sheaves (`AlgebraicGeometry.Etale.derivedTensor`) is defined
-- for a symmetric monoidal coefficient category, with the braiding of the symmetric structure;
-- finding the braiding of `ModuleCat` through the same path avoids expensive kernel unfoldings.
attribute [local instance high] SymmetricCategory.toBraidedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] (J : Ideal Λ) (X : Scheme.{u})

/-- The small étale site of a scheme is locally small. Instance search does not find this in the
presence of the imports of this file. -/
local instance (X : Scheme.{u}) : LocallySmall.{u + 1} X.Etale :=
  @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  essentiallySmall_of_small_of_locallySmall _

section

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {B : Type u'} [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] {X}
  {F : Sheaf X.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology B} [F.Additive]
  [F.PreservesKFlatQuasiIso] [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  {R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}

/-- For a monoidal functor `F` of étale sheaves with derived functor `LF` left adjoint to `R`,
`R ⋙ RHom(K, -) ≅ RHom(LF K, -) ⋙ R`: both are right adjoint to
`T ↦ LF(K ⊗ᴸ T) ≅ LF K ⊗ᴸ LF T`. -/
noncomputable def derivedHomCompIsoOfAdjunction (adj : F.leftDerivedFunctor ⊣ R)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    R ⋙ (derivedHom A X).obj (op K) ≅ (derivedHom B X).obj (op (F.leftDerivedFunctor.obj K)) ⋙ R :=
  (((derivedTensorHomAdjunction A K).comp adj).ofNatIsoLeft
    (F.leftDerivedTensorIsoOfKFlat K)).rightAdjointUniq
    (adj.comp (derivedTensorHomAdjunction B _))

/-- **Internal adjunction for a universal arrow.** In the situation of
`AlgebraicGeometry.Etale.derivedHomCompIsoOfAdjunction`, if `η : K ⟶ R K'` is universal among
morphisms from `K` to objects in the image of `R`, then
`RHom(K, R N) ≅ R RHom(K', N)` for every `N`. -/
theorem nonempty_iso_derivedHom_of_bijective (adj : F.leftDerivedFunctor ⊣ R)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)} (η : K ⟶ R.obj K')
    (hη : ∀ N, Function.Bijective fun g : K' ⟶ N ↦ η ≫ R.map g)
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    Nonempty (((derivedHom A X).obj (op K)).obj (R.obj N) ≅
      R.obj (((derivedHom B X).obj (op K')).obj N)) := by
  obtain ⟨h, hh₀⟩ := (hη _).2 (adj.unit.app K)
  have hh : η ≫ R.map h = adj.unit.app K := hh₀
  let g := (adj.homEquiv K K').symm η
  have hg : adj.unit.app K ≫ R.map g = η := by
    rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
  have e : F.leftDerivedFunctor.obj K ≅ K' :=
    { hom := g
      inv := h
      hom_inv_id := (adj.homEquiv _ _).injective (by
        simp only [Adjunction.homEquiv_unit, Functor.map_comp, reassoc_of% hg, hh,
          CategoryTheory.Functor.map_id]
        erw [Category.comp_id])
      inv_hom_id := (hη K').1 (by
        simp only [Functor.map_comp, reassoc_of% hh, hg, CategoryTheory.Functor.map_id]
        erw [Category.comp_id]) }
  exact ⟨(derivedHomCompIsoOfAdjunction adj K).app N ≪≫
    R.mapIso (((derivedHom B X).mapIso e.symm.op).app N)⟩

end

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {J X}

set_option maxHeartbeats 4000000 in
-- the kernel compares the derived categories underlying `derivedHom` and the adjunction
/-- **Internal adjunction for a derived base change.** For a derived base change
`η : K ⟶ Res K'` of `K` along `Λ ⟶ Λ ⧸ J` and `N ∈ D(X_ét, Λ ⧸ J)`,
`RHom_Λ(K, Res N) ≅ Res RHom_{Λ ⧸ J}(K', N)`
(`AlgebraicGeometry.Etale.derivedHomCompIsoOfAdjunction`). -/
theorem nonempty_iso_derivedHom_restrictScalars_of_isDerivedBaseChange {K : 𝐃(X, Λ)}
    {K' : 𝐃(X, Λ ⧸ J)}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) (N : 𝐃(X, Λ ⧸ J)) :
    Nonempty (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj N) ≅
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj
        (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ J)) X).obj (op K')).obj N)) := by
  exact nonempty_iso_derivedHom_of_bijective (derivedExtendScalarsAdjunction J X) η hη N

end AlgebraicGeometry.Etale
