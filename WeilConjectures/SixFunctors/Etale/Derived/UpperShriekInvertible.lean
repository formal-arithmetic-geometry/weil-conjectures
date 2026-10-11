/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!
# Invertible objects and the exceptional inverse image

For finite coefficients, an invertible tensor factor passes through the exceptional inverse
image: for `f : X ⟶ Y` admitting a compactification and `L` invertible in `D(Y_ét, Λ)`,

`Rf^!(K ⊗ᴸ L) ≅ Rf^! K ⊗ᴸ Lf^* L`,

naturally in `K`. Both sides are right adjoints, of `N ↦ Rf_! N ⊗ᴸ L⁻¹` and of
`N ↦ Rf_!(N ⊗ᴸ Lf^* L⁻¹)`, tensoring with an invertible object being an equivalence; and these
left adjoints agree by the projection formula. This is the general form of the co-projection
of blueprint `sk-lem-coprojection`, used in the composition law for cohomologically smooth
morphisms (`lem-pur-co-smooth-composition`).

Alongside: invertible objects are stable under derived pullback and under the derived tensor
product.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible.leftDerivedUpperStar`
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible.derivedTensor`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_derivedTensorRight`
- `AlgebraicGeometry.Etale.isInvertible_derivedTensor`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X Y : Scheme.{u}}

/-- The tensor product of two invertible objects of `D(X_ét)` is invertible. -/
theorem isInvertible_derivedTensor
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hL : IsInvertible L) (hL' : IsInvertible L') : IsInvertible (L ⊗ L') := by
  obtain ⟨M, ⟨e₁⟩, ⟨e₂⟩⟩ := hL
  obtain ⟨M', ⟨e₁'⟩, ⟨e₂'⟩⟩ := hL'
  exact ⟨M' ⊗ M, ⟨α_ L L' (M' ⊗ M) ≪≫ whiskerLeftIso L ((α_ L' M' M).symm ≪≫
      whiskerRightIso e₁' M ≪≫ λ_ M) ≪≫ e₁⟩,
    ⟨α_ M' M (L ⊗ L') ≪≫ whiskerLeftIso M' ((α_ M L L').symm ≪≫
      whiskerRightIso e₂ L' ≪≫ λ_ L') ≪≫ e₂'⟩⟩

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]

/-- **An invertible tensor factor passes through `Rf^!`.** For `f` admitting a compactification
and satisfying the projection formula, and `L` invertible in `D(Y_ét)`,

`Rf^!(K ⊗ᴸ L) ≅ Rf^! K ⊗ᴸ Lf^* L`,

naturally in `K`. With `M` a tensor inverse of `L`, both functors are right adjoints: tensoring
with `L` is right adjoint to tensoring with `M`, being an equivalence
(`CategoryTheory.tensorRightEquivalenceOfTensorIso`), and similarly for `Lf^* L` and `Lf^* M`.
Their left adjoints `N ↦ Rf_! N ⊗ᴸ M` and `N ↦ Rf_!(N ⊗ᴸ Lf^* M)` agree by the projection
formula. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_derivedTensorRight_of_isInvertible
    (hPF : ∀ K M, HasProjectionFormula A f K M)
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (hL : IsInvertible L) :
    Nonempty (derivedTensorRight A Y L ⋙ R(f)^![A] ≅
      R(f)^![A] ⋙ derivedTensorRight A X ((L((f)^*[A])).obj L)) := by
  obtain ⟨M, ⟨e₁⟩, ⟨e₂⟩⟩ := hL
  let adjY : derivedTensorRight A Y M ⊣ derivedTensorRight A Y L :=
    (tensorRightEquivalenceOfTensorIso e₁ e₂).symm.toAdjunction
  let fL := (L((f)^*[A])).obj L
  let fM := (L((f)^*[A])).obj M
  let e₁' : fL ⊗ fM ≅ 𝟙_ _ := (leftDerivedUpperStarTensorIso A f L M).symm ≪≫
    (L((f)^*[A])).mapIso e₁ ≪≫ leftDerivedUpperStarUnitIso A f
  let e₂' : fM ⊗ fL ≅ 𝟙_ _ := (leftDerivedUpperStarTensorIso A f M L).symm ≪≫
    (L((f)^*[A])).mapIso e₂ ≪≫ leftDerivedUpperStarUnitIso A f
  let adjX : derivedTensorRight A X fM ⊣ derivedTensorRight A X fL :=
    (tensorRightEquivalenceOfTensorIso e₁' e₂').symm.toAdjunction
  obtain ⟨ι⟩ := nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight A f M
    (fun K ↦ hPF K M)
  exact ⟨Adjunction.rightAdjointUniq
    (((rightDerivedUpperShriekAdjunction A f).comp adjY).ofNatIsoLeft ι)
    (adjX.comp (rightDerivedUpperShriekAdjunction A f))⟩

end General

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}}

/-- The derived pullback of an invertible object is invertible: `Lf^*` is monoidal, so
`Lf^* L ⊗ᴸ Lf^* M ≅ Lf^*(L ⊗ᴸ M) ≅ Lf^* Λ_Y ≅ Λ_X` for a tensor inverse `M` of `L`. -/
theorem DerivedCategory.isInvertible.leftDerivedUpperStar (f : X ⟶ Y)
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.isInvertible Λ Y L) :
    DerivedCategory.isInvertible Λ X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L) := by
  obtain ⟨M, ⟨e⟩, ⟨e'⟩⟩ := hL
  exact ⟨(L((f)^*[ModuleCat.{u + 1} Λ])).obj M,
    ⟨(leftDerivedUpperStarTensorIso _ f L M).symm ≪≫ (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫
      leftDerivedUpperStarUnitIso _ f⟩,
    ⟨(leftDerivedUpperStarTensorIso _ f M L).symm ≪≫ (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso e' ≪≫
      leftDerivedUpperStarUnitIso _ f⟩⟩

/-- The derived tensor product of two invertible objects is invertible. -/
theorem DerivedCategory.isInvertible.derivedTensor
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.isInvertible Λ X L) (hL' : DerivedCategory.isInvertible Λ X L') :
    DerivedCategory.isInvertible Λ X
      (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj L).obj L') :=
  (isInvertible_iff_exists_derivedTensor _).1 (isInvertible_derivedTensor
    ((isInvertible_iff_exists_derivedTensor _).2 hL)
    ((isInvertible_iff_exists_derivedTensor _).2 hL'))

variable (Λ) [Finite Λ] (f : X ⟶ Y) [HasCompactification f]

/-- **An invertible tensor factor passes through `Rf^!`**, finite coefficients: for `f`
admitting a compactification and `L` invertible in `D(Y_ét, Λ)`,

`Rf^!(K ⊗ᴸ L) ≅ Rf^! K ⊗ᴸ Lf^* L`,

naturally in `K`: the general statement for coefficients satisfying the projection formula,
together with the projection formula at finite coefficients
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`). -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_derivedTensorRight
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.isInvertible Λ Y L) :
    Nonempty (derivedTensorRight _ Y L ⋙ R(f)^![ModuleCat.{u + 1} Λ] ≅
      R(f)^![ModuleCat.{u + 1} Λ] ⋙
        derivedTensorRight _ X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
  nonempty_iso_rightDerivedUpperShriek_comp_derivedTensorRight_of_isInvertible f
    (hasProjectionFormula_of_finite Λ f) ((isInvertible_iff_exists_derivedTensor _).2 hL)

end Etale

end AlgebraicGeometry
