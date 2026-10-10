/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs

/-!

# Kernel transforms are linear over the base

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor`: kernel transforms are linear
  over the base, given the projection formula for the second projection.

See `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` for the implementation notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- A kernel transform is linear over the base: tensoring the input with a complex pulled back
from `S` along `π` is the same as tensoring the output with the same complex pulled back along
`π'`,

`Φ_𝒦(K ⊗ᴸ π^* N) ≅ Φ_𝒦(K) ⊗ᴸ π'^* N`,

naturally in `K` and `N`, provided the projection formula holds for the second projection
`p₂ : V ×_S V' ⟶ V'` on the whole unbounded derived categories.

The shift is first moved into the kernel
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_shift`). Then
`p₁^*(K ⊗ᴸ π^* N) ≅ p₁^* K ⊗ᴸ p₂^* π'^* N` by monoidality of `Lp₁^*` and
`p₁ ≫ π = p₂ ≫ π'`, the factor `p₂^* π'^* N` is moved past `𝒦` with the associator and a
braiding of `D((V ×_S V')_ét)`, and the projection formula for `p₂` concludes.
(sketch blueprint: `sk-prop-base-linear`, proof) -/
theorem nonempty_iso_kernelTransform_tensor [HasCompactification (pullback.snd π π')]
    [IsIso (projectionMap A (pullback.snd π π'))]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a : ℤ) :
    Nonempty (derivedTensorRightPullback A π ⋙
          (Functor.whiskeringRight _ _ _).obj (kernelTransform A π π' 𝒦 a) ≅
        derivedTensorRightPullback A π' ⋙
          (Functor.whiskeringLeft _ _ _).obj (kernelTransform A π π' 𝒦 a)) := by
  -- Move the shift into the kernel.
  obtain ⟨eₛ⟩ := nonempty_iso_kernelTransform_shift A π π' 𝒦 a 0
  rw [add_zero] at eₛ
  suffices h : Nonempty (derivedTensorRightPullback A π ⋙
      (Functor.whiskeringRight _ _ _).obj
        (D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A (pullback π π') (𝒦⟦a⟧) ⋙
          R(pullback.snd π π')_![A]) ≅
      derivedTensorRightPullback A π' ⋙ (Functor.whiskeringLeft _ _ _).obj
        (D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A (pullback π π') (𝒦⟦a⟧) ⋙
          R(pullback.snd π π')_![A])) by
    obtain ⟨e⟩ := h
    let e₀ : kernelTransform A π π' (𝒦⟦a⟧) 0 ≅
        D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A (pullback π π') (𝒦⟦a⟧) ⋙
          R(pullback.snd π π')_![A] :=
      Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙
          derivedTensorRight A (pullback π π') (𝒦⟦a⟧) ⋙ R(pullback.snd π π')_![A])
        (shiftFunctorZero _ ℤ)
    let f := eₛ.symm ≪≫ e₀
    exact ⟨Functor.isoWhiskerLeft _ ((Functor.whiskeringRight _ _ _).mapIso f) ≪≫ e ≪≫
      Functor.isoWhiskerLeft _ ((Functor.whiskeringLeft _ _ _).mapIso f.symm)⟩
  generalize 𝒦⟦a⟧ = 𝒦
  set p₁ := pullback.fst π π'
  set p₂ := pullback.snd π π'
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (pullback π π').smallEtaleTopology A)
  -- `Lp₁^*(K ⊗ᴸ M) ≅ Lp₁^* K ⊗ᴸ Lp₁^* M`, naturally in `M` and `K`.
  let ι₁ := leftDerivedUpperStarIsoMapDerivedCategory A p₁
  let μ₁ : (-⊗ᴸ-(V)[A]).flip ⋙ (Functor.whiskeringRight _ _ _).obj L((p₁)^*[A]) ≅
      L((p₁)^*[A]) ⋙ (-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj L((p₁)^*[A]) :=
    (flipFunctor _ _ _).mapIso (leftDerivedUpperStarTensorNatIso A p₁)
  let μ : (-⊗ᴸ-(V)[A]).flip ⋙ (Functor.whiskeringRight _ _ _).obj D((p₁)^*[A]) ≅
      D((p₁)^*[A]) ⋙ (-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A]) :=
    Functor.isoWhiskerLeft _ ((Functor.whiskeringRight _ _ _).mapIso ι₁.symm) ≪≫ μ₁ ≪≫
      Functor.isoWhiskerRight ι₁ ((-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj L((p₁)^*[A])) ≪≫
      Functor.isoWhiskerLeft (D((p₁)^*[A]) ⋙ (-⊗ᴸ-(pullback π π')[A]).flip)
        ((Functor.whiskeringLeft _ _ _).mapIso ι₁)
  -- `p₁^* π^* ≅ p₂^* π'^*`.
  let c : D((π)^*[A]) ⋙ D((p₁)^*[A]) ≅ D((π')^*[A]) ⋙ D((p₂)^*[A]) :=
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A π).symm _ ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A p₁).symm ≪≫
      (leftDerivedUpperStarComp A p₁ π).symm ≪≫
      leftDerivedUpperStarComp A p₂ π' (p₁ ≫ π) pullback.condition ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A π') _ ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A p₂)
  -- `(X ⊗ᴸ M) ⊗ᴸ 𝒦 ≅ (X ⊗ᴸ 𝒦) ⊗ᴸ M`, naturally in `M` and `X`.
  let β : (-⊗ᴸ-(pullback π π')[A]).flip ⋙ (Functor.whiskeringRight _ _ _).obj
        (derivedTensorRight A (pullback π π') 𝒦) ≅
      (-⊗ᴸ-(pullback π π')[A]).flip ⋙ (Functor.whiskeringLeft _ _ _).obj
        (derivedTensorRight A (pullback π π') 𝒦) :=
    NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun X ↦
      α_ X M 𝒦 ≪≫ whiskerLeftIso X (β_ M 𝒦) ≪≫ (α_ X 𝒦 M).symm) (fun f ↦ by
        dsimp [derivedTensor, derivedTensorRight]
        simp only [whiskerLeftIso_hom, Category.assoc]
        rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
          associator_inv_naturality_left])) (fun g ↦ by
        ext X
        change (X ◁ g) ▷ 𝒦 ≫ (α_ X _ 𝒦).hom ≫ X ◁ (β_ _ 𝒦).hom ≫ (α_ X 𝒦 _).inv =
          ((α_ X _ 𝒦).hom ≫ X ◁ (β_ _ 𝒦).hom ≫ (α_ X 𝒦 _).inv) ≫ (X ⊗ 𝒦) ◁ g
        rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
          BraidedCategory.braiding_naturality_left, whiskerLeft_comp_assoc, Category.assoc,
          Category.assoc, associator_inv_naturality_right])
  -- The projection formula `Rp₂,!(X ⊗ᴸ p₂^* L) ≅ Rp₂,! X ⊗ᴸ L`.
  let ρ : D((p₂)^*[A]) ⋙ (-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringRight _ _ _).obj R(p₂)_![A] ≅
      (-⊗ᴸ-(V')[A]).flip ⋙ (Functor.whiskeringLeft _ _ _).obj R(p₂)_![A] :=
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A p₂).symm _ ≪≫
      (flipFunctor _ _ _).mapIso (asIso (projectionMap A p₂)).symm
  let T𝒦 := derivedTensorRight A (pullback π π') 𝒦
  let s₁ : derivedTensorRightPullback A π ⋙ (Functor.whiskeringRight _ _ _).obj
        (D((p₁)^*[A]) ⋙ T𝒦 ⋙ R(p₂)_![A]) ≅
      D((π)^*[A]) ⋙ (D((p₁)^*[A]) ⋙ (-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A])) ⋙
          (Functor.whiskeringRight _ _ _).obj (T𝒦 ⋙ R(p₂)_![A]) :=
    Functor.isoWhiskerLeft D((π)^*[A])
      (Functor.isoWhiskerRight μ ((Functor.whiskeringRight _ _ _).obj (T𝒦 ⋙ R(p₂)_![A])))
  let s₂ : D((π)^*[A]) ⋙ (D((p₁)^*[A]) ⋙ (-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A])) ⋙
          (Functor.whiskeringRight _ _ _).obj (T𝒦 ⋙ R(p₂)_![A]) ≅
      (D((π')^*[A]) ⋙ D((p₂)^*[A])) ⋙ ((-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringRight _ _ _).obj T𝒦) ⋙
          (Functor.whiskeringRight _ _ _).obj R(p₂)_![A] ⋙
            (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A]) :=
    Functor.isoWhiskerRight c ((-⊗ᴸ-(pullback π π')[A]).flip ⋙
      (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A]) ⋙
        (Functor.whiskeringRight _ _ _).obj (T𝒦 ⋙ R(p₂)_![A]))
  let s₃ : (D((π')^*[A]) ⋙ D((p₂)^*[A])) ⋙ ((-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringRight _ _ _).obj T𝒦) ⋙
          (Functor.whiskeringRight _ _ _).obj R(p₂)_![A] ⋙
            (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A]) ≅
      (D((π')^*[A]) ⋙ D((p₂)^*[A])) ⋙ ((-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj T𝒦) ⋙
          (Functor.whiskeringRight _ _ _).obj R(p₂)_![A] ⋙
            (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A]) :=
    Functor.isoWhiskerLeft (D((π')^*[A]) ⋙ D((p₂)^*[A])) (Functor.isoWhiskerRight β
      ((Functor.whiskeringRight _ _ _).obj R(p₂)_![A] ⋙
        (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A])))
  let s₄ : D((π')^*[A]) ⋙ (D((p₂)^*[A]) ⋙ (-⊗ᴸ-(pullback π π')[A]).flip ⋙
        (Functor.whiskeringRight _ _ _).obj R(p₂)_![A]) ⋙
          (Functor.whiskeringLeft _ _ _).obj T𝒦 ⋙
            (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A]) ≅
      D((π')^*[A]) ⋙ ((-⊗ᴸ-(V')[A]).flip ⋙ (Functor.whiskeringLeft _ _ _).obj R(p₂)_![A]) ⋙
          (Functor.whiskeringLeft _ _ _).obj T𝒦 ⋙
            (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A]) :=
    Functor.isoWhiskerLeft D((π')^*[A]) (Functor.isoWhiskerRight ρ
      ((Functor.whiskeringLeft _ _ _).obj T𝒦 ⋙ (Functor.whiskeringLeft _ _ _).obj D((p₁)^*[A])))
  exact ⟨s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄⟩

end General

end AlgebraicGeometry.Etale
