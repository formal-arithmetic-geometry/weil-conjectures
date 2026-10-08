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
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

/-!

# Kernel transforms

Let `π : V ⟶ S` and `π' : V' ⟶ S` be two `S`-schemes and let `𝒦` be a complex on
`V ×_S V'`, the *kernel*. The *kernel transform* (or integral transform) attached to `𝒦` and
a shift `a : ℤ` is

`Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]`,

`p₁, p₂` being the two projections of `V ×_S V'`. Kernel transforms compose: the composite
of the kernel transforms of `𝒦` and `𝒦'` is the kernel transform of the convolution
`𝒦' ∗ 𝒦`, with the shifts added. The Fourier–Deligne transform of
`WeilConjectures.FourierTransform.Defs` is the kernel transform of the Fourier kernel.

The constructions are made for any coefficient category `A` on which the étale six functors
are built: a Grothendieck abelian, closed symmetric monoidal category with functorial flat
resolutions.

## Main definitions

- `AlgebraicGeometry.Etale.kernelTransform`: the kernel transform `Φ_𝒦` with shift `a`.
- `AlgebraicGeometry.Etale.kernelConvolution`: the convolution
  `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_shift`: shifting the kernel shifts the
  kernel transform.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`: composition of kernel
  transforms.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`: the kernel transform of a
  kernel supported on the diagonal is a tensor product.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor`: kernel transforms are linear
  over the base, given the projection formula for the second projection.

## Implementation notes

The statements only assert that an isomorphism *exists*. Showing that the composition of
kernel transforms is compatible with the associativity of convolution will need specific,
coherent isomorphisms, which `Classical.choice` cannot provide.

`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp` is proved on the triple product by
compact-support base change along the cartesian square with sides `r₁₂`, `r₂₃`, `p₂` and
`q₁`, then the projection formula for `r₂₃` and `r₁₃` and the composition law of `Rf_!`. The
maps `p₂`, `q₂` and `r₁₃` are base changes of `π`, `π'` and `π'` respectively (`r₁₃` along
`V ×_S V'' ⟶ S`), so the finiteness hypotheses are put on `π` and `π'`: instance search does
not derive them for `CategoryTheory.Limits.pullback.tripleProj₁₃`. The statement is over the
whole unbounded derived categories, while the project's projection formula
`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerShriek` only covers a
bounded constructible complex and a complex of finite Tor amplitude. The unbounded form holds
for finite `Λ`: the projection map is an isomorphism for `j_!` of an open immersion formally,
and for a proper morphism because its direct image then has finite cohomological dimension.
That argument does not use the exponent of `Λ`, and the classical projection formula for
`Rf_!` holds for all torsion coefficients (SGA 4 XVII 5.2.9); `[HasInvertibleExponent Λ S]` is
inherited from the project's projection formula.

`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal` is the projection formula for
the closed immersion `Δ`, followed by `Δ_* = Δ_!` and `Δ ≫ p₂ = 𝟙`. Since `R(f)_!` is computed
with a chosen compactification, the last two steps use independence of the compactification
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), which needs `π` quasi-compact and
torsion coefficients.

TODO: prove `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_shift`. It is formal once the
shift isomorphism of the derived tensor product in its second variable is natural in the first,
`derivedTensorRight A X (𝒦⟦a⟧) ≅ derivedTensorRight A X 𝒦 ⋙ shiftFunctor _ a`. The instances
`AlgebraicGeometry.Etale.commShiftDerivedTensorObj` and
`AlgebraicGeometry.Etale.commShiftDerivedTensorFlipObj`, and
`AlgebraicGeometry.Etale.derivedTensorShiftIso` built from them, only give naturality in the
shifted variable.

`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor` moves the shift into the kernel
before applying the projection formula, so that it never has to commute a shift with
`- ⊗ᴸ π'^* N` naturally in `N` (which the instances above do not provide). It uses some braiding
of `D((V ×_S V')_ét)` (`DerivedCategory.nonempty_braidedCategory`); since only the existence of
an isomorphism is asserted, the choice does not matter.

TODO: upgrade the statements back to `Iso` constructions once they can be built.

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

/-- The *kernel transform* `Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]` attached to a kernel
`𝒦 ∈ D((V ×_S V')_ét)` and a shift `a : ℤ`:

```
              V ×ₛ V'
             ╱       ╲
          p₁╱         ╲p₂
           ▼           ▼
           V            V'
            ╲          ╱
            π╲        ╱π'
              ▼      ▼
                 S
```

`K` is pulled back along `p₁`, tensored with `𝒦`, pushed forward with compact support
along `p₂` and shifted by `a`. -/
noncomputable def kernelTransform [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology A) :=
  D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A (pullback π π') 𝒦 ⋙
    R(pullback.snd π π')_![A] ⋙ shiftFunctor _ a

/-- Shifting the kernel shifts the kernel transform: the kernel transform of `𝒦[a]` with shift
`c` is the kernel transform of `𝒦` with shift `a + c`.

Class: general; decided by formal six-functor yoga (shifts commute with the derived tensor
product and `Rf_!`), so it holds at every coefficient category `A`. -/
theorem nonempty_iso_kernelTransform_shift [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a c : ℤ) :
    Nonempty (kernelTransform A π π' ((shiftFunctor _ a).obj 𝒦) c ≅
        kernelTransform A π π' 𝒦 (a + c)) :=
  sorry

/-- The convolution `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')` of a kernel `𝒦` on `V ×_S V'`
with a kernel `𝒦'` on `V' ×_S V''`, a kernel on `V ×_S V''`.

The triple product `V ×_S V' ×_S V''` is realised as `(V ×_S V') ×_{V'} (V' ×_S V'')`, whose
two projections are `r₁₂` and `r₂₃`; `r₁₃` is
`CategoryTheory.Limits.pullback.tripleProj₁₃`:

```
                       𝒦
    V ×ₛ V' ×ₛ V'' ──r₁₂──▶ V ×ₛ V'
           │ ╲
           │   ╲ r₁₃
        r₂₃│     ╲
           ▼       ▶ V ×ₛ V''
      V' ×ₛ V''
           𝒦'
```

`𝒦` is pulled back along `r₁₂`, `𝒦'` along `r₂₃`, the two are tensored, and the result is
pushed forward with compact support along `r₁₃`. -/
noncomputable def kernelConvolution
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology A)) :
    DerivedCategory (Sheaf (pullback π π'').smallEtaleTopology A) :=
  (R(pullback.tripleProj₁₃ π π' π'')_![A]).obj
    ((derivedTensorRight A (pullback (pullback.snd π π') (pullback.fst π' π''))
        ((D((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦')).obj
      ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦))

set_option maxHeartbeats 4000000 in
-- The kernel compares the stored body of `kernelConvolution`, whose proof arguments are
-- auxiliary lemmas, with the elaborated right-hand side; this takes a few minutes, done once here.
/-- The convolution unfolded: `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`. Rewriting with this lemma
avoids unfolding `AlgebraicGeometry.Etale.kernelConvolution` at specific coefficients, which is
much slower in the kernel. -/
theorem kernelConvolution_eq [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology A)) :
    kernelConvolution A π π' π'' 𝒦 𝒦' =
      (R(pullback.tripleProj₁₃ π π' π'')_![A]).obj
        ((derivedTensorRight A (pullback (pullback.snd π π') (pullback.fst π' π''))
            ((D((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦')).obj
          ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦)) :=
  rfl

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

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- The composite of the kernel transform of `𝒦` with shift `a` and the kernel transform of
`𝒦'` with shift `c` is the kernel transform of the convolution `𝒦' ∗ 𝒦` with shift `a + c`.
The composite is read on the triple product, in the cartesian square

```
    V ×ₛ V' ×ₛ V'' ──r₁₂──▶ V ×ₛ V'
          │                    │
       r₂₃│                    │p₂
          ▼                    ▼
      V' ×ₛ V'' ─────q₁─────▶ V'
```

with `r₁₃ : V ×ₛ V' ×ₛ V'' ⟶ V ×ₛ V''` the remaining projection and
`q₂ : V' ×ₛ V'' ⟶ V''` the second projection.

Class: torsion; decided by compact-support base change and the projection formula for `Rf_!`,
which need `[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `sk-lem-kernel-composition`) -/
theorem nonempty_iso_kernelTransform_comp [Finite Λ] [HasInvertibleExponent Λ S]
    [LocallyOfFiniteType π] [QuasiCompact π] [LocallyOfFiniteType π'] [QuasiCompact π']
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a c : ℤ) :
    Nonempty (kernelTransform (ModuleCat.{u + 1} Λ) π π' 𝒦 a ⋙
          kernelTransform (ModuleCat.{u + 1} Λ) π' π'' 𝒦' c ≅
        kernelTransform (ModuleCat.{u + 1} Λ) π π''
          (kernelConvolution (ModuleCat.{u + 1} Λ) π π' π'' 𝒦 𝒦') (a + c)) :=
  sorry

/-- The kernel transform of a kernel `Δ_* N` supported on the diagonal of `V ×_S V`, with
shift `0`, is tensoring with `N`:

`Rp₂,!(p₁^* K ⊗ᴸ Δ_* N) ≅ K ⊗ᴸ N`,

naturally in `K`, where `Δ` is the diagonal of the separated morphism `π`:

```
             Δ
        V ──────▶ V ×ₛ V ──p₂──▶ V
         ╲          │
          ╲ 𝟙       │p₁
           ╲        ▼
            ──────▶ V
```

with `Δ ≫ p₁ = 𝟙 = Δ ≫ p₂`. For `N = Λ` this says that `Δ_* Λ` is the identity kernel.

Class: compactification-dependent; decided by independence of the compactification. The
blueprint proof is formal: the projection formula for the closed immersion `Δ`, `Δ_* = Δ_!`
and `Δ ≫ p₂ = 𝟙`. Here `[Finite Λ]` enters solely through independence of the
compactification (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), since `R(f)_!` is
computed with a chosen compactification. The same comparison is why `[QuasiCompact π]` is
assumed: `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso` compares compactifications of a
quasi-compact morphism, here of `p₂` and of `Δ ≫ p₂ = 𝟙`; `p₂` is quasi-compact as a base
change of `π`. `[IsSeparated π]` makes `Δ` a closed immersion.
(sketch blueprint: `sk-thm-inversion`, proof) -/
theorem nonempty_iso_kernelTransform_diagonal [Finite Λ] [IsSeparated π] [QuasiCompact π]
    [HasCompactification (pullback.snd π π)]
    (N : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (kernelTransform (ModuleCat.{u + 1} Λ) π π
          ((R((pullback.diagonal π)_*[ModuleCat.{u + 1} Λ])).obj N) 0 ≅
        derivedTensorRight (ModuleCat.{u + 1} Λ) V N) :=
  sorry

end AlgebraicGeometry.Etale
