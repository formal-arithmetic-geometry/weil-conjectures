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

- `AlgebraicGeometry.Etale.isTriangulated_kernelTransform`: the kernel transform is a
  triangulated functor, being a composite of four triangulated functors.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_shift`: shifting the kernel shifts the
  kernel transform.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`: composition of kernel
  transforms, at finite coefficients.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp_of_nonempty_iso`:
  composition of kernel transforms at a general coefficient category, given the composition
  law of `Rf_!`, compact-support base change and the projection formula.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`: the kernel transform of a
  kernel supported on the diagonal is a tensor product.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor`: kernel transforms are linear
  over the base, given the projection formula for the second projection.

## Implementation notes

The statements only assert that an isomorphism *exists*. Showing that the composition of
kernel transforms is compatible with the associativity of convolution will need specific,
coherent isomorphisms, which `Classical.choice` cannot provide.

`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp_of_nonempty_iso` proves the
composition law at a general coefficient category `A`, on the triple product, from
compact-support base change along the cartesian square with sides `r₁₂`, `r₂₃`, `p₂` and `q₁`
and from the projection formula for `r₂₃` and `r₁₃`; it also uses the composition law of `Rf_!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`) and the symmetry of
`⊗ᴸ`. Working over a general `A` keeps the kernel from comparing the
monoidal structures on `D(X_ét)` at `A = ModuleCat Λ` (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).
`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp` specialises it to a finite ring
`Λ`, where base change is `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`
and the projection formula, on the unbounded derived categories, is
`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`. Base change needs `r₂₃`, a base
change of `π`, to be quasi-compact, so the finiteness hypotheses are put on `π` and `π'`. The
composition law is applied to `r₁₃ ≫ s₂ = r₂₃ ≫ q₂`, `s₂ : V ×_S V'' ⟶ V''` being the second
projection. Instance search does not give this composite a compactification (a composite of
compactifiable morphisms is compactifiable by Nagata's theorem, which needs a quasi-compact
and quasi-separated base), so it is a hypothesis.

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

/-- The kernel transform commutes with shifts, as the composite of `D(p₁^*)`, `- ⊗ᴸ 𝒦`, `Rp₂,!`
and the shift by `a`, each of which does. -/
noncomputable instance commShiftKernelTransform [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a : ℤ) :
    (kernelTransform A π π' 𝒦 a).CommShift ℤ :=
  inferInstanceAs ((D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A (pullback π π') 𝒦 ⋙
    R(pullback.snd π π')_![A] ⋙ shiftFunctor _ a).CommShift ℤ)

/-- The kernel transform is a triangulated functor: the pullback `D(p₁^*)`, the derived tensor
product `- ⊗ᴸ 𝒦`, the compact-support direct image `Rp₂,!` and the shift by `a` are
triangulated.

Class: general; it holds at every coefficient category `A`. -/
instance isTriangulated_kernelTransform [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A)) (a : ℤ) :
    (kernelTransform A π π' 𝒦 a).IsTriangulated :=
  inferInstanceAs ((D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A (pullback π π') 𝒦 ⋙
    R(pullback.snd π π')_![A] ⋙ shiftFunctor _ a).IsTriangulated)

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

section Composition

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- Composition of kernel transforms, at a general coefficient category `A`, from the inputs of
the six-functor formalism it uses: the composition law of `Rf_!` (`hcomp`, which holds for
torsion coefficients, `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`),
compact-support
base change (`hbc`) along the cartesian square

```
    V ×ₛ V' ×ₛ V'' ──r₁₂──▶ V ×ₛ V'
          │                    │
       r₂₃│                    │p₂
          ▼                    ▼
      V' ×ₛ V'' ─────q₁─────▶ V'
```

and the projection formula for `r₂₃` and `r₁₃` (`hpf₂₃`, `hpf₁₃`). Then the composite of the
kernel transform of `𝒦` with shift `a` and the kernel transform of `𝒦'` with shift `c` is the
kernel transform of the convolution `𝒦' ∗ 𝒦` with shift `a + c`.

Base change gives `q₁^* Rp₂,! ≅ Rr₂₃,! r₁₂^*`, the projection formula for `r₂₃` moves
`r₂₃^* 𝒦'` inside, and the composition law turns the composite into
`R(r₁₃ ≫ s₂)_!(r₁^* K ⊗ᴸ r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`, with `r₁ = r₁₂ ≫ p₁ = r₁₃ ≫ s₁` and `s₁`,
`s₂` the projections of `V ×ₛ V''`. The projection formula for `r₁₃`, the symmetry of `⊗ᴸ`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`) and the composition law turn the
kernel transform of `𝒦' ∗ 𝒦` into the same expression.
(sketch blueprint: `sk-lem-kernel-composition`; blueprint: `lem-fd-kernel-composition`) -/
theorem nonempty_iso_kernelTransform_comp_of_nonempty_iso
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    [HasCompactification (pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'')]
    (hcomp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f]
      [HasCompactification g] [HasCompactification (f ≫ g)],
      Nonempty (R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]))
    (hbc : Nonempty (R(pullback.snd π π')_![A] ⋙ L((pullback.fst π' π'')^*[A]) ≅
      L((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
        R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A]))
    (hpf₂₃ : ∀ L, Nonempty
      (R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] ⋙
          derivedTensorRight A _ L ≅
        derivedTensorRight A _
            ((L((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj L) ⋙
          R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A]))
    (hpf₁₃ : ∀ K, Nonempty
      ((derivedTensor A _).obj ((R(pullback.tripleProj₁₃ π π' π'')_![A]).obj K) ≅
        L((pullback.tripleProj₁₃ π π' π'')^*[A]) ⋙ (derivedTensor A _).obj K ⋙
          R(pullback.tripleProj₁₃ π π' π'')_![A]))
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology A))
    (a c : ℤ) :
    Nonempty (kernelTransform A π π' 𝒦 a ⋙ kernelTransform A π' π'' 𝒦' c ≅
        kernelTransform A π π'' (kernelConvolution A π π' π'' 𝒦 𝒦') (a + c)) := by
  -- the derived pullbacks `Lf^*` and `D(f^*)` agree
  let ι {X Y : Scheme.{u}} (f : X ⟶ Y) := leftDerivedUpperStarIsoMapDerivedCategory A f
  -- tensoring with isomorphic complexes
  let τ {X : Scheme.{u}} {N N' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : N ≅ N') :
      derivedTensorRight A X N ≅ derivedTensorRight A X N' :=
    (derivedTensor A X).flip.mapIso e
  have hcongr {X Y : Scheme.{u}} {f g : X ⟶ Y} [HasCompactification f]
      [HasCompactification g] (h : f = g) : Nonempty (R(f)_![A] ≅ R(g)_![A]) := by
    subst h
    exact ⟨Iso.refl _⟩
  have hc : pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'' =
      pullback.snd (pullback.snd π π') (pullback.fst π' π'') ≫ pullback.snd π' π'' :=
    pullback.tripleProj₁₃_snd _ _ _
  have : HasCompactification
      (pullback.snd (pullback.snd π π') (pullback.fst π' π'') ≫ pullback.snd π' π'') :=
    .of_eq hc
  -- the inputs from the six-functor formalism
  obtain ⟨β₁₃⟩ := nonempty_iso_derivedTensor_flip A (pullback π π'')
  obtain ⟨βP⟩ := nonempty_iso_derivedTensor_flip A
    (pullback (pullback.snd π π') (pullback.fst π' π''))
  obtain ⟨c₂₃⟩ := hcomp
    (pullback.snd (pullback.snd π π') (pullback.fst π' π'')) (pullback.snd π' π'')
  obtain ⟨c₁₃⟩ := hcomp (pullback.tripleProj₁₃ π π' π'') (pullback.snd π π'')
  obtain ⟨cc⟩ := hcongr hc
  obtain ⟨pf₂₃⟩ := hpf₂₃ 𝒦'
  obtain ⟨bc₀⟩ := hbc
  obtain ⟨pf₁₃⟩ := hpf₁₃
    ((derivedTensorRight A _ ((D((pullback.snd (pullback.snd π π')
      (pullback.fst π' π''))^*[A])).obj 𝒦')).obj
      ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦))
  -- compact-support base change `q₁^* Rp₂,! ≅ Rr₂₃,! r₁₂^*`
  let bc : R(pullback.snd π π')_![A] ⋙ D((pullback.fst π' π'')^*[A]) ≅
      D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
        R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] :=
    Functor.isoWhiskerLeft _ (ι _).symm ≪≫ bc₀ ≪≫ Functor.isoWhiskerRight (ι _) _
  -- `r₁₂^*` is monoidal
  let tp : derivedTensorRight A _ 𝒦 ⋙
        D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ≅
      D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
        derivedTensorRight A _
          ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦) :=
    Functor.isoWhiskerLeft _ (ι _).symm ≪≫
      derivedTensorRightCompLeftDerivedUpperStarIso A
        (pullback.fst (pullback.snd π π') (pullback.fst π' π'')) 𝒦 ≪≫
      Functor.isoWhiskerRight (ι (pullback.fst (pullback.snd π π') (pullback.fst π' π'')))
        (derivedTensorRight A _
          ((L((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦)) ≪≫
      Functor.isoWhiskerLeft _ (τ ((ι _).app 𝒦))
  -- the projection formula for `r₂₃`
  let pf : R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] ⋙
        derivedTensorRight A _ 𝒦' ≅
      derivedTensorRight A _
          ((D((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦') ⋙
        R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] :=
    pf₂₃ ≪≫ Functor.isoWhiskerRight (τ ((ι _).app 𝒦')) _
  -- `r₁₂ ≫ p₁ = r₁₃ ≫ s₁`
  let pc : D((pullback.fst π π')^*[A]) ⋙
        D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ≅
      D((pullback.fst π π'')^*[A]) ⋙ D((pullback.tripleProj₁₃ π π' π'')^*[A]) :=
    (Functor.isoWhiskerRight (ι _) _ ≪≫ Functor.isoWhiskerLeft _ (ι _)).symm ≪≫
      (leftDerivedUpperStarComp A _ _).symm ≪≫
      leftDerivedUpperStarComp A (pullback.tripleProj₁₃ π π' π'') (pullback.fst π π'') _
        (pullback.tripleProj₁₃_fst _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ι _) _ ≪≫ Functor.isoWhiskerLeft _ (ι _)
  -- the composite of the unshifted transforms
  let e : (D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A _ 𝒦 ⋙
        R(pullback.snd π π')_![A]) ⋙
      (D((pullback.fst π' π'')^*[A]) ⋙ derivedTensorRight A _ 𝒦' ⋙
        R(pullback.snd π' π'')_![A]) ≅
      D((pullback.fst π π'')^*[A]) ⋙
        derivedTensorRight A _ (kernelConvolution A π π' π'' 𝒦 𝒦') ⋙
        R(pullback.snd π π'')_![A] :=
    Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A _ 𝒦)
        (Functor.isoWhiskerRight bc (derivedTensorRight A _ 𝒦' ⋙
          R(pullback.snd π' π'')_![A])) ≪≫
      Functor.isoWhiskerLeft D((pullback.fst π π')^*[A])
        (Functor.isoWhiskerRight tp
          (R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] ⋙
            derivedTensorRight A _ 𝒦' ⋙ R(pullback.snd π' π'')_![A])) ≪≫
      Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙
          D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
          derivedTensorRight A _
            ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦))
        (Functor.isoWhiskerRight pf R(pullback.snd π' π'')_![A]) ≪≫
      Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙
          D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
          derivedTensorRight A _
            ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦) ⋙
          derivedTensorRight A _
            ((D((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦'))
        (c₂₃.symm ≪≫ cc.symm) ≪≫
      Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙
          D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]))
        (Functor.isoWhiskerRight (tensorRightTensor _ _).symm
          R(pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'')_![A]) ≪≫
      Functor.isoWhiskerRight pc _ ≪≫
      Functor.isoWhiskerLeft D((pullback.fst π π'')^*[A])
        (Functor.isoWhiskerRight (ι _).symm _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (βP.app _).symm _ ≪≫
            Functor.isoWhiskerLeft _ c₁₃) ≪≫
          Functor.isoWhiskerRight pf₁₃.symm R(pullback.snd π π'')_![A] ≪≫
          Functor.isoWhiskerRight (β₁₃.app _) R(pullback.snd π π'')_![A])
  -- moving the shifts to the end
  have : (derivedTensorRight A _ 𝒦').CommShift ℤ := commShiftDerivedTensorFlipObj A 𝒦'
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A _ 𝒦 ⋙
        R(pullback.snd π π')_![A])
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((D((pullback.fst π' π'')^*[A]) ⋙ derivedTensorRight A _ 𝒦' ⋙
          R(pullback.snd π' π'')_![A]).commShiftIso a) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (shiftFunctorAdd _ a c).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _⟩

end Composition

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
which need `[Finite Λ]`. The composition law of `Rf_!` is applied
to `r₁₃ ≫ s₂ = r₂₃ ≫ q₂`, `s₂ : V ×ₛ V'' ⟶ V''` being the second projection, which is why that
composite is assumed to admit a compactification.
(sketch blueprint: `sk-lem-kernel-composition`; blueprint: `lem-fd-kernel-composition`) -/
theorem nonempty_iso_kernelTransform_comp [Finite Λ]
    [LocallyOfFiniteType π] [QuasiCompact π] [LocallyOfFiniteType π'] [QuasiCompact π']
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    [HasCompactification (pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a c : ℤ) :
    Nonempty (kernelTransform (ModuleCat.{u + 1} Λ) π π' 𝒦 a ⋙
          kernelTransform (ModuleCat.{u + 1} Λ) π' π'' 𝒦' c ≅
        kernelTransform (ModuleCat.{u + 1} Λ) π π''
          (kernelConvolution (ModuleCat.{u + 1} Λ) π π' π'' 𝒦 𝒦') (a + c)) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (IsPullback.of_hasPullback (pullback.snd π π') (pullback.fst π' π''))
  nonempty_iso_kernelTransform_comp_of_nonempty_iso (ModuleCat.{u + 1} Λ) π π' π''
    (fun f g _ _ _ ↦ nonempty_iso_rightDerivedLowerShriek_comp Λ f g)
    ⟨asIso (rightDerivedLowerShriekBaseChangeMap _
      (IsPullback.of_hasPullback (pullback.snd π π') (pullback.fst π' π'')))⟩
    (fun L ↦ nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight _ _ L
      (fun K ↦ hasProjectionFormula_of_finite Λ _ K L))
    (fun K ↦ nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek _ _ K
      (fun L ↦ hasProjectionFormula_of_finite Λ _ K L)) 𝒦 𝒦' a c

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
