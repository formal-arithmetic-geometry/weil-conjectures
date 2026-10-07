/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!

# Kernel transforms on the pro-étale site

Let `π : V ⟶ S` and `π' : V' ⟶ S` be two `S`-schemes and let `𝒦` be a complex of pro-étale
sheaves on `V ×_S V'`, the *kernel*. The *kernel transform* attached to `𝒦` and a shift `a : ℤ`
is

`Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]`,

`p₁, p₂` being the two projections of `V ×_S V'`, now with the pro-étale six functors. This is
the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform`; the
pro-étale Fourier–Deligne transform of `WeilConjectures.FourierTransform.ProEtale` is the
kernel transform of the Fourier kernel.

The constructions are made for any coefficient category `A` on which the pro-étale six
functors are built: a Grothendieck abelian, closed symmetric monoidal category with functorial
flat resolutions.

## Main definitions

- `AlgebraicGeometry.ProEtale.kernelTransform`: the kernel transform `Φ_𝒦` with shift `a`.
- `AlgebraicGeometry.ProEtale.kernelConvolution`: the convolution
  `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`.

## Main statements

- `AlgebraicGeometry.ProEtale.nonempty_iso_kernelTransform_shift`: shifting the kernel shifts
  the kernel transform.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

## Implementation notes

There is no pro-étale `derivedTensorRight`; tensoring on the right with `𝒦` is
`(derivedTensor A X).flip.obj 𝒦`.

TODO: prove `AlgebraicGeometry.ProEtale.nonempty_iso_kernelTransform_shift`. As on the étale
side it is formal once the pro-étale six functors carry `Functor.CommShift` instances and the
shift isomorphism of the derived tensor product in its second variable is natural in the
first; neither is in the repository yet.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- The *kernel transform* `Φ_𝒦(K) = Rp₂,!(p₁^* K ⊗ᴸ 𝒦)[a]` attached to a kernel
`𝒦 ∈ D((V ×_S V')_proét)` and a shift `a : ℤ`:

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
along `p₂` and shifted by `a`, all with the pro-étale six functors.
(sketch blueprint: `sk-def-kernel`, pro-étale realisation) -/
noncomputable def kernelTransform [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback π π')) A)) (a : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology V) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology V') A) :=
  D((pullback.fst π π')^*[A]) ⋙ (derivedTensor A (pullback π π')).flip.obj 𝒦 ⋙
    R(pullback.snd π π')_![A] ⋙ shiftFunctor _ a

/-- Shifting the kernel shifts the kernel transform: the kernel transform of `𝒦[a]` with shift
`c` is the kernel transform of `𝒦` with shift `a + c`.

Class: general; decided by formal six-functor yoga (shifts commute with the derived tensor
product and `Rf_!`), so it holds at every coefficient category `A`.
(sketch blueprint: `sk-def-kernel`, pro-étale realisation) -/
theorem nonempty_iso_kernelTransform_shift [HasCompactification (pullback.snd π π')]
    (𝒦 : DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback π π')) A)) (a c : ℤ) :
    Nonempty (kernelTransform A π π' ((shiftFunctor _ a).obj 𝒦) c ≅
        kernelTransform A π π' 𝒦 (a + c)) :=
  sorry

/-- The convolution `𝒦' ∗ 𝒦 = r₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')` of a kernel `𝒦` on `V ×_S V'`
with a kernel `𝒦'` on `V' ×_S V''`, a kernel on `V ×_S V''`, with the pro-étale six functors.

The triple product `V ×_S V' ×_S V''` is realised as `(V ×_S V') ×_{V'} (V' ×_S V'')`, whose
two projections are `r₁₂` and `r₂₃`; `r₁₃` is
`CategoryTheory.Limits.pullback.tripleProj₁₃`. `𝒦` is pulled back along `r₁₂`, `𝒦'` along
`r₂₃`, the two are tensored, and the result is pushed forward with compact support along
`r₁₃`. (sketch blueprint: `sk-lem-kernel-composition`, pro-étale realisation) -/
noncomputable def kernelConvolution
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    (𝒦 : DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback π π')) A))
    (𝒦' : DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback π' π'')) A)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback π π'')) A) :=
  (R(pullback.tripleProj₁₃ π π' π'')_![A]).obj
    (((derivedTensor A (pullback (pullback.snd π π') (pullback.fst π' π''))).obj
        ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦)).obj
      ((D((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦'))

end AlgebraicGeometry.ProEtale
