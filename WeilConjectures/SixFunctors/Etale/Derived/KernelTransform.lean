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
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor
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
  triangulated functor.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_shift`: shifting the kernel shifts the
  kernel transform.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`: composition of kernel
  transforms, at finite coefficients.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp_of_nonempty_iso`:
  composition of kernel transforms at a general coefficient category, given the composition
  law of `Rf_!`, compact-support base change and the projection formula.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`: the kernel transform of a
  kernel supported on the diagonal is a tensor product.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor_of_hasProjectionFormula`: kernel
  transforms are linear over the base on full subcategories where the projection formula for
  the second projection holds.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor`: kernel transforms are linear
  over the base, given the projection formula for the second projection.

## Implementation details

The statements only assert that an isomorphism *exists*. Showing that the composition of
kernel transforms is compatible with the associativity of convolution will need specific,
coherent isomorphisms, which `Classical.choice` cannot provide.

The composition law is proved at a general coefficient category `A`, which avoids comparing the
monoidal structures on `D(X_ét)` at `A = ModuleCat Λ`, and then specialised to a finite ring `Λ`.
Base change needs `r₂₃`, a base change of `π`, to be quasi-compact, so the finiteness hypotheses
are put on `π` and `π'`. Instance search does not give the composite `r₁₃ ≫ s₂` a
compactification, so it is a hypothesis.

TODO: upgrade the statements back to `Iso` constructions once they can be built.

This module only imports its parts: the definitions are in
`WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs`, linearity over the base in
`WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor`, the composition law in
`WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` and the statements at
finite coefficients in `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite`.
-/
