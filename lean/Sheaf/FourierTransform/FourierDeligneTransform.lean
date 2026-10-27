/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.FourierTransform.KernelNatCastEqZero
public import Sheaf.Paper.CommonStageFourierTransform
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# The Fourier–Deligne transform, including empty fiber products

Source: main-20261015 blueprint, `sec-fourier-transform/sk-def-ft/_section.md`
and `def-fd-transform.md` (blueprint: sk-def-ft).

The transform uses the prime-field kernel, placed in degree zero, and the specified
compactification. Its construction also covers empty fiber products, where the condition
`p = 0` in global sections holds but a `CharP` assumption would exclude the case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The Fourier–Deligne transform `K ↦ Rp₂,!(p₁^* K ⊗ᴸ K_psi[0])[r]`, computed with
one chosen compactification `c` of the second projection. The first factor is the functor
on unbounded derived categories induced by the exact inverse image of module sheaves.
The second is the existing derived tensor with the prime-field Artin–Schreier kernel
placed in degree zero. The third is `D(c.i_!) ⋙ R(c.g_*)`, and the last is the usual
cohomological shift, with degree `i` term `C^(i+r)` and differential `(-1)^r d`.

On a morphism `a`, this composite applies `p₁^*`, tensors with the identity of the kernel,
applies the compact-support direct image, and shifts by `r`; no object-only construction
or arbitrary choice of a map is used. The same definition with `Ψ⁻¹` gives the transform
with the inverse character. For a vector bundle and its dual, use their evaluation pairing
and take `r` equal to the rank (Laumon's normalization). On the affine line, use `b = x ξ`
and `r = 1`. No finiteness condition on the coefficients or nontriviality of `Ψ` is needed,
and the open immersion in `c` need not be quasi-compact.

Source: main-20261015 blueprint, `sec-fourier-transform/sk-def-ft/def-fd-transform.md`
and `sk-def-ft/_section.md` (blueprint: sk-def-ft). -/
noncomputable def fourierTransformOfNatCastEqZero
    (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    (h : (p : Γ(pullback π π', ⊤)) = 0)
    (c : Compactification (pullback.snd π π')) (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  D((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
    derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
      ((DerivedCategory.singleFunctor _ 0).obj (fourierKernelOfNatCastEqZero Λ π π' h Ψ b)) ⋙
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ⋙ shiftFunctor _ r

/-- The Fourier–Deligne transform `K ↦ Rp₂,!(p₁^* K ⊗ᴸ K_psi)[r]`, with the
prime-field Fourier kernel in degree zero and `Rp₂,!` computed from the chosen
compactification `c`. This abbreviation uses the detailed construction verbatim,
on objects and morphisms, with no further conditions. In the vector-bundle application,
use evaluation as `b` and the rank as `r`; on the affine line take `b = x ξ` and `r = 1`.
Replacing `Ψ` by `Ψ⁻¹` gives the inverse-character transform.

Source: main-20261015 blueprint, `sec-fourier-transform/sk-def-ft/_section.md`
(blueprint: sk-def-ft). -/
noncomputable abbrev fourierDeligneTransform
    (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    (h : (p : Γ(pullback π π', ⊤)) = 0)
    (c : Compactification (pullback.snd π π')) (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fourierTransformOfNatCastEqZero Λ π π' h c Ψ b r

end AlgebraicGeometry.Etale
