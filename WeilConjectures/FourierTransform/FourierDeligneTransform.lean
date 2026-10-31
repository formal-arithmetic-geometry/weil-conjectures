/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.KernelNatCastEqZero
public import WeilConjectures.AlgebraicGeometry.CommonStageFourierTransform

/-! # The Fourier–Deligne transform with a chosen compactification

Source: the accepted DAG statement sk-def-ft; current blueprint,
sec-fourier-transform/sk-thm-inversion/def-fd-transform.md, torsion-coefficient formula
(blueprint: sk-def-ft).

This module supplies the ordinary étale construction specified by the accepted node.
The condensed pro-étale transform in the pending blueprint update has different coefficient
objects; it is not substituted for this ordinary étale functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The composite `D(p₁^*)`, tensor with the recorded Fourier kernel in degree zero,
`Rp₂,!` for the supplied compactification, and cohomological shift by `r`.
The characteristic condition only requires `p = 0` in global sections, retaining
empty fibre products. The action on morphisms is the composite of these functors.
For a bundle and its dual, use the evaluation function for `b` and its rank for `r`;
on the affine line take `b(x,xi) = x * xi` and `r = 1`. Replacing `Ψ` by `Ψ⁻¹`
defines the inverse-character transform by the same formula.

Source: accepted sk-def-ft, defining formula and all specializations; current blueprint,
sec-fourier-transform/sk-thm-inversion/def-fd-transform.md, torsion-coefficient formula
(blueprint: sk-def-ft). -/
def fourierTransformOfNatCastEqZero (Λ : Type (u + 1)) [CommRing Λ]
    {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)] {S V V' : Scheme.{u}}
    (π : V ⟶ S) (π' : V' ⟶ S) (h : (p : Γ(pullback π π', ⊤)) = 0)
    (c : Compactification (pullback.snd π π')) (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  D((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
    derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
      ((DerivedCategory.singleFunctor _ 0).obj (fourierKernelOfNatCastEqZero Λ π π' h Ψ b)) ⋙
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ⋙ shiftFunctor _ r

/-- The Fourier–Deligne transform with its kernel in degree zero and its normalization
shift supplied explicitly. This is the preceding composite, on both objects and morphisms.
Source: accepted sk-def-ft, defining formula; current blueprint,
sec-fourier-transform/sk-thm-inversion/def-fd-transform.md, torsion-coefficient formula
(blueprint: sk-def-ft). -/
abbrev fourierDeligneTransform (Λ : Type (u + 1)) [CommRing Λ]
    {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)] {S V V' : Scheme.{u}}
    (π : V ⟶ S) (π' : V' ⟶ S) (h : (p : Γ(pullback π π', ⊤)) = 0)
    (c : Compactification (pullback.snd π π')) (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf V'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fourierTransformOfNatCastEqZero Λ π π' h c Ψ b r

end AlgebraicGeometry.Etale
