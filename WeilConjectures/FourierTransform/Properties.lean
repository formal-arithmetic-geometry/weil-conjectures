/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FourierTransform.Defs

/-!

# Formal properties of the Fourier–Deligne transform

The Fourier–Deligne transform of `WeilConjectures.FourierTransform.Defs` is a kernel
transform, and the three properties collected here are the ones a kernel transform always
has: its stalks are integrals of the input against the kernel, it commutes with base change
on `S`, and it is linear over the base, in the sense that it turns tensoring with a complex
pulled back from `S` into tensoring with the same complex pulled back to the dual.

## Main definitions

- `AlgebraicGeometry.Etale.pairingAt`: the function `x ↦ b(x, ξ)` attached to a section `ξ`
  of `V' ⟶ S`.
- `AlgebraicGeometry.Etale.pairingBaseChange`: the base change of the pairing.

## Main statements

- `AlgebraicGeometry.Etale.fourierTransformStalkIso`: the stalk of `FT_ψ(K)` at a section
  `ξ` of `V' ⟶ S` is the compactly supported cohomology of `K ⊗ᴸ ℒ_{ψ(b(x, ξ))}`, shifted
  by `r`.
- `AlgebraicGeometry.Etale.fourierTransformBaseChangeIso`: the transform commutes with base
  change along `S' ⟶ S`.
- `AlgebraicGeometry.Etale.fourierTransformTensorIso`: the transform is linear over the
  base.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

section Stalk

/-- The pairing `b` evaluated at a section `ξ` of `V' ⟶ S`: the global function
`x ↦ b(x, ξ)` on `V`, the pullback of `b` along the graph `V ⟶ V ×_S V'` of `ξ`. -/
noncomputable def pairingAt (b : Γ(pullback π π', ⊤)) (ξ : S ⟶ V') (hξ : ξ ≫ π' = 𝟙 S) :
    Γ(V, ⊤) :=
  (pullback.lift (𝟙 V) (π ≫ ξ) (by simp [hξ])).appTop b

/-- Blueprint `sk-prop-stalk`: P3: the stalks are fibre integrals.

At a section `ξ` of `V' ⟶ S` — a geometric point of the dual when `S` is the spectrum of an
algebraically closed field — the stalk of the Fourier–Deligne transform is the compactly
supported cohomology of the input twisted by the Artin–Schreier sheaf of the function
`x ↦ b(x, ξ)`, shifted by the relative dimension:

`FT_ψ(K)_ξ ≅ RΓ_c(V, K ⊗ᴸ ℒ_{ψ(b(x, ξ))})[r]`. -/
noncomputable def fourierTransformStalkIso [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')] [CharP Γ(V, ⊤) p] [HasCompactification π]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ)
    (ξ : S ⟶ V') (hξ : ξ ≫ π' = 𝟙 S)
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (D((ξ)^*[ModuleCat.{u + 1} Λ])).obj ((fourierTransform Λ π π' Ψ b r).obj K) ≅
      (shiftFunctor _ r).obj ((R(π)_![ModuleCat.{u + 1} Λ]).obj
        ((artinSchreierTwist Λ V Ψ (pairingAt π π' b ξ hξ)).obj K)) :=
  sorry

end Stalk

section BaseChange

/-- The base change of the pairing `b` along `g : S' ⟶ S`: its pullback to `W ×_{S'} W'`,
where `W = V ×_S S'` and `W' = V' ×_S S'`. -/
noncomputable def pairingBaseChange (b : Γ(pullback π π', ⊤)) {S' W W' : Scheme.{u}}
    (g : S' ⟶ S) (ρ : W ⟶ S') (ρ' : W' ⟶ S') (u : W ⟶ V) (u' : W' ⟶ V')
    (hu : u ≫ π = ρ ≫ g) (hu' : u' ≫ π' = ρ' ≫ g) :
    Γ(pullback ρ ρ', ⊤) :=
  (pullback.map ρ ρ' π π' u u' g hu.symm hu'.symm).appTop b

/-- Blueprint `sk-prop-base-change`: P5: base change.

For a morphism `g : S' ⟶ S` and the base changes `W = V ×_S S'`, `W' = V' ×_S S'` with the
pulled back pairing, the Fourier–Deligne transform commutes with the pullbacks
`u^* : D(V_ét) ⥤ D(W_ét)` and `u'^* : D(V'_ét) ⥤ D(W'_ét)`:

`FT_ψ(u^* K) ≅ u'^* FT_ψ(K)`. -/
noncomputable def fourierTransformBaseChangeIso [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ) {S' W W' : Scheme.{u}}
    (g : S' ⟶ S) (ρ : W ⟶ S') (ρ' : W' ⟶ S') (u : W ⟶ V) (u' : W' ⟶ V')
    (hu : u ≫ π = ρ ≫ g) (hu' : u' ≫ π' = ρ' ≫ g)
    [CharP Γ(pullback ρ ρ', ⊤) p] [HasCompactification (pullback.snd ρ ρ')]
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (fourierTransform Λ ρ ρ' Ψ (pairingBaseChange π π' b g ρ ρ' u u' hu hu') r).obj
        ((D((u)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (D((u')^*[ModuleCat.{u + 1} Λ])).obj ((fourierTransform Λ π π' Ψ b r).obj K) :=
  sorry

end BaseChange

section BaseLinear

/-- Blueprint `sk-prop-base-linear`: P7: the transform is linear over the base.

Tensoring the input with a complex pulled back from the base `S` along `π : V ⟶ S` is the
same as tensoring the output with the same complex pulled back along `π' : V' ⟶ S`:

`FT_ψ(K ⊗ᴸ π^* N) ≅ FT_ψ(K) ⊗ᴸ π'^* N`.

In particular `FT_ψ(π^* N) ≅ FT_ψ(Λ) ⊗ᴸ π'^* N`, so the transform of a complex pulled back
from the base is determined by the transform of the unit. -/
noncomputable def fourierTransformTensorIso [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ)
    (K : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (fourierTransform Λ π π' Ψ b r).obj ((tensorPullback Λ π N).obj K) ≅
      (tensorPullback Λ π' N).obj ((fourierTransform Λ π π' Ψ b r).obj K) :=
  sorry

end BaseLinear

end AlgebraicGeometry.Etale
