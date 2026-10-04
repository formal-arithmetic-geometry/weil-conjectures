/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions

/-!

# Formal properties of the Fourier–Deligne transform

The Fourier–Deligne transform of `WeilConjectures.FourierTransform.Defs` is a kernel
transform, and the properties collected here are the ones a kernel transform always has:
its stalks are integrals of the input against the kernel, it commutes with base change on
`S`, it is linear over the base — it turns tensoring with a complex pulled back from `S`
into tensoring with the same complex pulled back to the dual — and it commutes with the
Tate twist.

All four are stated as isomorphisms of *functors*: an object-wise family of isomorphisms
would not suffice downstream, where they are used to build the inverse functor and to
transport `t`-structures.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensorRightPullback`: tensoring with a complex pulled
  back along `f : X ⟶ Y`, `N ↦ (K ↦ K ⊗ᴸ f^* N)`.
- `AlgebraicGeometry.Etale.artinSchreierTwist`: tensoring with the Artin–Schreier sheaf of
  a global function, `K ↦ K ⊗ᴸ ℒ_{Ψ, f}`.
- `AlgebraicGeometry.Etale.pairingAt`: the function `x ↦ b(x, ξ)` on the base change
  `V ×_S T` of `V` along a point `ξ : T ⟶ V'` of the dual.
- `AlgebraicGeometry.Etale.pairingBaseChange`: the base change of the pairing.

## Main statements

- `AlgebraicGeometry.Etale.fourierTransformPullbackIso`: the pullback of `FT_ψ(K)` along
  `ξ : T ⟶ V'` is the compactly supported pushforward to `T` of `K|_{V_ξ} ⊗ᴸ ℒ_{ψ(b(x, ξ))}`
  on `V_ξ = V ×_S T`, shifted by `r`; at a geometric point this computes the stalks of
  `FT_ψ(K)`.
- `AlgebraicGeometry.Etale.fourierTransformBaseChangeIso`: the transform commutes with base
  change along `S' ⟶ S`.
- `AlgebraicGeometry.Etale.fourierTransformTensorIso`: the transform is linear over the
  base.
- `AlgebraicGeometry.Etale.fourierTransformTateTwistIso`: the transform commutes with the
  Tate twist.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

/-- Tensoring with a complex pulled back along `f : X ⟶ Y`, as a functor of the complex
downstairs: `N ↦ (K ↦ K ⊗ᴸ f^* N)`. -/
noncomputable def derivedTensorRightPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  D((f)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedTensorRightFunctor (ModuleCat.{u + 1} Λ) X

/-- Twisting by the Artin–Schreier sheaf of a global function: `K ↦ K ⊗ᴸ ℒ_{Ψ, f}`. -/
noncomputable def artinSchreierTwist (X : Scheme.{u}) [CharP Γ(X, ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  derivedTensorRight (ModuleCat.{u + 1} Λ) X
    ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod X Ψ f))

section Stalk

/-- The pairing `b` pulled back to the fibre `V_ξ = V ×_S T` of `V` over a point
`ξ : T ⟶ V'` of the dual, where `T` lies over `S` via `ξ ≫ π'`. It is the pullback along the
morphism `V ×_S T ⟶ V ×_S V'` induced by `p₁` and `p₂ ≫ ξ`:

```
                 ⟨p₁, p₂ ≫ ξ⟩
      V ×_S T ─────────────────▶ V ×_S V'
        │                          │
      p₂│                          │p₂
        ▼                          ▼
        T ───────────ξ───────────▶ V'
```

When `T = Spec Ω` is a geometric point, this is the function `x ↦ b(x, ξ)` on the geometric
fibre `V_ξ`. -/
noncomputable def pairingAt (b : Γ(pullback π π', ⊤)) {T : Scheme.{u}} (ξ : T ⟶ V') :
    Γ(pullback π (ξ ≫ π'), ⊤) :=
  (pullback.lift (pullback.fst π (ξ ≫ π')) (pullback.snd π (ξ ≫ π') ≫ ξ)
    (by simp [pullback.condition])).appTop b

/-- For a morphism `ξ : T ⟶ V'`, the pullback of the Fourier–Deligne transform along `ξ` is
the compactly supported pushforward to `T` of the input restricted to the fibre
`V_ξ = V ×_S T`, twisted by the Artin–Schreier sheaf of the function `x ↦ b(x, ξ)` of
`AlgebraicGeometry.Etale.pairingAt`, shifted by the relative dimension:

`ξ^* FT_ψ(K) ≅ Rp₂,!(K|_{V_ξ} ⊗ᴸ ℒ_{ψ(b(x, ξ))})[r]`,

naturally in `K`. Here `V_ξ` sits in the square

```
                 ⟨p₁, p₂ ≫ ξ⟩
      V_ξ ────────────────────▶ V ×_S V'
        │                          │
      p₂│                          │p₂
        ▼                          ▼
        T ───────────ξ──────────▶  V'
```

When `T = Spec Ω` with `Ω` separably closed, so that `ξ` is a geometric point of `V'`, this
says that the stalk of `FT_ψ(K)` at `ξ` is `RΓ_c(V_ξ, K|_{V_ξ} ⊗ᴸ ℒ_{ψ(b(x, ξ))})[r]`.
(sketch blueprint: `sk-prop-stalk`) -/
noncomputable def fourierTransformPullbackIso [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification π] (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ)
    {T : Scheme.{u}} (ξ : T ⟶ V') [CharP Γ(pullback π (ξ ≫ π'), ⊤) p] :
    fourierTransform Λ π π' Ψ b r ⋙ D((ξ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((pullback.fst π (ξ ≫ π'))^*[ModuleCat.{u + 1} Λ]) ⋙
        artinSchreierTwist Λ (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ) ⋙
          R(pullback.snd π (ξ ≫ π'))_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r :=
  -- Proof sketch: compactly supported base change (sketch blueprint: `sk-prop-sf-cbc`) for
  -- `Rp₂,!` along `ξ` in the square above, followed by the projection formula for the
  -- pullback of the kernel to `V_ξ`. No smooth base change is needed.
  sorry

end Stalk

section BaseChange

/-- The base change of the pairing `b` along `g : S' ⟶ S`: its pullback to `W ×_{S'} W'`
along the induced morphism of fibre products,

```
      W ──u──▶ V           W' ──u'──▶ V'
      │        │            │         │
     ρ│        │π          ρ'│        │π'
      ▼        ▼            ▼         ▼
      S' ──g──▶ S           S' ──g──▶ S
```

Only commutativity of the two squares is needed to pull the pairing back; the base change
*theorem* below asks them to be cartesian. -/
noncomputable def pairingBaseChange (b : Γ(pullback π π', ⊤)) {S' W W' : Scheme.{u}}
    (g : S' ⟶ S) (ρ : W ⟶ S') (ρ' : W' ⟶ S') (u : W ⟶ V) (u' : W' ⟶ V')
    (hu : u ≫ π = ρ ≫ g) (hu' : u' ≫ π' = ρ' ≫ g) :
    Γ(pullback ρ ρ', ⊤) :=
  (pullback.map ρ ρ' π π' u u' g hu.symm hu'.symm).appTop b

/-- For a morphism `g : S' ⟶ S` and the base changes `W = V ×_S S'`, `W' = V' ×_S S'` with
the pulled back pairing, the Fourier–Deligne transform commutes with the pullbacks
`u^* : D(V_ét) ⥤ D(W_ét)` and `u'^* : D(V'_ét) ⥤ D(W'_ét)`:

`FT_ψ(u^* K) ≅ u'^* FT_ψ(K)`,

naturally in `K`. Both squares

```
      W ──u──▶ V           W' ──u'──▶ V'
      │        │            │         │
     ρ│        │π          ρ'│        │π'
      ▼        ▼            ▼         ▼
      S' ──g──▶ S           S' ──g──▶ S
```

must be **cartesian**: the isomorphism is proper base change for `Rp₂,!` along the induced
cartesian square `W ×_{S'} W' ⟶ V ×_S V'`, which is false for merely commuting squares.
(sketch blueprint: `sk-prop-base-change`) -/
noncomputable def fourierTransformBaseChangeIso [CharP Γ(pullback π π', ⊤) p]
    [HasCompactification (pullback.snd π π')]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ) {S' W W' : Scheme.{u}}
    (g : S' ⟶ S) (ρ : W ⟶ S') (ρ' : W' ⟶ S') (u : W ⟶ V) (u' : W' ⟶ V')
    (hu : IsPullback u ρ π g) (hu' : IsPullback u' ρ' π' g)
    [CharP Γ(pullback ρ ρ', ⊤) p] [HasCompactification (pullback.snd ρ ρ')] :
    D((u)^*[ModuleCat.{u + 1} Λ]) ⋙
        fourierTransform Λ ρ ρ' Ψ
          (pairingBaseChange π π' b g ρ ρ' u u' hu.w hu'.w) r ≅
      fourierTransform Λ π π' Ψ b r ⋙ D((u')^*[ModuleCat.{u + 1} Λ]) :=
  sorry

end BaseChange

section BaseLinear

variable [CharP Γ(pullback π π', ⊤) p] [HasCompactification (pullback.snd π π')]

/-- Tensoring the input with a complex pulled back from the base `S` along `π : V ⟶ S` is
the same as tensoring the output with the same complex pulled back along `π' : V' ⟶ S`:

`FT_ψ(K ⊗ᴸ π^* N) ≅ FT_ψ(K) ⊗ᴸ π'^* N`,

naturally in `K` **and** in `N`; that is the content of the statement below, an isomorphism
of functors `D(S_ét) ⥤ (D(V_ét) ⥤ D(V'_ét))`.

In particular `FT_ψ(π^* N) ≅ FT_ψ(Λ) ⊗ᴸ π'^* N`, so the transform of a complex pulled back
from the base is determined by the transform of the unit.
(sketch blueprint: `sk-prop-base-linear`) -/
noncomputable def fourierTransformTensorIso (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    derivedTensorRightPullback Λ π ⋙
        (Functor.whiskeringRight _ _ _).obj (fourierTransform Λ π π' Ψ b r) ≅
      derivedTensorRightPullback Λ π' ⋙
        (Functor.whiskeringLeft _ _ _).obj (fourierTransform Λ π π' Ψ b r) :=
  sorry

/-- The Fourier–Deligne transform commutes with the Tate twist: `FT_ψ(K(m)) ≅ FT_ψ(K)(m)`
for every `m : ℤ`, naturally in `K`. This is the second clause of the base linearity
proposition, the Tate twist being tensoring with an invertible complex pulled back from the
base.
(sketch blueprint: `sk-prop-base-linear`) -/
noncomputable def fourierTransformTateTwistIso [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r m : ℤ) :
    tateTwist Λ V m ⋙ fourierTransform Λ π π' Ψ b r ≅
      fourierTransform Λ π π' Ψ b r ⋙ tateTwist Λ V' m :=
  sorry

end BaseLinear

end AlgebraicGeometry.Etale
