/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal

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

- `AlgebraicGeometry.Etale.artinSchreierTwist`: tensoring with the Artin–Schreier sheaf of
  a global function, `K ↦ K ⊗ᴸ ℒ_{Ψ, f}`.
- `AlgebraicGeometry.Etale.pairingAt`: the function `x ↦ b(x, ξ)` on the base change
  `V ×_S T` of `V` along a point `ξ : T ⟶ V'` of the dual.
- `AlgebraicGeometry.Etale.pairingBaseChange`: the base change of the pairing.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_geometricStalk`: the stalk of
  `FT_ψ(K)` at a geometric point `ξ` of `V'` is the compactly supported cohomology of
  `K|_{V_ξ} ⊗ᴸ ℒ_{ψ(b(x, ξ))}` on the fibre `V_ξ = V ×_S Ω`, shifted by `r`.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_baseChange`: the transform commutes
  with base change along `S' ⟶ S`.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tensor`: the transform is
  linear over the base.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tateTwist`: the transform commutes
  with the Tate twist.

## Coefficients

Coefficient hypotheses follow the classes in `WeilConjectures.FourierTransform.Defs`.

## Implementation notes

The base change, base linearity and Tate twist compatibilities only assert that an
isomorphism *exists*. Later uses, such as transporting `t`-structures, will need specific
isomorphisms that are coherent with one another, which `Classical.choice` cannot provide.

The stalk formula and base change are compact-support base change for `Rp₂,!`
(sketch blueprint: `sk-prop-sf-cbc`), along `ξ` for the stalk formula and along the induced
cartesian square `W ×_{S'} W' ⟶ V ×_S V'` for base change. For the stalk formula it is
followed by the pullback of the kernel to `V_ξ`, which is formal (`Lξ^*` is monoidal); no
smooth base change is needed. In both cases the result is compared with `Rp₂,!` computed
with the *chosen* compactification of the base changed projection
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), which needs that projection to be
quasi-compact: it is a base change of `π`, resp. of `pullback.snd π π'`, which are assumed
quasi-compact.

Base linearity is the projection formula for `Rp₂,!` on the unbounded derived categories,
as in `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform`.

TODO: upgrade these back to `Iso` constructions once the exchange isomorphisms they are
built from exist as data.

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

/-- For a geometric point `ξ : Spec Ω ⟶ V'` of the dual, with `Ω` separably closed, the
stalk of the Fourier–Deligne transform at `ξ` is the compactly supported cohomology of the
input restricted to the geometric fibre `V_ξ = V ×_S Ω`, twisted by the Artin–Schreier sheaf
of the function `x ↦ b(x, ξ)` of `AlgebraicGeometry.Etale.pairingAt`, shifted by the relative
dimension:

`ξ^* FT_ψ(K) ≅ RΓ_c(V_ξ, K|_{V_ξ} ⊗ᴸ ℒ_{ψ(b(x, ξ))})[r]`,

naturally in `K`. Here `V_ξ` sits in the square

```
                 ⟨p₁, p₂ ≫ ξ⟩
      V_ξ ────────────────────▶ V ×_S V'
        │                          │
      p₂│                          │p₂
        ▼                          ▼
      Spec Ω ────────ξ─────────▶  V'
```

Class: torsion; decided by compact-support base change of `Rp₂,!` along `ξ`, which needs
`[Finite Λ]`.
(sketch blueprint: `sk-prop-stalk`) -/
theorem nonempty_iso_fourierTransform_geometricStalk [Finite Λ]
    [CharP Γ(pullback π π', ⊤) p] [HasCompactification π] [QuasiCompact π]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ V')
    [CharP Γ(pullback π (ξ ≫ π'), ⊤) p] :
    Nonempty (fourierTransform Λ π π' Ψ b r ⋙ D((ξ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((pullback.fst π (ξ ≫ π'))^*[ModuleCat.{u + 1} Λ]) ⋙
        artinSchreierTwist Λ (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ) ⋙
          R(pullback.snd π (ξ ≫ π'))_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r) :=
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

must be **cartesian**; the statement fails for merely commuting squares.

Class: torsion; decided by compact-support base change of `Rp₂,!` along the cartesian square
`W ×_{S'} W' ⟶ V ×_S V'` (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`),
which needs `[Finite Λ]` and the base changed projection `pullback.snd ρ ρ'` quasi-compact,
hence `[QuasiCompact (pullback.snd π π')]`.
(sketch blueprint: `sk-prop-base-change`) -/
theorem nonempty_iso_fourierTransform_baseChange [Finite Λ]
    [CharP Γ(pullback π π', ⊤) p] [HasCompactification (pullback.snd π π')]
    [LocallyOfFiniteType (pullback.snd π π')] [QuasiCompact (pullback.snd π π')]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ) {S' W W' : Scheme.{u}}
    (g : S' ⟶ S) (ρ : W ⟶ S') (ρ' : W' ⟶ S') (u : W ⟶ V) (u' : W' ⟶ V')
    (hu : IsPullback u ρ π g) (hu' : IsPullback u' ρ' π' g)
    [CharP Γ(pullback ρ ρ', ⊤) p] [HasCompactification (pullback.snd ρ ρ')] :
    Nonempty (D((u)^*[ModuleCat.{u + 1} Λ]) ⋙
          fourierTransform Λ ρ ρ' Ψ
            (pairingBaseChange π π' b g ρ ρ' u u' hu.w hu'.w) r ≅
        fourierTransform Λ π π' Ψ b r ⋙ D((u')^*[ModuleCat.{u + 1} Λ])) :=
  sorry

end BaseChange

section BaseLinear

variable [Finite Λ] [CharP Γ(pullback π π', ⊤) p] [HasCompactification (pullback.snd π π')]

/-- Tensoring the input with a complex pulled back from the base `S` along `π : V ⟶ S` is
the same as tensoring the output with the same complex pulled back along `π' : V' ⟶ S`:

`FT_ψ(K ⊗ᴸ π^* N) ≅ FT_ψ(K) ⊗ᴸ π'^* N`,

naturally in `K` **and** in `N`: the statement below asserts that the two functors
`D(S_ét) ⥤ (D(V_ét) ⥤ D(V'_ét))` are isomorphic. For fixed `N` it is the square

```
     D(V_ét) ───FT_ψ───▶ D(V'_ét)
        │                    │
  ⊗π^*N │                    │ ⊗π'^*N
        ▼                    ▼
     D(V_ét) ───FT_ψ───▶ D(V'_ét)
```

In particular `FT_ψ(π^* N) ≅ FT_ψ(Λ) ⊗ᴸ π'^* N`, so the transform of a complex pulled back
from the base is determined by the transform of the unit.

Class: torsion; decided by the projection formula for `Rp₂,!`
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`), which needs `[Finite Λ]`.
(sketch blueprint: `sk-prop-base-linear`) -/
theorem nonempty_iso_fourierTransform_tensor (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    Nonempty (derivedTensorRightPullback (ModuleCat.{u + 1} Λ) π ⋙
          (Functor.whiskeringRight _ _ _).obj (fourierTransform Λ π π' Ψ b r) ≅
        derivedTensorRightPullback (ModuleCat.{u + 1} Λ) π' ⋙
          (Functor.whiskeringLeft _ _ _).obj (fourierTransform Λ π π' Ψ b r)) :=
  sorry

/-- The Fourier–Deligne transform commutes with the Tate twist: `FT_ψ(K(m)) ≅ FT_ψ(K)(m)`
for every `m : ℤ`, naturally in `K`:

```
     D(V_ét) ───FT_ψ───▶ D(V'_ét)
        │                    │
    (m) │                    │ (m)
        ▼                    ▼
     D(V_ét) ───FT_ψ───▶ D(V'_ét)
```

This is the second clause of the base linearity proposition, the Tate twist being tensoring
with an invertible complex pulled back from the base: it is
`AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tensor` at `N = Λ_S(m)`, composed
with the identifications `π^* Λ_S(m) ≅ Λ_V(m)` and `π'^* Λ_S(m) ≅ Λ_{V'}(m)`.

Class: torsion; decided by the projection formula for `Rp₂,!`, through
`AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tensor`, which needs `[Finite Λ]`.
(sketch blueprint: `sk-prop-base-linear`) -/
theorem nonempty_iso_fourierTransform_tateTwist [HasTateTwist Λ] (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r m : ℤ) :
    Nonempty (tateTwist Λ V m ⋙ fourierTransform Λ π π' Ψ b r ≅
        fourierTransform Λ π π' Ψ b r ⋙ tateTwist Λ V' m) := by
  obtain ⟨e⟩ := nonempty_iso_fourierTransform_tensor Λ π π' Ψ b r
  -- `K ↦ K ⊗ᴸ f^* Λ_S(m)` is the Tate twist `(m)` on the source of `f`.
  let φ {X : Scheme.{u}} (f : X ⟶ S) :
      (derivedTensorRightPullback (ModuleCat.{u + 1} Λ) f).obj (tateObject Λ S m) ≅
        tateTwist Λ X m :=
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.mapIso
      (((leftDerivedUpperStarIsoMapDerivedCategory _ f).app _).symm ≪≫
        leftDerivedUpperStarTateObjectIso f m)
  exact ⟨Functor.isoWhiskerRight (φ π).symm _ ≪≫ e.app (tateObject Λ S m) ≪≫
    Functor.isoWhiskerLeft _ (φ π')⟩

end BaseLinear

end AlgebraicGeometry.Etale
