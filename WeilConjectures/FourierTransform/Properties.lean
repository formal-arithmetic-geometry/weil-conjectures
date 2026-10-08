/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
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
- `AlgebraicGeometry.Etale.fibreToProduct`: the morphism `⟨p₁, p₂ ≫ ξ⟩ : V ×_S T ⟶ V ×_S V'`
  from the fibre of `p₂` over a point `ξ : T ⟶ V'` of the dual.
- `AlgebraicGeometry.Etale.pairingAt`: the function `x ↦ b(x, ξ)` on the base change
  `V ×_S T` of `V` along a point `ξ : T ⟶ V'` of the dual.
- `AlgebraicGeometry.Etale.fourierTransformStalkIso`: the stalk formula as an isomorphism of
  functors.
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

The stalk formula is constructed as an isomorphism
(`AlgebraicGeometry.Etale.fourierTransformStalkIso`). The base change, base linearity and Tate
twist compatibilities only assert that an isomorphism *exists*. Later uses, such as
transporting `t`-structures, will need specific isomorphisms that are coherent with one
another, which `Classical.choice` cannot provide.

The stalk formula and base change are compact-support base change for `Rp₂,!`
(sketch blueprint: `sk-prop-sf-cbc`), along `ξ` for the stalk formula and along the induced
cartesian square `W ×_{S'} W' ⟶ V ×_S V'` for base change. For the stalk formula it is
followed by the pullback of the kernel to `V_ξ`, which is formal (`Lξ^*` is monoidal); no
smooth base change is needed. In both cases the result is compared with `Rp₂,!` computed
with the *chosen* compactification of the base changed projection
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), which needs that projection to be
quasi-compact: it is a base change of `π`, resp. of `pullback.snd π π'`, which are assumed
quasi-compact.

Base linearity is the base linearity of kernel transforms
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor`), that is, the projection
formula for `Rp₂,!`. The statement is over the whole unbounded derived categories, while the
project's projection formula
`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerShriek` only covers a
bounded constructible `K` and an `N` of finite Tor amplitude. It therefore uses the unbounded
projection formula `AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`, which holds for
all finite `Λ` (SGA 4 XVII 5.2.9): the projection map is an isomorphism for `j_!` of an open
immersion formally, and for a proper morphism because its direct image then has finite
cohomological dimension and so commutes with the colimits reducing to bounded complexes.

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

/-- The morphism `⟨p₁, p₂ ≫ ξ⟩ : V ×_S T ⟶ V ×_S V'` from the fibre `V_ξ = V ×_S T` of the
second projection over a point `ξ : T ⟶ V'` of the dual, where `T` lies over `S` via
`ξ ≫ π'`. It is the top arrow of the cartesian square
(`AlgebraicGeometry.Etale.isPullback_fibreToProduct`)

```
                 ⟨p₁, p₂ ≫ ξ⟩
      V ×_S T ─────────────────▶ V ×_S V'
        │                          │
      p₂│                          │p₂
        ▼                          ▼
        T ───────────ξ───────────▶ V'
```
-/
noncomputable def fibreToProduct {T : Scheme.{u}} (ξ : T ⟶ V') :
    pullback π (ξ ≫ π') ⟶ pullback π π' :=
  pullback.lift (pullback.fst π (ξ ≫ π')) (pullback.snd π (ξ ≫ π') ≫ ξ)
    (by simp [pullback.condition])

@[reassoc (attr := simp)]
lemma fibreToProduct_fst {T : Scheme.{u}} (ξ : T ⟶ V') :
    fibreToProduct π π' ξ ≫ pullback.fst π π' = pullback.fst π (ξ ≫ π') :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma fibreToProduct_snd {T : Scheme.{u}} (ξ : T ⟶ V') :
    fibreToProduct π π' ξ ≫ pullback.snd π π' = pullback.snd π (ξ ≫ π') ≫ ξ :=
  pullback.lift_snd _ _ _

/-- The fibre `V ×_S T` of the second projection `p₂ : V ×_S V' ⟶ V'` over `ξ : T ⟶ V'` is
the fibre product of `p₂` and `ξ`. -/
lemma isPullback_fibreToProduct {T : Scheme.{u}} (ξ : T ⟶ V') :
    IsPullback (fibreToProduct π π' ξ) (pullback.snd π (ξ ≫ π')) (pullback.snd π π') ξ :=
  IsPullback.of_right (h₁₂ := pullback.fst π π') (h₂₂ := π') (v₁₃ := π)
    (by rw [fibreToProduct_fst]; exact IsPullback.of_hasPullback π (ξ ≫ π'))
    (fibreToProduct_snd π π' ξ) (IsPullback.of_hasPullback π π')

/-- The pairing `b` pulled back to the fibre `V_ξ = V ×_S T` of `V` over a point
`ξ : T ⟶ V'` of the dual, where `T` lies over `S` via `ξ ≫ π'`. It is the pullback along the
morphism `AlgebraicGeometry.Etale.fibreToProduct` `V ×_S T ⟶ V ×_S V'` induced by `p₁` and
`p₂ ≫ ξ`:

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
  (fibreToProduct π π' ξ).appTop b

section

variable [CharP Γ(pullback π π', ⊤) p] (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤))
  (r : ℤ) {T : Scheme.{u}} (ξ : T ⟶ V') [CharP Γ(pullback π (ξ ≫ π'), ⊤) p]

/-- The pullback of the Fourier kernel to the fibre `V_ξ` is the Artin–Schreier sheaf of the
pairing with `ξ`: `⟨p₁, p₂ ≫ ξ⟩^* 𝒦_ψ ≅ ℒ_{ψ(b(x, ξ))}`, placed in degree `0`. -/
noncomputable def fourierKernelFibreIso :
    D((fibreToProduct π π' ξ)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafZMod (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ)) :=
  ((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _).symm ≪≫
    (singleFunctorCompLeftDerivedUpperStarIso _ _).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (artinSchreierSheafZModPullbackIso (fibreToProduct π π' ξ) Ψ b)

/-- Pulling the Fourier integrand back to the fibre `V_ξ`: with `g = ⟨p₁, p₂ ≫ ξ⟩`,
`g^*(p₁^* K ⊗ᴸ 𝒦_ψ) ≅ (p₁ ∘ g)^* K ⊗ᴸ ℒ_{ψ(b(x, ξ))}`, naturally in `K`. -/
noncomputable def fourierIntegrandFibreIso :
    fourierIntegrand Λ π π' Ψ b ⋙ D((fibreToProduct π π' ξ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((pullback.fst π (ξ ≫ π'))^*[ModuleCat.{u + 1} Λ]) ⋙
        artinSchreierTwist Λ (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ _).symm ≪≫
        derivedTensorRightCompLeftDerivedUpperStarIso _ _ _ ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ _) _ ≪≫
        Functor.isoWhiskerLeft _ ((derivedTensorRightFunctor _ _).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _ ≪≫
            fourierKernelFibreIso Λ π π' Ψ b ξ))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} Λ)
          (fibreToProduct π π' ξ) (pullback.fst π π') (pullback.fst π (ξ ≫ π'))
          (fibreToProduct_fst π π' ξ).symm) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).symm _

/-- **The stalk formula** as an isomorphism of functors: for a point `ξ : T ⟶ V'` of the
dual,

`ξ^* FT_ψ(K) ≅ Rp₂,!((p₁ ∘ g)^* K ⊗ᴸ ℒ_{ψ(b(x, ξ))})[r]`

on the fibre `V_ξ = V ×_S T`, with `g = ⟨p₁, p₂ ≫ ξ⟩`, naturally in `K`. It is
compact-support base change of `Rp₂,!` along `ξ`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`), followed by the
pullback of the Fourier integrand to `V_ξ`: `Lg^*` is monoidal and
`g^* 𝒦_ψ ≅ ℒ_{ψ(b(x, ξ))}`. For `T = Spec Ω` a geometric point this is the stalk of the
transform at `ξ`; see `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_geometricStalk`.
(sketch blueprint: `sk-prop-stalk`; blueprint: `lem-fd-stalk-formula`) -/
noncomputable def fourierTransformStalkIso [Finite Λ] [HasCompactification π]
    [QuasiCompact π] :
    fourierTransform Λ π π' Ψ b r ⋙ D((ξ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((pullback.fst π (ξ ≫ π'))^*[ModuleCat.{u + 1} Λ]) ⋙
        artinSchreierTwist Λ (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ) ⋙
          R(pullback.snd π (ξ ≫ π'))_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ (isPullback_fibreToProduct π π' ξ)
  Functor.isoWhiskerLeft
      (fourierIntegrand Λ π π' Ψ b ⋙ R(pullback.snd π π')_![ModuleCat.{u + 1} Λ])
      (D((ξ)^*[ModuleCat.{u + 1} Λ]).commShiftIso r) ≪≫
    Functor.isoWhiskerLeft (fourierIntegrand Λ π π' Ψ b)
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ ξ).symm ≪≫
          asIso (rightDerivedLowerShriekBaseChangeMap _ (isPullback_fibreToProduct π π' ξ)) ≪≫
          Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ _) _)
        (shiftFunctor _ r) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fourierIntegrandFibreIso Λ π π' Ψ b ξ) _ ≪≫
    Functor.associator _ _ _

end

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
`[Finite Λ]`. The isomorphism is `AlgebraicGeometry.Etale.fourierTransformStalkIso`.
(sketch blueprint: `sk-prop-stalk`; blueprint: `lem-fd-stalk-formula`) -/
theorem nonempty_iso_fourierTransform_geometricStalk [Finite Λ]
    [CharP Γ(pullback π π', ⊤) p] [HasCompactification π] [QuasiCompact π]
    (Ψ : AddChar (ZMod p) Λ) (b : Γ(pullback π π', ⊤)) (r : ℤ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ V')
    [CharP Γ(pullback π (ξ ≫ π'), ⊤) p] :
    Nonempty (fourierTransform Λ π π' Ψ b r ⋙ D((ξ)^*[ModuleCat.{u + 1} Λ]) ≅
      D((pullback.fst π (ξ ≫ π'))^*[ModuleCat.{u + 1} Λ]) ⋙
        artinSchreierTwist Λ (pullback π (ξ ≫ π')) Ψ (pairingAt π π' b ξ) ⋙
          R(pullback.snd π (ξ ≫ π'))_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r) :=
  ⟨fourierTransformStalkIso Λ π π' Ψ b r ξ⟩

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

Class: compactification-dependent; decided by independence of the compactification. The
blueprint proof is formal: compact-support base change along the cartesian square
`W ×_{S'} W' ⟶ V ×_S V'`. Here `[Finite Λ]` enters solely through independence of the
compactification (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`), since `R(f)_!` is
computed with a chosen compactification. The same comparison is why
`[QuasiCompact (pullback.snd π π')]` is assumed: compact-support base change
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap` needs the base changed
morphism `f' = pullback.snd ρ ρ'` to be quasi-compact, because it goes through
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`, and `f'` is quasi-compact as a base change
of `pullback.snd π π'` (`MorphismProperty.of_isPullback`).
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
        fourierTransform Λ π π' Ψ b r ⋙ D((u')^*[ModuleCat.{u + 1} Λ])) := by
  -- the induced morphism `h : W ×_{S'} W' ⟶ V ×_S V'` of fibre products
  let h : pullback ρ ρ' ⟶ pullback π π' := pullback.map ρ ρ' π π' u u' g hu.w.symm hu'.w.symm
  -- the square of `h` over `u'` is cartesian: pasted with the square of `V ×_S V'` it is the
  -- square of `W ×_{S'} W'` pasted with the cartesian square of `u`
  have hsq : IsPullback h (pullback.snd ρ ρ') (pullback.snd π π') u' := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback π π')
    rw [pullback.lift_fst, hu'.w]
    exact (IsPullback.of_hasPullback ρ ρ').paste_horiz hu
  have : QuasiCompact (pullback.snd ρ ρ') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ hsq
  have hb : pairingBaseChange π π' b g ρ ρ' u u' hu.w hu'.w = h.appTop b := by
    unfold pairingBaseChange; rfl
  rw [hb]
  -- the kernel pulls back to the kernel: `Lh^* 𝒦_ψ ≅ 𝒦'_ψ`
  let eK : L((h)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ ρ ρ' Ψ (h.appTop b)) :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ h).app _ ≪≫
      ((h)^*[ModuleCat.{u + 1} Λ].mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (artinSchreierSheafZModPullbackIso h Ψ b)
  refine ⟨?_⟩
  calc D((u)^*[ModuleCat.{u + 1} Λ]) ⋙ D((pullback.fst ρ ρ')^*[ModuleCat.{u + 1} Λ]) ⋙
        derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback ρ ρ')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ ρ ρ' Ψ (h.appTop b))) ⋙
        R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r
      _ ≅ L((u)^*[ModuleCat.{u + 1} Λ]) ⋙ L((pullback.fst ρ ρ')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback ρ ρ')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ ρ ρ' Ψ (h.appTop b))) ⋙
          R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r :=
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ u).symm _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
            (leftDerivedUpperStarIsoMapDerivedCategory _ (pullback.fst ρ ρ')).symm _)
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙ L((h)^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback ρ ρ')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ ρ ρ' Ψ (h.appTop b))) ⋙
          R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r :=
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight ((leftDerivedUpperStarComp _ (pullback.fst ρ ρ') u).symm ≪≫
            leftDerivedUpperStarComp _ h (pullback.fst π π') _ (pullback.lift_fst _ _ _).symm) _ ≪≫
          Functor.associator _ _ _
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙ L((h)^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight _ _ (L((h)^*[ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b))) ⋙
          R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r :=
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
          (Functor.isoWhiskerRight ((derivedTensor _ _).flip.mapIso eK.symm) _))
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ⋙
          L((h)^*[ModuleCat.{u + 1} Λ]) ⋙ R(pullback.snd ρ ρ')_![ModuleCat.{u + 1} Λ] ⋙
          shiftFunctor _ r :=
        Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (derivedTensorRightCompLeftDerivedUpperStarIso _ h _).symm _ ≪≫
          Functor.associator _ _ _)
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ⋙
          R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙ L((u')^*[ModuleCat.{u + 1} Λ]) ⋙
          shiftFunctor _ r :=
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (asIso (rightDerivedLowerShriekBaseChangeMap _ hsq)).symm _ ≪≫
          Functor.associator _ _ _))
      _ ≅ L((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ⋙
          R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r ⋙
          L((u')^*[ModuleCat.{u + 1} Λ]) :=
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
          (L((u')^*[ModuleCat.{u + 1} Λ]).commShiftIso r).symm))
      _ ≅ D((pullback.fst π π')^*[ModuleCat.{u + 1} Λ]) ⋙
          derivedTensorRight (ModuleCat.{u + 1} Λ) (pullback π π')
          ((DerivedCategory.singleFunctor _ 0).obj (fourierKernel Λ π π' Ψ b)) ⋙
          R(pullback.snd π π')_![ModuleCat.{u + 1} Λ] ⋙ shiftFunctor _ r ⋙
          D((u')^*[ModuleCat.{u + 1} Λ]) :=
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ _) _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
            (Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ u'))))

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

Class: torsion; decided by the projection formula for `Rp₂,!` on the unbounded derived
categories (`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`), which needs `[Finite Λ]`.
The proof is that of `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_tensor`.
(sketch blueprint: `sk-prop-base-linear`; blueprint: `prop-base-linear`) -/
theorem nonempty_iso_fourierTransform_tensor (Ψ : AddChar (ZMod p) Λ)
    (b : Γ(pullback π π', ⊤)) (r : ℤ) :
    Nonempty (derivedTensorRightPullback (ModuleCat.{u + 1} Λ) π ⋙
          (Functor.whiskeringRight _ _ _).obj (fourierTransform Λ π π' Ψ b r) ≅
        derivedTensorRightPullback (ModuleCat.{u + 1} Λ) π' ⋙
          (Functor.whiskeringLeft _ _ _).obj (fourierTransform Λ π π' Ψ b r)) :=
  have := isIso_projectionMap_of_finite Λ (pullback.snd π π')
  nonempty_iso_kernelTransform_tensor (ModuleCat.{u + 1} Λ) π π' _ r

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
(sketch blueprint: `sk-prop-base-linear`; blueprint: `prop-base-linear`, clause (2)) -/
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
