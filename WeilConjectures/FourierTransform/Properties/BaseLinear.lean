/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.FourierTransform.Defs

/-!

# Base linearity of the Fourier–Deligne transform

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tensor`: the transform is
  linear over the base.
- `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tateTwist`: the transform commutes
  with the Tate twist.

See `WeilConjectures.FourierTransform.Properties` for the implementation notes.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)

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
