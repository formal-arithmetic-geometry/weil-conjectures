/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk

/-!
# Stalks of a flat morphism to an affine scheme

For a flat morphism `g : X ⟶ Spec R` of schemes, the ring homomorphism `R ⟶ 𝒪_{X, x}` given by
taking global sections and then the germ at a point `x` of `X` is flat: it factors as the
localisation map `R ⟶ 𝒪_{Spec R, g x}` followed by the stalk map of `g`, and both are flat.
This is applied to the base change `W ×_T Tₙ ⟶ Tₙ` of a flat morphism `f : W ⟶ T` along the
`n`-th infinitesimal neighbourhood of a point `t` of `T`.

## Main results

- `AlgebraicGeometry.flat_ΓSpecIso_inv_comp_appTop_comp_germ`: for a flat morphism
  `g : X ⟶ Spec R` and any point `x` of `X`, the ring homomorphism `R ⟶ 𝒪_{X, x}` is flat; the
  special case `AlgebraicGeometry.flat_ΓSpecIso_inv_comp_germ` says that `R ⟶ 𝒪_{Spec R, y}` is
  flat, being a localisation of `R`.
- `AlgebraicGeometry.Scheme.flat_infinitesimalRingToStalk`: the stalks of `W ×_T Tₙ` are flat
  over `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)` when `f` is flat.

## Implementation notes

The flatness statements are phrased in terms of `RingHom.Flat`, not of `Module.Flat`: the
`Module.Flat` form needs an `Algebra` instance on a stalk, which is deliberately not made global
and is introduced at the call site by `algebraize`.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable (R : CommRingCat.{u}) {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- **The ring homomorphism `R ⟶ 𝒪_{Spec R, y}` is flat** for every point `y` of `Spec R`: it is
the localisation of `R` at the prime `y`. -/
lemma flat_ΓSpecIso_inv_comp_germ (y : Spec R) :
    ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ y trivial).hom.Flat := by
  have : y.asIdeal.IsPrime := y.isPrime
  rw [ΓSpecIso_inv_comp_germ_eq_toStalk]
  exact (RingHom.flat_algebraMap_iff
      (R := R) (S := (Spec.structureSheaf R).presheaf.stalk y)).mpr
    (IsLocalization.flat _ y.asIdeal.primeCompl)

variable {R}

/-- **The ring homomorphism `R ⟶ 𝒪_{X, x}` induced by a flat morphism `g : X ⟶ Spec R` is
flat**:

```
                 ΓSpecIso.inv                 g.appTop            germ ⊤ x
              R ──────────────▶ Γ(Spec R, 𝒪) ──────────▶ Γ(X, 𝒪) ──────────▶ 𝒪_{X, x}
                                     │                                          ▲
                                     │ germ ⊤ (g.base x)           g.stalkMap x │  (flat)
                                     └────────────▶ 𝒪_{Spec R, g.base x} ───────┘
                                                 (flat, a localisation)
```
-/
lemma flat_ΓSpecIso_inv_comp_appTop_comp_germ (g : X ⟶ Spec R) [Flat g] (x : X) :
    ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.Flat := by
  -- the composite is the localisation map followed by the stalk map of `g`
  rw [ΓSpecIso_inv_comp_appTop_comp_germ, CommRingCat.hom_comp]
  exact RingHom.Flat.comp (flat_ΓSpecIso_inv_comp_germ R _) (Flat.stalkMap _ x)

namespace Scheme

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T)

/-- **The stalks of `W ×_T Tₙ` are flat over `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)`** when `f` is flat.

Use `algebraize [(infinitesimalRingToStalk f t n x).hom]` for the `Module.Flat` form. -/
lemma flat_infinitesimalRingToStalk [Flat f] (n : ℕ) (x : infinitesimalBaseChange f t n) :
    (infinitesimalRingToStalk f t n x).hom.Flat := by
  rw [infinitesimalRingToStalk_eq_comp_appTop_comp_germ]
  exact flat_ΓSpecIso_inv_comp_appTop_comp_germ _ x

end Scheme

end AlgebraicGeometry
