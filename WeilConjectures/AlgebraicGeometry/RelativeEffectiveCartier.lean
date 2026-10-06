/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

/-!
# Relative effective Cartier divisors

Let `π : X ⟶ S` be a morphism of schemes. A closed subscheme `D ⊆ X`, given by a quasi-coherent
ideal `J`, is a *relative effective Cartier divisor on `X/S`* if `J` is invertible (`D` is an
effective Cartier divisor on `X`) and `D ⟶ S` is flat:
`AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier`.

We state the criteria that the Picard framework needs:

* a locally principal closed subscheme of a flat, locally finitely presented `X/S` whose fibres
  are effective Cartier divisors is a relative effective Cartier divisor;
* on a smooth `X/S` of relative dimension `1` (the Cartier criterion), a closed subscheme which
  is finite locally free over `S` is a relative effective Cartier divisor, a relative effective
  Cartier divisor is the same as a closed subscheme which is locally quasi-finite, flat and
  locally of finite presentation over `S`, and if moreover `X/S` is proper, a relative effective
  Cartier divisor is finite locally free over `S`;
* relative effective Cartier divisors are stable under base change, and so is their line bundle.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier`
  (blueprint `def-pc-relative-effective-cartier`).

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.IsLocallyPrincipal.isInvertible_and_flat`
  (blueprint `lem-pc-recd-locally-principal`).
- `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isFinite_and_locallyOfFinitePresentation`
  (blueprint `lem-pc-cartier-criterion`, `(2) ⇒ (1)` for proper `X/S`).
- `AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat`
  (blueprint `lem-pc-cartier-criterion`, `(1) ⇒ (2)`).
- `AlgebraicGeometry.Scheme.IdealSheafData.isRelativeEffectiveCartier_of_isFinite`,
  `AlgebraicGeometry.Scheme.IdealSheafData.isRelativeEffectiveCartier_iff_locallyQuasiFinite`,
  `AlgebraicGeometry.Scheme.IdealSheafData.locallyOfFinitePresentation_of_locallyQuasiFinite`
  (blueprint `lem-pc-cartier-criterion`, the remaining implications).
- `AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap_of_isPullback`
  (blueprint `lem-pc-recd-pullback`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

open scoped AlgebraicGeometry.Scheme.Modules

/-- A closed subscheme `D ⊆ X`, with quasi-coherent ideal `J`, is a **relative effective Cartier
divisor on `X/S`** for a morphism `π : X ⟶ S` if it is an effective Cartier divisor on `X`, i.e.
`J` is invertible, and `D ⟶ S` is flat.

(Stacks, Tag 062T; blueprint: `def-pc-relative-effective-cartier`) -/
def IsRelativeEffectiveCartier (J : X.IdealSheafData) (π : X ⟶ S) : Prop :=
  J.IsInvertible ∧ Flat (J.subschemeι ≫ π)

/-- **Effective Cartier divisors from local equations.** Let `π : X ⟶ S` be flat and locally of
finite presentation and let `D ⊆ X` be a locally principal closed subscheme, with ideal `J`. If
every fibre `D_s ⊆ X_s` is an effective Cartier divisor, then `D` is a relative effective
Cartier divisor on `X/S`: `J` is invertible and `D ⟶ S` is flat.

(Stacks, Tag 062Y; blueprint: `lem-pc-recd-locally-principal`) -/
theorem IsLocallyPrincipal.isInvertible_and_flat (π : X ⟶ S) [Flat π]
    [LocallyOfFinitePresentation π] {J : X.IdealSheafData} (hJ : J.IsLocallyPrincipal)
    (hfib : ∀ s : S, (J.comap (π.fiberι s)).IsInvertible) :
    J.IsInvertible ∧ Flat (J.subschemeι ≫ π) :=
  sorry

/-- **The Cartier criterion on proper smooth curves.** Let `π : X ⟶ S` be proper and smooth of
relative dimension `1`, and let `D ⊆ X` be a relative effective Cartier divisor, i.e. its ideal
`J` is invertible and `D ⟶ S` is flat. Then `D ⟶ S` is finite locally free: finite, (flat) and
locally of finite presentation.

(Stacks, Tag 0B9D; blueprint: `lem-pc-cartier-criterion`, the implication `(2) ⇒ (1)` for
proper `X/S`) -/
theorem IsInvertible.isFinite_and_locallyOfFinitePresentation (π : X ⟶ S)
    [IsProper π] [SmoothOfRelativeDimension 1 π] {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hflat : Flat (J.subschemeι ≫ π)) :
    IsFinite (J.subschemeι ≫ π) ∧ LocallyOfFinitePresentation (J.subschemeι ≫ π) :=
  sorry

/-- **Finite locally free closed subschemes of a smooth curve are divisors.** Let `π : X ⟶ S`
be smooth of relative dimension `1`, and let `D ⊆ X` be a closed subscheme, with ideal `J`,
which is finite locally free over `S`: `D ⟶ S` is finite, flat and locally of finite
presentation. Then `J` is invertible, so `D` is a relative effective Cartier divisor on `X/S`.

(Stacks, Tag 0B9D; blueprint: `lem-pc-cartier-criterion`, the implication `(1) ⇒ (2)`) -/
theorem isInvertible_of_isFinite_of_flat (π : X ⟶ S) [SmoothOfRelativeDimension 1 π]
    {J : X.IdealSheafData} (hfin : IsFinite (J.subschemeι ≫ π)) (hflat : Flat (J.subschemeι ≫ π))
    (hlfp : LocallyOfFinitePresentation (J.subschemeι ≫ π)) : J.IsInvertible :=
  sorry

/-- **The Cartier criterion, `(1) ⇒ (2)`, for relative divisors.** Let `π : X ⟶ S` be smooth of
relative dimension `1` and let `D ⊆ X` be a closed subscheme, with ideal `J`, which is finite
locally free over `S`. Then `D` is a relative effective Cartier divisor on `X/S`: `J` is
invertible by `isInvertible_of_isFinite_of_flat`, and `D ⟶ S` is flat by hypothesis.

(Stacks, Tag 0B9D; blueprint: `lem-pc-cartier-criterion`, the implication `(1) ⇒ (2)`) -/
theorem isRelativeEffectiveCartier_of_isFinite (π : X ⟶ S) [SmoothOfRelativeDimension 1 π]
    {J : X.IdealSheafData} [IsFinite (J.subschemeι ≫ π)] [Flat (J.subschemeι ≫ π)]
    [LocallyOfFinitePresentation (J.subschemeι ≫ π)] :
    J.IsRelativeEffectiveCartier π :=
  ⟨isInvertible_of_isFinite_of_flat π inferInstance inferInstance inferInstance, inferInstance⟩

/-- **The Cartier criterion, `(2) ⇔ (3)`.** Let `π : X ⟶ S` be smooth of relative dimension `1`
and let `D ⊆ X` be a closed subscheme, with ideal `J`. Then `D` is a relative effective Cartier
divisor on `X/S` if and only if `D ⟶ S` is locally quasi-finite, flat and locally of finite
presentation.

(Stacks, Tag 0B9D; blueprint: `lem-pc-cartier-criterion`, the equivalence `(2) ⇔ (3)`) -/
theorem isRelativeEffectiveCartier_iff_locallyQuasiFinite (π : X ⟶ S)
    [SmoothOfRelativeDimension 1 π] {J : X.IdealSheafData} :
    J.IsRelativeEffectiveCartier π ↔ LocallyQuasiFinite (J.subschemeι ≫ π) ∧
      Flat (J.subschemeι ≫ π) ∧ LocallyOfFinitePresentation (J.subschemeι ≫ π) :=
  sorry

/-- **The Cartier criterion, `(4) ⇒ (3)` over a locally noetherian base.** A locally
quasi-finite morphism into a locally noetherian scheme is locally of finite presentation.

In the Stacks project a locally quasi-finite morphism is locally of finite type; Mathlib's
`AlgebraicGeometry.LocallyQuasiFinite` does not include this, so it is assumed separately.

(Stacks, Tag 01TX; blueprint: `lem-pc-cartier-criterion`, the implication `(4) ⇒ (3)` for
locally noetherian `S`) -/
theorem locallyOfFinitePresentation_of_locallyQuasiFinite [IsLocallyNoetherian S] (π : X ⟶ S)
    {J : X.IdealSheafData} [LocallyOfFiniteType (J.subschemeι ≫ π)]
    [LocallyQuasiFinite (J.subschemeι ≫ π)] :
    LocallyOfFinitePresentation (J.subschemeι ≫ π) :=
  inferInstance

/-- **Pullback of relative effective Cartier divisors.** Let `π : X ⟶ S` be flat and locally of
finite presentation, let `D ⊆ X` be a relative effective Cartier divisor on `X/S` with ideal
`J`, and let

```
  X' ──── g' ───▶ X
  │               │
  π'              π
  ▼               ▼
  T ───── g ────▶ S
```

be a pullback square. Then the base change `D_T = D ×[S] T ⊆ X'`, with ideal `J.comap g'`, is a
relative effective Cartier divisor on `X'/T`, and its line bundle is the pullback of that of
`D`: `𝒪_{X'}(D_T) ≅ g'^* 𝒪_X(D)`.

(Stacks, Tag 056Q; blueprint: `lem-pc-recd-pullback`) -/
theorem IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback {π : X ⟶ S}
    [Flat π] [LocallyOfFinitePresentation π] {J : X.IdealSheafData}
    (hJ : J.IsRelativeEffectiveCartier π) {X' T : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ T}
    {g : T ⟶ S} (h : IsPullback g' π' π g) : (J.comap g').IsRelativeEffectiveCartier π' :=
  sorry

/-- **Pullback of relative effective Cartier divisors, with the line bundle.** In the situation
of `IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback`, the base change
`D_T` is a relative effective Cartier divisor on `X'/T` and `𝒪_{X'}(D_T) ≅ g'^* 𝒪_X(D)`.

(Stacks, Tag 056Q; blueprint: `lem-pc-recd-pullback`) -/
theorem IsRelativeEffectiveCartier.comap_of_isPullback {π : X ⟶ S} [Flat π]
    [LocallyOfFinitePresentation π] {J : X.IdealSheafData} (hJ : J.IsRelativeEffectiveCartier π)
    {X' T : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ T} {g : T ⟶ S} (h : IsPullback g' π' π g) :
    (J.comap g').IsRelativeEffectiveCartier π' ∧
      Nonempty ((J.comap g').toModulesᵛ ≅ (Modules.pullback g').obj J.toModulesᵛ) := by
  have h' := hJ.isRelativeEffectiveCartier_comap_of_isPullback h
  exact ⟨h', (hJ.1.nonempty_pullback_dual_toModules_iso g' h'.1).map Iso.symm⟩

end AlgebraicGeometry.Scheme.IdealSheafData
