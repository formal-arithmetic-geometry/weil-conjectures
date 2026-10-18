/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Formal
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!
# Finite exceptional adjoints and Verdier duality

For a finite coefficient ring `Λ` whose exponent is invertible on an algebraically closed field
`k`, and a morphism `f : X ⟶ Y` of separated schemes of finite type over `k`, the exceptional
inverse image of an object `L` of `Dctf(Y, Λ)` is computed by Verdier duality:

`Rf^! L ≅ 𝔻_X (Lf^* (𝔻_Y L))`

(blueprint `lem-coef-finite-exceptional`). Consequently `Rf^!` carries a constructible complex of
Tor amplitude in `[a, b]` to a constructible complex of Tor amplitude in
`[a - 2 dim X, b + 2 dim Y]`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor`:
  the duality formula.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_and_torAmplitudeIn_rightDerivedUpperShriek`:
  the Tor amplitude bound.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
  [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
  (f : X ⟶ Y) [HasCompactification f] [HasCompactification (f ≫ aY)] [QuasiCompact (f ≫ aY)]

/-- Blueprint `lem-coef-finite-exceptional`: Finite exceptional adjoints and coefficient change,
the duality formula.

For a finite `Λ` whose exponent is invertible on an algebraically closed field `k`, a separated
finite-type `k`-scheme `Y` with structure morphism `a_Y`, and `f : X ⟶ Y` (with `a_X = f ≫ a_Y`),
every `L ∈ Dctf(Y, Λ)` satisfies `Rf^! L ≅ 𝔻_X (Lf^* (𝔻_Y L))`: by biduality
`L ≅ 𝔻_Y 𝔻_Y L` (`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`), and duality
against pullback `𝔻_X (Lf^* M) ≅ Rf^! (𝔻_Y M)`
(`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`) at `M = 𝔻_Y L`. -/
theorem nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty ((R(f)^![ModuleCat.{u + 1} Λ]).obj L ≅
      (verdierDual (ModuleCat.{u + 1} Λ) (f ≫ aY)).obj
        (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
          ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op L))))) := by
  obtain ⟨β⟩ := nonempty_iso_verdierDual_verdierDual Λ aY hL
  obtain ⟨e⟩ := nonempty_iso_verdierDual_leftDerivedUpperStar Λ aY f
    ((verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op L))
  exact ⟨(R(f)^![ModuleCat.{u + 1} Λ]).mapIso β ≪≫ e.symm⟩

/-- Blueprint `lem-coef-finite-exceptional`: Finite exceptional adjoints and coefficient change,
the Tor interval of the finite exceptional adjoint.

In the situation of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor`,
with `X` separated of finite type over `k` and `dim X ≤ d_X`, `dim Y ≤ d_Y`: if `L` is bounded
constructible of Tor amplitude in `[a, b]`, then `Rf^! L` lies in `Dctf(X, Λ)` with Tor amplitude
in `[a - 2 d_X, b + 2 d_Y]`. Indeed `𝔻_Y` sends `[a, b]` to `[-b - 2 d_Y, -a]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_verdierDual`), `Lf^*` preserves Tor amplitude, and
`𝔻_X` then gives `[a - 2 d_X, b + 2 d_Y]`. -/
theorem constructibleFiniteTor_and_torAmplitudeIn_rightDerivedUpperShriek
    [IsSeparated (f ≫ aY)] [LocallyOfFiniteType (f ≫ aY)] (dX dY : ℕ)
    (hdX : topologicalKrullDim X ≤ (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y ≤ (dY : WithBot ℕ∞)) (a b : ℤ)
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : boundedConstructible (ModuleCat.{u + 1} Λ) Y L)
    (hLt : torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b L) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((R(f)^![ModuleCat.{u + 1} Λ]).obj L) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * (dX : ℤ)) (b + 2 * (dY : ℤ))
        ((R(f)^![ModuleCat.{u + 1} Λ]).obj L) := by
  have hctf : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L := ⟨hL, a, b, hLt⟩
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_of_constructibleFiniteTor Λ aY f hctf
  have h₁ := constructibleFiniteTor_verdierDual Λ aY hctf
  have h₁t := torAmplitudeIn_verdierDual Λ aY dY hdY a b hL hLt
  have h₂ := constructibleFiniteTor_leftDerivedUpperStar _ f h₁
  have h₂t := torAmplitudeIn_leftDerivedUpperStar _ f _ _ h₁t
  have h₃ := constructibleFiniteTor_verdierDual Λ (f ≫ aY) h₂
  have h₃t := torAmplitudeIn_verdierDual Λ (f ≫ aY) dX hdX _ _ h₂.1 h₂t
  refine ⟨(constructibleFiniteTor _ X).prop_of_iso e.symm h₃,
    (torAmplitudeIn _ X _ _).prop_of_iso e.symm ?_⟩
  convert h₃t using 2 <;> ring

end Etale

end AlgebraicGeometry
