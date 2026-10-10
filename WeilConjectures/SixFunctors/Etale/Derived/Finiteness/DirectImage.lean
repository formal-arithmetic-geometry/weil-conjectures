/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Finiteness of direct images

`Rf_*` and `Rf_!` preserve bounded constructibility, with a cohomological-dimension bound in
terms of the fibre dimension (`sk-prop-sf-finiteness`). Here `Λ` is a finite coefficient ring
whose exponent is invertible on the schemes in question
(`AlgebraicGeometry.HasInvertibleExponent`) and the schemes are of finite type over a field:
without the invertibility the Artin–Schreier sequence already defeats constructibility of
`R¹f_*` in characteristic `p`.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent`
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek` and
  `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek_padicAlgCl`
- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

section Finiteness

variable [Finite Λ] {k : Type u} [Field k]

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of direct images.** Let `Λ` be a finite ring whose exponent is invertible on `X`
and let `f : X ⟶ Y` be a quasi-compact morphism of finite-type `k`-schemes. Then `Rf_*`
carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`; separatedness of `f` is not needed.

The underlying numerical input is that the torsion cohomological dimension of a finite-type
`k`-scheme of dimension `d` over a field of torsion cohomological dimension at most `c` is
bounded by `2d + c`; in particular it is `0` for the spectrum of a separably closed field. -/
theorem boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent (f : X ⟶ Y)
    [QuasiCompact f] [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of compactly supported direct images.** For `f : X ⟶ Y` separated of finite type
between finite-type `k`-schemes, `Rf_!` carries `D^b_c(X, Λ)` into `D^b_c(Y, Λ)`. -/
theorem boundedConstructible_rightDerivedLowerShriek (f : X ⟶ Y) [HasCompactification f]
    [HasInvertibleExponent Λ X] (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [LocallyOfFiniteType aY] (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**Finiteness of compactly supported direct images with `ℚ̄_ℓ`-coefficients.** For a prime `ℓ`
invertible in `k` and `f : X ⟶ Y` separated of finite type between finite-type `k`-schemes,
`Rf_!` carries `D^b_c(X, ℚ̄_ℓ)` into `D^b_c(Y, ℚ̄_ℓ)`.

The blueprint deduces this from the finite-coefficient case
`boundedConstructible_rightDerivedLowerShriek` by passing to the limit over the `ℤ/ℓⁿ` and
inverting `ℓ`; that passage is not formalised. -/
theorem boundedConstructible_rightDerivedLowerShriek_padicAlgCl (l : ℕ) [Fact l.Prime]
    (hl : ringChar k ≠ l) (f : X ⟶ Y) [HasCompactification f] (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [LocallyOfFiniteType aY]
    (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)))))
    (hK : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))) Y
      ((R(f)_![ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))]).obj K) :=
  sorry

/-- Blueprint `sk-prop-sf-finiteness`: Finiteness and constructibility

**The fibre-dimension bound.** If `e` bounds the dimensions of the *geometric* fibres of a
separated finite-type `f : X ⟶ Y`, then `R^q f_! K = 0` for `q > 2e` and every bounded
constructible `K` concentrated in degrees `≤ 0`; for a sheaf `𝓕` placed in degree `0` this is
the blueprint's `R^q f_! 𝓕 = 0`. Some bound on the degrees of `K` is needed: for `f = 𝟙` the
complex `K = Λ[-1]` has `H^1(Rf_! K) = Λ`. -/
theorem isZero_homology_rightDerivedLowerShriek (f : X ⟶ Y) [HasCompactification f]
    [HasInvertibleExponent Λ X] (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (Limits.pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hK₀ : _root_.DerivedCategory.TStructure.t.IsLE K 0) (q : ℤ) (hq : (2 * e : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) :=
  sorry

end Finiteness

end Etale

end AlgebraicGeometry
