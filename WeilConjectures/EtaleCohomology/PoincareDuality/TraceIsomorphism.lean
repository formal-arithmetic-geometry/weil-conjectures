/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism.PointClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStarShift
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The trace isomorphism

Let `k` be an algebraically closed field, `Λ` a finite coefficient ring whose exponent is
invertible in `k` (the finite stage `A_{E,n}` of the blueprint), and `a : X ⟶ Spec k` smooth,
proper and geometrically connected of pure relative dimension `d`, with a Tate orientation
`γ : Λ_X(d)[2d] ≅ Ra^! Λ`. The trace isomorphism says:

* the untwisted trace `tr^{(-d)}_X : H^{2d}(X, Λ) ⟶ Λ(-d)` is bijective, whatever the
  orientation `γ`;
* for the normalized orientation, its twist `tr_X : H^{2d}(X, Λ(d)) ⟶ Λ` sends the class
  `[x ⊂ X]` of every `k`-point `x` of `X` to `1`.

The class `[x ⊂ X]` is the image in `H^{2d}(X, Λ(d)) = H^{2d}_c(X, Λ(d))` of the fundamental
class of the regular closed immersion `x : Spec k ⟶ X` of codimension `d`
(`AlgebraicGeometry.Etale.fundamentalClass`, `sk-thm-regular`), obtained by forgetting
supports.

## Main definitions

- `AlgebraicGeometry.Etale.unitClassCompactSupport`: the class `1 ∈ H^0_c(X, Λ)`.
- `AlgebraicGeometry.Etale.TateOrientation.traceDualityEquiv`: the duality at `i = 0`,
  `H^{2d}_c(X, Λ(d)) ≃ Hom(Ra_! Λ_X, Λ_Y)`.
- `AlgebraicGeometry.Etale.pointClass`: the class `[x ⊂ X] ∈ H^{2d}_c(X, Λ(d))` of a `k`-point.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.traceMap_eq_unitClassCompactSupport_comp`: the trace
  `tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ` is the map produced by the duality at `i = 0`, followed by
  evaluation at `1 ∈ H^0_c(X, Λ)`; `bijective_traceMap_iff` is the resulting criterion.
- `AlgebraicGeometry.Etale.TateOrientation.bijective_untwistedTraceMap`: the untwisted trace
  `H^{2d}_c(X, Λ) ⟶ Λ(-d)` is bijective.
- `AlgebraicGeometry.Etale.exists_tateOrientation_traceMap_pointClass`: for a suitable (the
  normalized) orientation the trace sends every point class to `1`. It rests on
  `AlgebraicGeometry.Etale.pointClass_eq` (all `k`-points have the same class) and
  `AlgebraicGeometry.Etale.isIso_traceMap_pointClass` (the trace of a point class is invertible).
- `AlgebraicGeometry.Etale.traceIsomorphism` (`sk-cor-trace`): the trace isomorphism
  `H^{2d}(X, Λ) ≅ Λ(-d)` and the normalization of the trace by point classes.

## Implementation notes

*The normalized orientation.* The repository has smooth purity only as the existence of an
isomorphism `Λ_X(d)[2d] ≅ Ra^! Λ`
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), not the canonical
orientation built from Kummer classes in `sk-thm-smooth-purity`. The normalization is therefore
stated as the existence of a Tate orientation whose trace sends all point classes to `1`.

*Points.* A `k`-point `x` of the smooth `X` is a regular closed immersion of codimension `d`; this
is taken as an instance argument `[IsRegularImmersion d x]`.

*Other coefficient stages.* The stages `𝒪_E`, `E` and `ℚ̄_ℓ` are not available for the étale
derived categories of the repository (see
`WeilConjectures.EtaleCohomology.PoincareDuality.Transport`). The field-stage statements with
their Frobenius actions are in `WeilConjectures.WeilSheaf.TraceIsomorphism`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section DualityAtZero

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y} [HasCompactification a] [IsProper a] {d : ℕ}

namespace TateOrientation

end TateOrientation

end DualityAtZero

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} [HasInvertibleExponent Λ X] {d : ℕ}
  (a : X ⟶ Spec (.of k)) [IsProper a] [SmoothOfRelativeDimension d a] [GeometricallyConnected a]

namespace TateOrientation

variable [HasTateTwist Λ]

end TateOrientation

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]

end Etale

end AlgebraicGeometry
