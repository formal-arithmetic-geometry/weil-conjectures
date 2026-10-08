/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion

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

- `AlgebraicGeometry.Etale.pointClass`: the class `[x ⊂ X] ∈ H^{2d}_c(X, Λ(d))` of a `k`-point.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.bijective_untwistedTraceMap`: the untwisted trace
  `H^{2d}_c(X, Λ) ⟶ Λ(-d)` is bijective.
- `AlgebraicGeometry.Etale.exists_tateOrientation_traceMap_pointClass`: for a suitable (the
  normalized) orientation the trace sends every point class to `1`.
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

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}} {d : ℕ}
  (a : X ⟶ Spec (.of k)) [IsProper a] [SmoothOfRelativeDimension d a] [GeometricallyConnected a]

namespace TateOrientation

variable [HasTateTwist Λ]

/-- Blueprint `sk-cor-trace` (the trace isomorphism, compactly supported form): for `X` smooth,
proper and geometrically connected of pure dimension `d` over the algebraically closed field `k`,
and any Tate orientation `γ`, the untwisted trace map
`tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` is bijective. -/
theorem bijective_untwistedTraceMap (γ : TateOrientation Λ a d) :
    Function.Bijective γ.untwistedTraceMap :=
  -- Proof sketch (blueprint): the duality `sk-thm-sf-identification` at `K = Λ_X` and `i = 0`
  -- reads `H^0_c(X, Λ)^∨ ≅ H^{2d}(X, Λ)(d)`; `H^0_c = H^0` as `X` is proper, and
  -- `H^0(X, Λ) = Λ` as `X` is connected (`sk-lem-finite`). The resulting isomorphism is the
  -- counit of `Ra_! ⊣ Ra^!` read through `γ`, i.e. the trace map.
  sorry

/-- The untwisted trace on ordinary cohomology, `tr^{(-d)}_X : H^{2d}(X, Λ) ⟶ Λ(-d)`, is
bijective: it is `AlgebraicGeometry.Etale.TateOrientation.untwistedTraceMap` read through
`H^{2d}(X, Λ) ≃ H^{2d}_c(X, Λ)`. -/
theorem bijective_untwistedTraceMap_comp_cohomologyAddEquivCompactSupport
    (γ : TateOrientation Λ a d) :
    Function.Bijective (γ.untwistedTraceMap.comp (cohomologyAddEquivCompactSupport a
      (leftDerivedUpperStarConstantComplexIso Λ a) (2 * d)).toAddMonoidHom) :=
  (bijective_untwistedTraceMap a γ).comp (AddEquiv.bijective _)

end TateOrientation

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]

/-- The class `[x ⊂ X] ∈ H^{2d}_c(X, Λ(d))` of a `k`-point `x : Spec k ⟶ X`: the fundamental
class `[x ⊂ X] ∈ H^{2d}_x(X, Λ(d))` of the regular closed immersion `x` of codimension `d`
(`AlgebraicGeometry.Etale.fundamentalClass`), mapped to `H^{2d}(X, Λ(d))` by forgetting supports,
that is by the counit `Rx_! Rx^! ⟶ 𝟙` of `Rx_! ⊣ Rx^!`, and read in `H^{2d}_c(X, Λ(d))` through
the adjunction `La^* ⊣ Ra_*` and `Ra_* ≅ Ra_!`. -/
noncomputable def pointClass (x : Spec (.of k) ⟶ X) [IsRegularImmersion d x] :
    𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d))⟦(2 * d : ℤ)⟧ :=
  haveI := HasInvertibleExponent.of_hom (Λ := Λ) a
  haveI := SmoothOfRelativeDimension.smooth d a
  (derivedUpperStarLowerStarAdjunction _ a).homEquiv _ _
      ((leftDerivedUpperStarConstantComplexIso Λ a).hom ≫
        fundamentalClass Λ d x a IsRegular.isRegularLocalRing_stalk ≫
          (rightDerivedUpperShriekAdjunction _ x).counit.app _) ≫
    (rightDerivedLowerStarShiftIsoLowerShriek a (tateObject Λ X d) (2 * d)).hom

/-- Blueprint `sk-cor-trace` (normalization of the trace by points): there is a Tate
orientation `γ` of `a` — the normalized orientation of `sk-thm-smooth-purity` — whose trace map
`tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ` sends the class `[x ⊂ X]` of every `k`-point `x` to `1`.

This is not an independent convention: by `sk-thm-regular` (c) the fundamental class of `x` is
the image of `1` under the isomorphism assembled from the orientations of `a` and of
`a ∘ x = 𝟙`, and the trace of its image is the counit of `R(a ∘ x)_! ⊣ R(a ∘ x)^!`, the
identity. -/
theorem exists_tateOrientation_traceMap_pointClass :
    ∃ γ : TateOrientation Λ a d, ∀ (x : Spec (.of k) ⟶ X) [IsRegularImmersion d x],
      x ≫ a = 𝟙 _ → γ.traceMap (pointClass a x) = 𝟙 _ :=
  -- Proof sketch (blueprint): take for `γ` the orientation of `sk-thm-smooth-purity`. By
  -- `sk-thm-regular` (c), `[x ⊂ X] = Φ_x(1)` for the isomorphism
  -- `Φ_x : Λ ≅ Rx^! Λ_X(d)[2d]` assembled from the orientations of `a` and of `a ∘ x = 𝟙`
  -- through `Rx^! Ra^! ≅ R(a ∘ x)^!`, and the orientation of the identity is the identity.
  -- Under `γ` the class `[x ⊂ X]` is `1 ∈ H^0(Rx^! Ra^! Λ)`, and its trace is the composite
  -- `Λ = R(a ∘ x)_! R(a ∘ x)^! Λ ≅ Ra_! Rx_! Rx^! Ra^! Λ ⟶ Ra_! Ra^! Λ ⟶ Λ` of counits, which is
  -- the counit of `R(a ∘ x)_! ⊣ R(a ∘ x)^!`, the identity.
  sorry

/-- Blueprint `sk-cor-trace`: The trace isomorphism.

Let `X` be smooth, proper and geometrically connected of pure dimension `d` over the
algebraically closed field `k`, and let `Λ` be a finite coefficient ring whose exponent is
invertible in `k`. Then:

1. for every Tate orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ`, the untwisted trace
   `tr^{(-d)}_X : H^{2d}(X, Λ) ⟶ Λ(-d)` is an isomorphism;
2. for the normalized orientation, the twisted trace `tr_X : H^{2d}(X, Λ(d)) ⟶ Λ` sends the
   class `[x ⊂ X]` of every `k`-point `x ∈ X(k)` to `1`.

See the module docstring for the form of the normalization. -/
theorem traceIsomorphism :
    (∀ γ : TateOrientation Λ a d,
      Function.Bijective (γ.untwistedTraceMap.comp (cohomologyAddEquivCompactSupport a
        (leftDerivedUpperStarConstantComplexIso Λ a) (2 * d)).toAddMonoidHom)) ∧
    ∃ γ : TateOrientation Λ a d, ∀ (x : Spec (.of k) ⟶ X) [IsRegularImmersion d x],
      x ≫ a = 𝟙 _ → γ.traceMap (pointClass a x) = 𝟙 _ :=
  ⟨TateOrientation.bijective_untwistedTraceMap_comp_cohomologyAddEquivCompactSupport a,
    exists_tateOrientation_traceMap_pointClass a⟩

end Etale

end AlgebraicGeometry
