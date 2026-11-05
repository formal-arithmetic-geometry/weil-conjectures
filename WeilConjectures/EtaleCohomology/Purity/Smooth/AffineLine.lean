/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback
public import WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineRelative
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineInputs

/-!
# The affine line, `𝔾ₘ`, and the model purity

The rank-one computation that the whole of smooth purity rests on. The base `Y` is separated
of finite type over a field `k`, the coefficient ring `Λ` is finite with exponent invertible
on `Y`, and `p : 𝔸¹_Y → Y` is the projection, `s : Y → 𝔸¹_Y` the zero section and
`j : 𝔾_{m,Y} → 𝔸¹_Y` the open complement:

* the affine line is acyclic, `Rp_* Λ ≅ Λ_Y`, and `Rπ_* Λ(1)` has `Λ_Y(1)` in degree zero,
  `Λ_Y` in degree one and nothing else (`sk-prop-a1-kummer`);
* consequently `Rs^! Λ(1)[2] ≅ Λ_Y`, the *fundamental class* of the zero section
  (`sk-prop-a1`);
* a complex on `𝔸¹_Y` that is a pullback is determined by its restriction to `t = 1`, so its
  fibres at `t = 0` and `t = 1` agree (`sk-prop-a1-inv`).

Iterating the one-dimensional case gives the model purity `Rz^! Λ(c)[2c] ≅ Λ_B` for the zero
section of `𝔸^c_B` (`sk-prop-an`), in
`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace`.

The invertibility hypothesis is not decorative: for `Λ = ℤ/p` over a base of characteristic
`p` the Artin–Schreier sequence gives `H¹(𝔸¹_k, ℤ/p) = k[t]/(F − 1)k[t] ≠ 0`, so the affine
line is not acyclic and every statement below fails.

## Implementation notes

`𝔾_m` is not a Mathlib scheme, so the open complement of the zero section is carried as data:
a scheme `G` with an open immersion `j` whose range is the complement of the range of the
zero section. This is the same idiom as `AlgebraicGeometry.Etale.openClosedShortComplex`.

The statements that compare the twist with geometry, `R¹π_*Λ(1) ≅ Λ_Y`,
`R^mπ_*Λ(1) = 0` for `m ≥ 2` and `Rs^!Λ(1)[2] ≅ Λ_Y`, assume the twist datum normalized
(`AlgebraicGeometry.Etale.HasTateTwist.IsNormalized`); they are false for the untwisted datum
`Λ_X(m) = Λ_X` or the shifted datum `Λ_X(m) = Λ_X[-2m]` (for the latter
`R²π_*(Λ_G[-2]) = R⁰π_*Λ_G = Λ_Y ≠ 0`). The last is then the normalisation itself,
transported along the identification of the zero section with `V(t)`.

Two clauses of the blueprint are stated only in part, and are TODOs.

* `sk-prop-a1-kummer` is recorded here as what the cohomology sheaves *are* rather than as a
  statement about the generator `κ(t)` of `R¹π_*Λ(1)`; for the twist `Λ(1) = μₙ ⊗ Λ` the
  generator, the unit `p^*` in degree zero and the compatibility with base change on `Y` are in
  `WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer`
  (`AlgebraicGeometry.Etale.isIso_homology_zero_kummerClassAdjoint` and its neighbours).
  Here `sk-prop-a1` records that `Rs^!Λ(1)[2] ≅ Λ_Y`; that the boundary `∂κ(t)` of the Kummer class
  (`AlgebraicGeometry.Etale.kummerBoundary`) is this isomorphism is the orientation
  `AlgebraicGeometry.Etale.affineLineOrientation` of
  `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation`.
* The gluing half of `sk-prop-a1-inv` (ii) — that normalized local comparisons over an étale
  cover of `Y` glue (`prop-pur-a1-invariance`) — is stated for a single surjective étale
  `v : Y' ⟶ Y`, the disjoint union of the members of a covering family.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_affineLine`
- `AlgebraicGeometry.Etale.nonempty_iso_homology_zero_multiplicativeGroup`,
  `AlgebraicGeometry.Etale.nonempty_iso_homology_one_multiplicativeGroup`,
  `AlgebraicGeometry.Etale.isZero_homology_multiplicativeGroup`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLineZero`
- `AlgebraicGeometry.Etale.injective_upperStar_map_of_isFiniteLocallyConstantSheaf`,
  `AlgebraicGeometry.Etale.injective_upperStar_oneSection_map_of_isFiniteLocallyConstantSheaf`
- `AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_oneSection_eq`
- `AlgebraicGeometry.Etale.existsUnique_iso_leftDerivedUpperStar_of_etale`,
  `AlgebraicGeometry.Etale.exists_iso_leftDerivedUpperStar_oneSection_iff_of_etale`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

section

variable {k : Type u} [Field k] {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY]
  [LocallyOfFiniteType aY] [HasInvertibleExponent Λ Y]

omit [HasTateTwist Λ] [HasInvertibleExponent Λ Y] in
include aY in
/-- Blueprint `lem-pur-a1-direct-image`: The affine line has no higher direct images

For `B` separated of finite type over the algebraically closed field `k` and the projection
`π : 𝔸¹_B ⟶ B`, the unit `Λ_B ⟶ Rπ_* Lπ^* Λ_B = Rπ_* Λ_{𝔸¹_B}` of `Lπ^* ⊣ Rπ_*` is an
isomorphism: the affine line has no higher direct images for the constant coefficients, and its
`H⁰` is the unit. The proof computes `Rπ_* Λ ≅ RΓ(𝔸¹_k, Λ)_B ≅ Λ_B` by the Künneth formula
(in place of the stalk computation over strict henselizations by smooth base change of the
blueprint), and then the unit, split by the zero section, is an isomorphism by counting
geometric stalks. -/
theorem isIso_unit_constantComplex_affineLine [IsAlgClosed k] [QuasiCompact aY]
    [HasInvertibleExponent Λ (Spec (.of k))] :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).unit.app (constantComplex Λ Y)) :=
  isIso_unit_affineLine_of_cohomology Λ aY (isZero_cohomology_affineLine Λ (k := k))
    (cohomologyZeroConstantComplexIso Λ _)
    (constructibleFiniteTor_constantComplex Λ Y) (constantComplexIsoSingleFunctor Λ Y)
    (nonempty_sheafFiber_unit_iso Λ)

variable {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]

end

end Etale

end AlgebraicGeometry
