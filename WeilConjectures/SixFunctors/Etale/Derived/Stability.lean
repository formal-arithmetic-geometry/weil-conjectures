/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation

/-!
# Stability of the constructible finite-Tor categories under the six operations

Let `A` be a monoidal Grothendieck abelian coefficient category. This file states that the six
operations of `WeilConjectures.SixFunctors.Etale.Derived.*` preserve the small categories
`D_c^[a, b](X, A)` and `Dctf(X, A)` of
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`, together with explicit shifts for the
cohomological range and for the Tor amplitude, and it constructs the restrictions of `Lf^*`,
`Rf_*`, `Rf_!`, `Rf^!` and `𝔻_X` to `Dctf`.

The declarations are split over the modules
`WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic`, `….ClosedImmersion`,
`….OpenImmersion`, `….DirectImage`, `….UpperShriek` and `….Generation`, which this module
imports; downstream files may import this module or just the pieces they need.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.leftDerivedUpperStar`,
  `…rightDerivedLowerStar`, `…rightDerivedLowerShriek`, `…rightDerivedUpperShriek`,
  `…verdierDual`: the descended functors between the small categories `Dctf`.

## Main statements

- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedLowerShriek`.
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar`.
- `AlgebraicGeometry.Etale.boundedConstructible_derivedHom`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom`,
  `AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_of_isDualizable`,
  `AlgebraicGeometry.Etale.boundedConstructible_derivedHom_of_isDualizable`.
- `AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion`,
  `…_of_isFinite_of_etale`, `…_of_isClosedImmersion`, `…_of_smoothOfRelativeDimension`,
  `AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek`,
  and `exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le`
  (with explicit constants), in the namespace `AlgebraicGeometry.Etale`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_leftDerivedUpperStar`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_tensor`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerStar`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerShriek`,
  `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedUpperShriek`.
- `AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_openImmersionLowerShriek`
  (generators `Rg_* j_! L` with the extension by zero `j_!`) and its `Rj_!` form
  `AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_eq_triangEnvelope_ctfGenerators`: `Dctf(X, Λ)`
  is the thick envelope of the generators `AlgebraicGeometry.Etale.ctfGenerators`.
- `AlgebraicGeometry.Etale.torAmplitudeIn_singleFunctor_obj_of_flat`: a flat constructible
  sheaf in degree `0` has Tor amplitude in `[0, 0]`.

## Implementation details

* The statements about the constructibility of the derived tensor product and about open
  immersions are made for a finite coefficient ring `Λ`. For an arbitrary coefficient category
  the tensor statement is false (over `R = k[x, y₁, y₂, …]` on a point, `R/(x yᵢ)ᵢ ⊗ᴸ R/(x)` has
  the non-finitely generated `Tor₁ = (yᵢ)ᵢ/(x yᵢ)ᵢ`), and `Rj_!` agrees with extension by zero
  only when it is known to be independent of the compactification
  (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`).
* That `Rf_!` preserves `Dctf` is stated for a finite `Λ` whose exponent is invertible on `Y`,
  and `Y` of finite type over a field. Over an arbitrary base it is false: for
  `f : ⊔ₙ ℙⁿ_ℂ ⟶ ⊔ₙ Spec ℂ`, `Rf_! Λ` is not bounded.
* The smooth case of the `Rf^!` bounds uses
  `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor` instead of smooth purity: only
  the shape of `ω_f`, a locally constant free rank-one sheaf in degree `-2d`, matters.
* The bundled stability statements are `AlgebraicGeometry.Etale.constructibleFiniteTor_stability`
  and `AlgebraicGeometry.Etale.boundedConstructibleIntegral_stability` of
  `WeilConjectures.SixFunctors.Etale.Derived.Stability.CtfStability`, which cannot be imported
  here. That `𝔻_X` preserves `Dctf(X, A)` and is an anti-equivalence is
  `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual` and
  `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`; only the descended functor
  `DerivedCategoryFiniteTor.verdierDual` is built here.
* Stability under `Lf^*` assumes that pullbacks preserve flat sheaves
  (`AlgebraicGeometry.Etale.UpperStarPreservesFlat A`, an instance for `A = ModuleCat Λ`).
* The generation statement is stated for `A = ModuleCat Λ` with `Λ` finite and `X` Noetherian,
  since it uses flat constructible models
  (`hasTorAmplitudeIn_iff_exists_flatConstructibleModel`). "Thick subcategory" is spelled as an
  `ObjectProperty` that is `IsTriangulated`, `IsStableUnderRetracts` and
  `IsClosedUnderIsomorphisms`, and the generated thick subcategory is
  `ObjectProperty.triangEnvelope`.
* `AlgebraicGeometry.Etale.not_forall_torAmplitudeIn_derivedHom` shows that the sharper interval
  for `RHom` fails without dualizability; it assumes a normalized Tate twist datum.
* A dimension bound `dim X ≤ d` is `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. Forming `Rf_!`
  and `Rf^!` needs `HasCompactification f`, an explicit hypothesis throughout (it is not automatic
  for an open immersion); it supplies `IsSeparated f` and `LocallyOfFiniteType f`, so "separated
  of finite type" is spelled `[HasCompactification f] [QuasiCompact f]`.
* Statements are made relatively, for an arbitrary base and coefficient category, with the
  dimension bound explicit. The vanishing above twice the dimension also needs the
  characteristic of the coefficients to be invertible on the base, which cannot yet be expressed
  for a general `A`, so this hypothesis is missing from the statements carrying a `2d` bound.
* The statements about direct images, internal homs, exceptional inverse images and the Verdier
  dual are for torsion coefficients and assume
  `CategoryTheory.ConcreteCategory.FiniteOfIsFinitelyGenerated`; the direct image statements
  assume instead that `K` is killed by a nonzero integer and
  `CategoryTheory.ConcreteCategory.FinitelyGeneratedOfMono`. With coefficients `ℤ`, `Rf_*ℤ` is
  not constructible for `f : ℙ¹ ⟶ Spec k`; the `ℓ`-adic stages use the pro-étale formalism.
* The uniform shifts for `Rf^!` assume `[IsNoetherian Y]`: for `f : ⊔ₙ 𝔸ⁿ_k ⟶ ⊔ₙ Spec k` the
  complex `Rf^!Λ` sits in degree `-2n` on the `n`-th component, and Noetherianity gives
  `dim 𝔸ⁿ_V = dim V + n`.
* Every operation is defined on the ambient derived category and proved to descend to the small
  categories; every exceptional inverse image is the étale adjoint `Rf^!`, and the coherence of
  `WeilConjectures.SixFunctors.Etale.Derived.Composition` is proved for étale-origin complexes.
-/
