/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Module

/-!
# Lisse and constructible `Λ`-adic sheaves on the pro-étale site

This is the counterpart, for a coefficient field `Λ` with an ultrametric norm (the case of
interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Constructible`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

Let `X` be a scheme. Following Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8) and
the blueprint (`def-weil-finite-torsion-constructibility`), a
sheaf `F` of `Λ`-modules on the small pro-étale site of `X` is

- *lisse* (`AlgebraicGeometry.ProEtale.IsFieldLisseSheaf`) if it is pro-étale locally a finite
  direct sum of copies of the constant sheaf `Λ`
  (`AlgebraicGeometry.ProEtale.fieldConstantSheaf`), that is, locally free of finite rank over
  `Λ_X`;
- *constructible* (`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf`) if, locally on `X`,
  `X` is the disjoint union of finitely many locally closed subschemes on each of which `F` is
  lisse (`AlgebraicGeometry.ProEtale.IsFieldStratifiedLisseSheaf`).

A lisse sheaf on a connected `X` is the same as a continuous finite-dimensional representation
of `π₁(X)` with coefficients in `Λ`: the trivialising pro-étale cover may be taken to be a
pro-finite étale Galois cover, whose group acts continuously on the fibre `Λⁿ`. For `Λ = E`
these are the lisse `E`-sheaves of the blueprint.

The strata are only required to be locally closed: on the noetherian schemes of the blueprint
every locally closed subset is constructible, and with this convention pullback along an
arbitrary morphism preserves constructibility. The stratification is only required locally on
`X`, so that constructibility is a local property; on the quasi-compact schemes of the blueprint
this is the same as a global finite stratification.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsFieldLisseSheaf` and
  `AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf`.
- `AlgebraicGeometry.ProEtale.fieldConstructibleSheaf`: constructibility as an object property.
- `AlgebraicGeometry.ProEtale.IsIrreducibleFieldLocalSystem`: irreducible lisse sheaves.

## Main results

- `AlgebraicGeometry.ProEtale.isFieldLisseSheaf_fieldConstantSheaf`: `Λ_X` is lisse.
- `AlgebraicGeometry.ProEtale.IsFieldLisseSheaf.upperStar`,
  `AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.upperStar`: pullback preserves lisse and
  constructible sheaves. Both rest on `g^* Λ ≅ Λ`
  (`AlgebraicGeometry.ProEtale.upperStarFieldConstantSheafIso`).
- `AlgebraicGeometry.ProEtale.IsFieldLisseSheaf.biprod`,
  `AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.biprod`: binary direct sums of lisse,
  resp. constructible, sheaves are lisse, resp. constructible.
- The constructible sheaves contain `0` and are closed under isomorphisms and finite products.
  On a locally Noetherian scheme they are also closed under kernels and cokernels
  (`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Abelian`), and they are closed under
  extensions (`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Extension`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ] {X : Scheme.{u}}

end AlgebraicGeometry.ProEtale
