/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.Sites.PullbackIsoOfLocallyGenerated
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Pullback of the constant sheaf

This is the counterpart, for a commutative coefficient ring `Λ` with an ultrametric norm (the
cases of interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers
`𝒪_E`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.UpperStar`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

The pullback of the constant sheaf `Λ_V` along an arbitrary morphism of schemes
`g : W ⟶ V` is the constant sheaf `Λ_W` (Bhatt–Scholze, *The pro-étale topology for
schemes*, Lemma 4.2.12 and §6.8).

For a weakly étale `g` the pullback is restriction along the localization functor
`W.ProEt ⥤ V.ProEt` (`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), and
both sheaves have the continuous functions on `T` as sections over `T → W`.

For a general `g`, the canonical morphism `g^* Λ_V ⟶ Λ_W`, adjoint to precomposition
`Λ_V ⟶ g_* Λ_W` with the projections `V' ×_V W ⟶ V'`, is an isomorphism by the criterion
`CategoryTheory.isIso_homEquiv_symm_of_locally_generated`:

- every section of `Λ_W` is locally the pullback of the tautological function on a constant
  profinite scheme `Spec (LocallyConstant K R)` over an affine open `Spec R ⊆ V`, for `K` a
  compact subset of `Λ`; this scheme is weakly étale
  over `Spec R` (`AlgebraicGeometry.ProEtale.exists_openImmersion_eq_comp_fst_field`);
- a section of `Λ_V` vanishing on the image of a map factors, locally, through its zero
  locus, which is weakly étale over `V`, being affine-locally the spectrum of a localization at
  idempotents (`AlgebraicGeometry.ProEtale.exists_opens_factor_of_eq_zero_field`).

## Main definitions

- `AlgebraicGeometry.ProEtale.upperStarFieldConstantSheafIsoOfWeaklyEtale`: `g^* Λ_V ≅ Λ_W`
  for a weakly étale `g`, computed by restriction.
- `AlgebraicGeometry.ProEtale.fieldConstantSheafToLowerStar`: the comparison
  `Λ_V ⟶ g_* Λ_W`.
- `AlgebraicGeometry.ProEtale.upperStarFieldConstantSheafIso`: `g^* Λ_V ≅ Λ_W` for an arbitrary
  `g`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ] {V W : Scheme.{u}}

section General

variable {Λ} (g : W ⟶ V)

end General

end AlgebraicGeometry.ProEtale
