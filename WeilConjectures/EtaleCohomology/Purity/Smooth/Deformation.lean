/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpacePurity
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.Concentrated
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

/-!
# DNC invariance of the section dualizing line

The deformation to the normal cone of a *section* transports the section invariant
`𝒞(g, s) = Ls^* ω_g` of a smooth morphism with a closed section to the section invariant of
its normal cone with the zero section. Together with the model purity for `𝔸ⁿ` this is what
computes `ω_f` in the smooth case.

Given a deformation datum `g̃ : 𝒟_s V ⟶ 𝔸¹_B` with section `s̃`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`), the *family object* is
`F = Ls̃^* ω_{g̃}`. The blueprint argument has three steps:

* étale-locally on `B` the family is the standard family `a^* 𝒞(𝔸^d, 0)`, so `F` and `𝒞(g, s)`
  are shifts and twists of lisse rank-one sheaves (`lem-pur-concentrated-complex-shift`);
* the normalized local comparisons `F ≅ La^* 𝒞(g, s)` glue, by `𝔸¹`-invariance
  (`prop-pur-a1-invariance`), to a global one, for the projection `a : 𝔸¹_B ⟶ B`;
* restricting to `t = 0` gives `𝒞(g, s) ≅ 𝒞(π_N, 0_N)`, the fibres of `F` at `t = 1` and
  `t = 0` being the two section invariants by base change for the cohomologically smooth `g̃`.

## Implementation notes

The deformation space is carried as data, not constructed (see
`WeilConjectures.AlgebraicGeometry.DeformationToNormalCone`). Its étale-local coordinates
(`lem-pur-dnc-section-geometry` (2), (4), (5)) are a field of the datum; from them,
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.exists_etale_nonempty_iso_familyObject`
computes the family object over an étale cover of `B` as the one of the standard pair
`(𝔸^d → B, 0)`, pulled back from the base. The sheaf-theoretic inputs are base change for the
smooth `g̃` and `Re^! ≅ e^*` for an étale `e` (`lem-pur-co-smooth-etale-locality`).

The family comparison `κ : F ≅ La^* 𝒞(g, s)` is pinned down by its restriction `θ` at `t = 1`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.existsUnique_familyObject_iso`), so
its compatibility with base change in `B` is a statement about this unique comparison:
restricted along any `u : B' ⟶ B` it is the unique comparison normalized against `Lu^* θ`
(`Scheme.Hom.DeformationToNormalConeData.leftDerivedUpperStar_familyObject_iso_baseChange`).

The fibre identifications `θ₁ : i₁^* F ≅ 𝒞(g, s)` and `θ₀ : i₀^* F ≅ 𝒞(π_N, 0_N)` come from
the base change isomorphism of `sk-prop-cohsm` (c), which is only known to exist, so they are
arguments of the normalization in coordinates
(`AlgebraicGeometry.Etale.existsUnique_iso_sectionInvariant_normalCone`): for coordinates `e`
over a surjective `u : B' ⟶ B`, the DNC isomorphism is the unique one which after `Lu^*` is the
identity of the standard object, read through `e` at `t = 1` and at `t = 0`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.familyObject`: the family object
  `F = Ls̃^* ω_{g̃}`.

## Main statements

In the list below, `DeformationToNormalConeData` abbreviates
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`.

- `AlgebraicGeometry.Etale.exists_nonempty_iso_twistShift_of_leftDerivedUpperStar_iso`: an
  object which is étale-locally `Λ(m)[2m]` is a lisse rank-one sheaf, twisted and shifted.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_sectionInvariant`: base change
  of section invariants.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_of_etale_chart`: section invariants
  through an étale chart to `𝔸^d`.
- `DeformationToNormalConeData.exists_etale_nonempty_iso_familyObject`: étale-locally the family
  is the standard family.
- `DeformationToNormalConeData.exists_nonempty_iso_familyObject_twistShift`,
  `DeformationToNormalConeData.exists_nonempty_iso_sectionInvariant_twistShift`:
  the family object and the section invariant are lisse rank-one sheaves, twisted and shifted.
- `DeformationToNormalConeData.leftDerivedUpperStar_familyObject_iso_baseChange`: the
  comparison commutes with base change.
- `DeformationToNormalConeData.nonempty_iso_familyObject_leftDerivedUpperStar`,
  `DeformationToNormalConeData.existsUnique_familyObject_iso`:
  the family is constant along `𝔸¹_B`, by a comparison that is unique once normalized at
  `t = 1`.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`: DNC invariance.
- `AlgebraicGeometry.Etale.existsUnique_iso_sectionInvariant_normalCone`: its normalization in
  coordinates and uniqueness.
- `AlgebraicGeometry.Etale.exists_iso_sectionInvariant_normalCone`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStar_mapIso_iso_sectionInvariant_normalCone`: its
  compatibility with étale localization and arbitrary base change in `B`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

end Etale

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {V B : Scheme.{u}} {d : ℕ}
  {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)

variable [HasInvertibleExponent Λ B]

variable [HasCompactification g]

variable {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]

variable [HasTateTwist.IsNormalized Λ]

end Scheme.Hom.DeformationToNormalConeData

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {V B : Scheme.{u}}

end Etale

end AlgebraicGeometry
