/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonUnit

/-!
# Base change between strictly henselian local rings at the closed point

Let `ι : R₁ ⟶ R₂` be a local homomorphism of strictly henselian local rings,
`tᵢ : Spec Ωᵢ ⟶ Spec Rᵢ`
morphisms from spectra of separably closed fields and `c : Spec Ω₂ ⟶ Spec Ω₁` with
`c ≫ t₁ = t₂ ≫ Spec ι`, and `b : R₂ ⟶ κ` a map to a field with kernel the maximal ideal. This
square is not cartesian, and its base change morphism `L(Spec ι)^* Rt₁_* ⟶ Rt₂_* Lc^*` is not
invertible; but it becomes invertible after pullback to the closed point `Spec b` of `Spec R₂`, at
every complex bounded below of étale origin
(`isIso_leftDerivedUpperStar_map_derivedBaseChangeMap_app_of_isStrictlyHenselianLocalRing`).
For strictly henselian traits with geometric generic points, this says that the nearby cycles of
the trait itself are invariant under change of trait, the step (B) of the proof of SGA 4½,
[Th. finitude], Prop. 3.7.

Every complex `L` bounded below of étale origin on `Spec Ω₁` is `Lt₁^* F` for `F = ν^* G` with `G`
a complex on `Spec R₁` with constant cohomology sheaves
(`AlgebraicGeometry.Etale.exists_isConstant_homology_iso_upperStar_obj`). At such an `L`, the base
change morphism composed with `L(Spec ι)^*` of the unit `F ⟶ Rt₁_* Lt₁^* F` is the unit at
`L(Spec ι)^* F` followed by an isomorphism (`CategoryTheory.unit_mateEquiv`). After pullback to the
closed point both units are invertible
(`ProEtale.isIso_leftDerivedUpperStar_map_unit_app_of_isConstant_homology`): the second since
`L(Spec ι)^* F` is again `ν^*` of a complex with constant cohomology sheaves, the first since the
composite `Spec b ≫ Spec ι` is a closed point of `Spec R₁`, `ι` being local.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry.ProEtale
