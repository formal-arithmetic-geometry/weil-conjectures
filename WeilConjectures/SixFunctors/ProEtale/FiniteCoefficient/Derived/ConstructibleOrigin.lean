/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology

/-!
# Intrinsically constructible pro-étale complexes are of étale origin

Let `Λ` be a finite commutative ring and `X` a scheme. A bounded complex of pro-étale sheaves of
`Λ`-modules with constructible cohomology sheaves (in the intrinsic sense of
`AlgebraicGeometry.ProEtale.IsConstructible`) is of étale origin: it is `D(ν^*) K'` for a bounded
complex `K'` of étale sheaves with constructible cohomology sheaves. This is clause (ii) of
blueprint `lem-sf-proetale-constructible-origin`, deduced from its clause (i)
(`AlgebraicGeometry.ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`) by
dévissage along the truncation triangles
(`AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin_of_etaleOriginHomology`) and the
full faithfulness of `ν^*`.

## Main statements

- `ProEtale.DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic`:
  intrinsically bounded constructible complexes are of étale origin.
- `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleIntrinsic_eq`: the two readings
  of `Dᵇc(X_proét, Λ)` agree.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}}

/-- Blueprint `lem-sf-proetale-constructible-origin`, clause (ii): at a finite coefficient ring,
a bounded pro-étale complex with constructible cohomology sheaves is of étale origin. By clause
(i) its cohomology sheaves are `ν^*` of constructible étale sheaves, so it is `D(ν^*) K'` for a
bounded below étale complex `K'` (dévissage along the truncation triangles); `K'` is bounded with
constructible cohomology since `ν^*` is exact and fully faithful. -/
theorem DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleIntrinsic Λ X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K :=
  sorry

variable (Λ X) in
/-- Blueprint `lem-sf-proetale-constructible-origin`, clause (ii): at a finite coefficient ring,
the intrinsic and the étale-origin readings of `Dᵇc(X_proét, Λ)` agree. -/
theorem DerivedCategory.boundedConstructibleIntrinsic_eq :
    DerivedCategory.boundedConstructibleIntrinsic Λ X =
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X :=
  le_antisymm (fun _ hK ↦ DerivedCategory.boundedConstructible_of_boundedConstructibleIntrinsic hK)
    (DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic)

end AlgebraicGeometry.ProEtale
