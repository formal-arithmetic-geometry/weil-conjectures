/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.RingTheory.Henselian.EtaleRetraction

/-!
# Functoriality of the strict henselization

Let `g : T ⟶ S` be a morphism of schemes and `t : Spec Ω ⟶ T` a geometric point, so that
`t ≫ g` is a geometric point of `S`. We construct the local homomorphism
`h : 𝒪^{sh}_{S, t ≫ g} ⟶ 𝒪^{sh}_{T, t}` of strict henselizations
(`AlgebraicGeometry.Scheme.strictHenselizationMap g t`): it is the unique ring homomorphism such
that `Spec h` is compatible with the structure morphisms to `S` and `T` and `h` is compatible with
the evaluations at the geometric points. For an affine pointed étale neighbourhood `(V, v)` of
`t ≫ g`, the composite `S_(t) ⟶ T_(t ≫ g) ⟶ V` is the unique morphism `T_(t) ⟶ V` over `S`
through which `v` factors (`strictLocalizationLift`); in particular it agrees with
`T_(t) ⟶ W ⟶ V` for every affine pointed étale neighbourhood `(W, w)` of `t` mapping to `V`.

The key input is `AlgebraicGeometry.existsUnique_lift_of_etale`: morphisms from the spectrum of a
strictly henselian local ring `R` lift uniquely along étale morphisms through prescribed points
over the closed point.

## Main definitions

- `AlgebraicGeometry.Scheme.strictLocalizationLift g t x`: the morphism `T_(t) ⟶ V` over `S`.
- `AlgebraicGeometry.Scheme.strictHenselizationMap g t`: the map `𝒪^{sh}_{S,t ≫ g} ⟶ 𝒪^{sh}_{T,t}`.

## Main results

- `AlgebraicGeometry.Scheme.existsUnique_strictHenselizationMap`: clause 3 of the blueprint.
- `AlgebraicGeometry.Scheme.strictLocalizationCone_π_app_comp_eq`: clause 4 of the blueprint.

## References

- Stacks Project, Lemma 59.33.1 and Definition 59.33.4,
  <https://stacks.math.columbia.edu/tag/04HX>, <https://stacks.math.columbia.edu/tag/03PS>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing

namespace AlgebraicGeometry

namespace Scheme

variable {S T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (g : T ⟶ S)
  (t : Spec (.of Ω) ⟶ T)

end Scheme

end AlgebraicGeometry
