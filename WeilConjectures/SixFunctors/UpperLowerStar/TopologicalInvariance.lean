/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!
# Topological invariance of the small étale topos

Let `f : X ⟶ Y` be a universal homeomorphism of schemes. Base change along `f` is an
equivalence of the small étale sites, matching the topologies
(`AlgebraicGeometry.Scheme.Hom.isDenseSubsite_etale`), so it induces an equivalence of the
small étale topoi. This is the sheaf-level half of [Stacks 03SI].

For arbitrary coefficients this is `AlgebraicGeometry.Etale.sheafEquivalence`, obtained from
`CategoryTheory.Equivalence.sheafCongr`; its functor is the pushforward
`AlgebraicGeometry.Etale.lowerStar`, which is restriction along base change. For
Grothendieck abelian coefficients, where the pullback
`AlgebraicGeometry.Etale.upperStar` is available, the pullback is the quasi-inverse.

## Main definitions

- `AlgebraicGeometry.Etale.sheafEquivalence`: the equivalence
  `Sheaf X.smallEtaleTopology A ≌ Sheaf Y.smallEtaleTopology A` for arbitrary coefficients
  `A`; its functor is the pushforward `(f)_*[A]`.
- `AlgebraicGeometry.Etale.upperStarIsoInverse`: the pullback `(f)^*[A]` is the quasi-inverse
  of the pushforward, by uniqueness of left adjoints.

## Main statements

- `AlgebraicGeometry.Etale.isEquivalence_lowerStar` and
  `AlgebraicGeometry.Etale.isEquivalence_upperStar`: the pushforward and the pullback along a
  universal homeomorphism are equivalences of categories of étale sheaves.

## Implementation notes

Everything in this file is proved; the only input left open is the equivalence of the
underlying categories, `AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`. Since that is
`sorry`ed it is not an instance, so it is activated by `attribute [local instance]` here and
the dependence is visible in the file text.

The general-coefficient statement comes first because it needs nothing on `A`: the
pushforward is objectwise restriction along base change, hence literally the functor of
`CategoryTheory.Equivalence.sheafCongr` for the equivalence of sites. The `upperStar`
statements then follow formally, the pullback being a left adjoint of an equivalence.

## References

* [Stacks 03SI], Étale Cohomology, Proposition 59.45.4.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme Etale

attribute [local instance] Scheme.Hom.isEquivalence_etale Scheme.Hom.isDenseSubsite_etale

section General

variable (A : Type u') [Category.{u + 1} A] {X Y : Scheme.{u}}

/-- **Topological invariance of the small étale topos**, [Stacks 03SI]: for a universal
homeomorphism `f : X ⟶ Y`, restriction along base change is an equivalence between the
category of `A`-valued sheaves on the small étale site of `X` and that of `Y`.

This is the sheaf-level form of the equivalence of sites
`AlgebraicGeometry.Scheme.Hom.isDenseSubsite_etale`.
(blueprint: `lemma:weil-pbc-universal-homeomorphism-coverings`) -/
@[stacks 03SI]
noncomputable def Etale.sheafEquivalence (f : X ⟶ Y) [IsUniversalHomeomorphism f] :
    Sheaf X.smallEtaleTopology A ≌ Sheaf Y.smallEtaleTopology A :=
  have : (f.etaleEquivalence.symm.inverse).IsDenseSubsite
      Y.smallEtaleTopology X.smallEtaleTopology := Scheme.Hom.isDenseSubsite_etale f
  f.etaleEquivalence.symm.sheafCongr X.smallEtaleTopology Y.smallEtaleTopology A

end General

section GrothendieckAbelian

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The pushforward along a universal homeomorphism is the functor of
`AlgebraicGeometry.Etale.sheafEquivalence`: both are restriction along the base change
functor `AlgebraicGeometry.Scheme.Hom.Etale`. -/
lemma Etale.lowerStar_eq_sheafEquivalence_functor :
    (f)_*[A] = (Etale.sheafEquivalence A f).functor :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- **Topological invariance of the small étale topos**, [Stacks 03SI]: the pushforward along
a universal homeomorphism is an equivalence of categories of étale sheaves. -/
@[stacks 03SI]
theorem Etale.isEquivalence_lowerStar : ((f)_*[A]).IsEquivalence :=
  inferInstanceAs ((Etale.sheafEquivalence A f).functor.IsEquivalence)

/-- The pullback along a universal homeomorphism is the quasi-inverse of the pushforward, by
uniqueness of left adjoints: `(f)^*[A] ⊣ (f)_*[A]` by
`AlgebraicGeometry.Etale.upperStarLowerStarAdjunction`, and the inverse of an equivalence is
left adjoint to it. -/
noncomputable def Etale.upperStarIsoInverse :
    (f)^*[A] ≅ (Etale.sheafEquivalence A f).inverse :=
  (Etale.upperStarLowerStarAdjunction A f).leftAdjointUniq
    (Etale.sheafEquivalence A f).symm.toAdjunction

/-- **Topological invariance of the small étale topos**, [Stacks 03SI]: the pullback along a
universal homeomorphism `f : X ⟶ Y` is an equivalence between the category of `A`-valued
sheaves on the small étale site of `Y` and that of `X`. -/
@[stacks 03SI]
theorem Etale.isEquivalence_upperStar : ((f)^*[A]).IsEquivalence :=
  Functor.isEquivalence_of_iso (Etale.upperStarIsoInverse A f).symm

end GrothendieckAbelian

end AlgebraicGeometry
