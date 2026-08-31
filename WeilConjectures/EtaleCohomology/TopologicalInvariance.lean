/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.EtaleCohomology.TopologicalInvarianceOfSite
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!
# Topological invariance of étale cohomology

Let `f : X ⟶ Y` be a universal homeomorphism of schemes. Then the small étale topoi of `X`
and `Y` are equivalent, and the pullback induces an isomorphism on étale cohomology in
every degree. This is [Stacks 03SI].

The topos statement is the sheaf-level form of the equivalence of small étale sites
`AlgebraicGeometry.Scheme.Hom.etaleEquivalence`: the pullback `(f)^*[A]` of
`WeilConjectures.SixFunctors.UpperLowerStar.Etale` is an equivalence of categories of
sheaves, with quasi-inverse the pushforward `(f)_*[A]`. The cohomological statement is
about Mathlib's sheaf cohomology `CategoryTheory.Sheaf.H`, i.e. `Ext`-groups out of the
constant sheaf `ℤ`, for coefficients in `AddCommGrpCat`.

## Main statements

- `AlgebraicGeometry.Etale.isEquivalence_upperStar`: the pullback along a universal
  homeomorphism is an equivalence of categories of étale sheaves.
- `AlgebraicGeometry.Etale.upperStarEquivalence`: the same, as a bundled equivalence of
  the small étale topoi of `Y` and `X`.
- `AlgebraicGeometry.Etale.cohomologyEquiv`: for every abelian sheaf `F` on the small
  étale site of `Y` and every `q`, the pullback induces an isomorphism
  `H^q(Y_ét, F) ≅ H^q(X_ét, f^* F)`.

## Implementation notes

The two `sorry`s are `Etale.isEquivalence_upperStar` and `Etale.cohomologyEquiv`; the
bundled equivalence and the identification of its inverse with `(f)_*[A]` are derived from
the first. The intended proof of the first is that the equivalence of sites of [Stacks 04DZ]
induces an equivalence on sheaves, and the second then follows since `f^*` is an exact
equivalence sending the constant sheaf `ℤ` to the constant sheaf `ℤ`, hence identifies the
`Ext`-groups computing sheaf cohomology.

Applying `CategoryTheory.Sheaf.H` on the small étale sites needs sheafification and
`Ext`-groups there: the former is
`CategoryTheory.GrothendieckTopology.hasSheafify_smallEtaleTopology`, the latter comes from
`CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_smallEtaleTopology` through
`CategoryTheory.IsGrothendieckAbelian.hasExt`. Both are found by instance search, which is
why this file imports `Mathlib.Algebra.Category.Grp.AB`,
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt` and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`.

## References

* [Stacks 03SI], Étale Cohomology, Proposition 59.45.4.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme Etale

section Topos

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f]

/-- **Topological invariance of the small étale topos**: the pullback along a universal
homeomorphism `f : X ⟶ Y` is an equivalence between the category of `A`-valued sheaves on
the small étale site of `Y` and that of `X`.

This is the sheaf-level form of the equivalence of sites
`AlgebraicGeometry.Scheme.Hom.etaleEquivalence`: an equivalence of sites carries sheaves to
sheaves in both directions, hence induces an equivalence of the associated topoi. -/
@[stacks 03SI]
instance Etale.isEquivalence_upperStar : ((f)^*[A]).IsEquivalence := sorry

/-- **Topological invariance of the small étale topos**, [Stacks 03SI]: for a universal
homeomorphism `f : X ⟶ Y`, the pullback `f^*` is an equivalence between the small étale
topos of `Y` and the small étale topos of `X`.

Its inverse is isomorphic to the pushforward `(f)_*[A]`, since `(f)^*[A] ⊣ (f)_*[A]` by
`AlgebraicGeometry.Etale.upperStarLowerStarAdjunction`. -/
@[stacks 03SI]
noncomputable def Etale.upperStarEquivalence :
    Sheaf Y.smallEtaleTopology A ≌ Sheaf X.smallEtaleTopology A :=
  ((f)^*[A]).asEquivalence

/-- The pushforward along a universal homeomorphism is the inverse of
`AlgebraicGeometry.Etale.upperStarEquivalence`, by uniqueness of right adjoints. -/
noncomputable def Etale.lowerStarIsoInverse :
    (f)_*[A] ≅ (Etale.upperStarEquivalence A f).inverse :=
  (Etale.upperStarLowerStarAdjunction A f).rightAdjointUniq
    (Etale.upperStarEquivalence A f).toAdjunction

end Topos

section Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f]

/-- **Topological invariance of étale cohomology**, [Stacks 03SI]: a universal
homeomorphism `f : X ⟶ Y` induces an isomorphism on étale cohomology in every degree. -/
@[stacks 03SI]
noncomputable def Etale.cohomologyEquiv
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Sheaf.H F n ≃+ Sheaf.H (((f)^*[AddCommGrpCat.{u + 1}]).obj F) n :=
  sorry

end Cohomology

end AlgebraicGeometry
