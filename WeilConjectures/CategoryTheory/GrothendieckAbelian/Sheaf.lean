/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!

# The sheaf categories on the small sites are Grothendieck abelian (sorried)

Following the convention of the `SixFunctors` folder, the coefficient category `A` of the
sheaf categories is a Grothendieck abelian category with `Hom`-types in the universe `u`
of the base schemes; this covers the intended applications `A = Ab.{u}` and
`A = ModuleCat.{u} Λ`. The instance below is stated for the small sites defined by a
general morphism property `P`, under the assumptions `[P.IsMultiplicative]`,
`[P.IsStableUnderBaseChange]` and `[P.HasOfPostcompProperty P]`; all of them hold for
`P = @Etale`.

## Sorried instance

- `CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_smallGrothendieckTopology`:
  the category of `A`-valued sheaves on the small `Q`-site of `P`-schemes is Grothendieck
  abelian: the site is essentially small for the étale-like properties `P` of interest, so
  `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall` applies.

Neither of the two Mathlib results is usable here directly. The general instance
`CategoryTheory.Sheaf` instance for Grothendieck abelian sheaf categories requires the site
to be a *small* category `C : Type v` with `Category.{v} C`, while the small sites of
`P`-schemes live in `Type (u + 1)` with `Hom`-types in `Type u`. The étale-specific
instance `AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology` is
stated for a *concrete* `A` (with the forgetful functor preserving limits and filtered
colimits and reflecting isomorphisms), assumptions the `SixFunctors` folder does not
impose. The mathematical content of the instance below does not use concreteness of `A`;
its binders are written out explicitly (rather than taken from a `variable` block), so
that the hypotheses on `A` are part of the statement even though the `sorry` body does
not use them.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- The category of `A`-valued sheaves on the small `Q`-site of `P`-schemes over a scheme
`U` is Grothendieck abelian, for a Grothendieck abelian coefficient category `A` with
`Hom`-types in the universe `u` of the base schemes: the site is essentially small for
the étale-like properties `P` of interest, so
`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall` applies. For the small
étale sites and *concrete* `A` this is proved in Mathlib
(`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`). -/
instance isGrothendieckAbelian_sheaf_smallGrothendieckTopology (A : Type u')
    [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    IsGrothendieckAbelian.{u} (Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) :=
  sorry

/-- The instance above specialized to the small étale site and restated for
`AlgebraicGeometry.Scheme.smallEtaleTopology` itself: `smallEtaleTopology` is a
non-reducible `def`, so instance search does not see through it to fire
`isGrothendieckAbelian_sheaf_smallGrothendieckTopology` on goals phrased in terms of
`X.smallEtaleTopology`. -/
instance isGrothendieckAbelian_sheaf_smallEtaleTopology (A : Type u') [Category.{u} A]
    [Abelian A] [IsGrothendieckAbelian.{u} A] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology A) :=
  inferInstanceAs (IsGrothendieckAbelian.{u}
    (Sheaf (X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)) A))

end CategoryTheory.GrothendieckTopology
