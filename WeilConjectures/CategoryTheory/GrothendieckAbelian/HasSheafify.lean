/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Affine
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!

# Sheafification on the small sites (sorried)

Sheafification exists for `A`-valued presheaves on the small `Q`-sites of `P`-schemes,
for a Grothendieck abelian category `A` with `Hom`-types in the universe `u` of the base
schemes.

## The smallness hypothesis

The small sites are **not** essentially small, not even the small étale site: for
`X = Spec ℤ` and any type `I : Type u` the fold map `∐_{i : I} X ⟶ X` is étale (it is an
isomorphism on each component of the coproduct, and `@Etale` is local at the source), and
for infinite `I` the underlying set of `∐_{i : I} X` has cardinality `#I`, so
non-equinumerous `I` give non-isomorphic objects of `X.Etale`. Its skeleton therefore
surjects onto the infinite cardinals of `Cardinal.{u}`, which is not `Small.{u}`
(`not_small_cardinal`). Only the small *affine* étale site is essentially small
(`AlgebraicGeometry.Scheme.AffineEtale`, `Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`),
because an affine scheme étale over `S` is `Spec` of a ring of bounded cardinality.

What the plus-construction actually needs is therefore not smallness of the site but an
essentially small **dense subsite**, and that is what the affine slice provides:
`Mathlib.AlgebraicGeometry.Sites.Affine` shows, for any `P` that is multiplicative,
Zariski-local at the source, stable under base change and satisfies
`P.HasOfPostcompProperty P`, that

* `AlgebraicGeometry.Scheme.isCoverDense_toOver_Spec` — the affine slice
  `P.CostructuredArrow ⊤ Scheme.Spec U` is cover-dense in `P.Over ⊤ U`, and
* `AlgebraicGeometry.Scheme.isOneHypercoverDense_toOver_Spec` — it is even
  one-hypercover-dense, so the two sheaf categories are equivalent,

and `AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec` shows the affine slice is
essentially small as soon as `P ≤ @LocallyOfFiniteType`. Accordingly the instance below
carries `[IsZariskiLocalAtSource P]` and
`[EssentiallySmall.{u} (MorphismProperty.CostructuredArrow P ⊤ Scheme.Spec U)]`; both hold
for `P = @Etale` (the latter by
`AlgebraicGeometry.Scheme.essentiallySmall_costructuredArrow_spec_etale`), and the second
fails for `P = ⊤`, which is what rules out the reading of the statement under which it is
false.

The remaining mathematical content of the sorry is then: for an essentially small site and
a Grothendieck abelian `A`, the plus-construction sheafifies and is left exact. Mathlib
proves this only for a *concrete* `A` with the forgetful functor preserving limits and
filtered colimits and reflecting isomorphisms; see
`Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`, whose `HasSheafify` instances are the
concrete-coefficient counterpart of the two instances below.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Sheafification for `A`-valued presheaves on the small `Q`-site of `P`-schemes over a
scheme `U`, for a Grothendieck abelian coefficient category `A` with `Hom`-types in the
universe `u` of the base schemes: the affine slice of the site is an essentially small
dense subsite (see the module docstring) and `A` is complete and cocomplete with exact
filtered colimits, so the plus-construction applies there and is left exact. -/
instance (priority := high) hasSheafify_smallGrothendieckTopology (A : Type u')
    [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [IsZariskiLocalAtSource P]
    (U : Scheme.{u})
    [EssentiallySmall.{u} (MorphismProperty.CostructuredArrow P ⊤ Scheme.Spec U)] :
    HasSheafify (U.smallGrothendieckTopology Q (Q := P)) A :=
  sorry

/-- Sheafification for `A`-valued presheaves on the small étale site: the instance above
specialized to `P = Q = @Etale`. -/
instance (priority := high) hasSheafify_smallEtaleTopology (A : Type u')
    [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A] (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology A :=
  inferInstanceAs (HasSheafify (X.smallGrothendieckTopology (P := @Etale) (Q := @Etale)) A)

end CategoryTheory.GrothendieckTopology
