/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib

/-!

# Sheafification on the small sites (sorried)

Following the convention of the `SixFunctors` folder, the coefficient category `A` of the
sheaf categories is a Grothendieck abelian category with `Hom`-types in the universe `u`
of the base schemes; this covers the intended applications `A = Ab.{u}` and
`A = ModuleCat.{u} Λ`. The instance below is stated for the small sites defined by a
general morphism property `P`, under the assumptions `[P.IsMultiplicative]`,
`[P.IsStableUnderBaseChange]` and `[P.HasOfPostcompProperty P]`; all of them hold for
`P = @Etale`.

## Sorried instance

- `CategoryTheory.GrothendieckTopology.hasSheafify_smallGrothendieckTopology`:
  sheafification for `A`-valued presheaves on the small `Q`-sites of `P`-schemes: the
  sites are essentially small and the Grothendieck abelian `A` is complete and cocomplete
  with exact filtered colimits, so the plus-construction applies and is left exact. For
  the small étale sites and *concrete* `A` this is proved in Mathlib.

The instance is stated for any Grothendieck abelian `A` — its mathematical content does
not use concreteness of `A` — and with its binders written out explicitly (rather than
taken from a `variable` block), so that the hypotheses on `A` are part of the statement
even though the `sorry` body does not use them.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Sheafification for `A`-valued presheaves on the small `Q`-site of `P`-schemes over a
scheme `U`, for a Grothendieck abelian coefficient category `A` with `Hom`-types in the
universe `u` of the base schemes: the site is essentially small for the étale-like
properties `P` of interest and `A` is complete and cocomplete with exact filtered
colimits, so the plus-construction applies and is left exact. For the small étale sites
and *concrete* `A` this is proved in Mathlib
(`Mathlib/AlgebraicGeometry/Sites/AffineEtale.lean`). -/
instance hasSheafify_smallGrothendieckTopology (A : Type u') [Category.{u} A] [Abelian A]
    [IsGrothendieckAbelian.{u} A] (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (U : Scheme.{u}) :
    HasSheafify (U.smallGrothendieckTopology Q (Q := P)) A :=
  sorry

end CategoryTheory.GrothendieckTopology
