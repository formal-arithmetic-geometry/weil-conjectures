/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper

/-!
# The composition law for `Rf_!` and its mate

Two statements of the six-functor bookkeeping that the purity chapter uses: the
identification `Rf_! ≅ Rf_*` for proper `f`, and the mate of the composition isomorphism,
`R(g ∘ f)^! ≅ Rf^! Rg^!`. The composition isomorphism `R(g ∘ f)_! ≅ Rf_! ⋙ Rg_!` itself is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, in
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`.

The compactification-independence that makes `Rf_!` well defined is already in the
repository, as
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`
together with its identity and composition coherences; it is not restated here.

## Implementation notes

Each statement below records only the *existence* of the isomorphism it names. The unit and
associativity coherences of `sk-thm-sf-comp-composition`, and the assertion of `sk-lem-sf-mate`
that `R(gf)^! ≅ Rf^! Rg^!` is the *mate* of the composition isomorphism, cannot be phrased in
that form; they need the isomorphism as a `def`, which in turn needs the comparison maps of
the framework chapter. This is the same gap as the TODO already recorded in
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y S : Scheme.{u}}

/-- Blueprint `sk-prop-sf-comp-proper`: Proper coincidence

**Proper coincidence.** For `f : X ⟶ Y` proper the identity is a compactification of `f`, and
the resulting canonical identification

`Rf_! ≅ Rf_*`

is independent of the compactification.

At the level of sheaves this is `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`, which
states that the *canonical comparison* `f_! ⟶ f_*` is an isomorphism; the derived comparison
map has not been constructed, so only the existence of the derived isomorphism is recorded
here. -/
theorem nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar (f : X ⟶ Y)
    [HasCompactification f] [IsProper f] :
    Nonempty (R(f)_![A] ≅ R((f)_*[A])) :=
  sorry

/-- Blueprint `sk-lem-sf-mate`: Mate calculus for a pasted adjunction

**The mate of the composition isomorphism.** For composable `f : X ⟶ Y` and `g : Y ⟶ S`,

```
  R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!           (left adjoints, sk-thm-sf-comp-composition)
        ⊣              ⊣
  R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!           (right adjoints, the mate)
```

the mate of the composition isomorphism is an isomorphism `R(g ∘ f)^! ≅ Rf^! ∘ Rg^!`: the
functoriality of the mate construction turns an isomorphism of left adjoints into one of right
adjoints, and the triangle identities of a composite adjunction are the composites of the
component ones. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (R(f ≫ g)^![A] ≅ R(g)^![A] ⋙ R(f)^![A]) :=
  sorry

end Etale

end AlgebraicGeometry
