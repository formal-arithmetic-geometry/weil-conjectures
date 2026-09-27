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

Three statements of the six-functor bookkeeping that the purity chapter uses: the composition
isomorphism `Rg_! Rf_! ≅ R(g ∘ f)_!`, the identification `Rf_! ≅ Rf_*` for proper `f`, and the
mate of the composition isomorphism, `R(g ∘ f)^! ≅ Rf^! Rg^!`.

The compactification-independence that makes `Rf_!` well defined is already in the
repository, as
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`
together with its identity and composition coherences; it is not restated here.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar`
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y S : Scheme.{u}}

/-- Blueprint `sk-thm-sf-comp-composition`: The composition law for `Rf_!`

**The composition law.** For `f : X ⟶ Y` and `g : Y ⟶ S` separated of finite type there is a
canonical isomorphism

`Rg_! ∘ Rf_! ≅ R(g ∘ f)_!`

of functors `D(X_ét) ⥤ D(S_ét)`, independent of all compactification choices by the
coherence of the compactification comparisons, equal to the identity when `f` or `g` is an
identity, and associative for a third morphism. -/
theorem nonempty_iso_rightDerivedLowerShriek_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (R(f)_![A] ⋙ R(g)_![A] ≅ R(f ≫ g)_![A]) :=
  sorry

/-- Blueprint `sk-prop-sf-comp-proper`: Proper coincidence

**Proper coincidence.** For `f : X ⟶ Y` proper the identity is a compactification of `f`, and
the resulting canonical identification

`Rf_! ≅ Rf_*`

is independent of the compactification. Under it the exchange `Ex_!` is the proper-base-change
exchange `Ex_*`, so that compact-support base change specializes to proper base change.

At the level of sheaves this is `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`; the
statement here is its derived counterpart. -/
theorem nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar (f : X ⟶ Y)
    [HasCompactification f] [IsProper f] :
    Nonempty (R(f)_![A] ≅ R((f)_*[A])) :=
  sorry

/-- Blueprint `sk-lem-sf-mate`: Mate calculus for a pasted adjunction

**The mate of the composition isomorphism.** For composable `f : X ⟶ Y` and `g : Y ⟶ S`, the
mate of the composition isomorphism `R(g ∘ f)_! ≅ Rg_! Rf_!` is the isomorphism

`R(g ∘ f)^! ≅ Rf^! ∘ Rg^!`,

and the units and counits of the composite adjunctions are the pasted ones: the functoriality
of the mate construction turns an isomorphism of left adjoints into one of right adjoints, and
the triangle identities of a composite adjunction are the composites of the component ones. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (R(f ≫ g)^![A] ≅ R(g)^![A] ⋙ R(f)^![A]) :=
  sorry

end Etale

end AlgebraicGeometry
