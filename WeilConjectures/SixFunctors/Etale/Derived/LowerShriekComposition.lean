/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# A chosen composition isomorphism for `Rf_!`

The blueprint's composition law `α_{f,g} : R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` (`sk-thm-sf-comp-composition`)
is a specific isomorphism, built from compactifications of `f`, `g` and `f ≫ g` and proper base
change. That construction is not formalised. Instead this file *chooses* one isomorphism
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`), from the statement that one exists
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`), and builds everything
downstream from this choice.

The choice is made once, so all the maps built from it are mutually compatible, but it is
*not* the blueprint's `α_{f,g}`: nothing ties it to compactifications, it need not be the
identity when `f` or `g` is, and it need not be associative. Statements whose blueprint form is
about the canonical `α_{f,g}` hold for this choice only up to such a discrepancy, and are stated
here only when they do not depend on it. The definitions built from the choice are
`@[no_expose]`, so that nothing downstream unfolds them.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`: the chosen `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIso`: the induced
  `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`, the conjugate of the chosen isomorphism under the adjunctions
  `Rf_! ⊣ Rf^!` (`sk-lem-sf-mate` (b)).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y S : Scheme.{u}}

namespace Etale

/-- Blueprint `sk-thm-sf-comp-composition`: The composition law for `Rf_!`

For composable `f : X ⟶ Y` and `g : Y ⟶ S` admitting compactifications, with `f ≫ g` admitting
one as well, `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`. The blueprint constructs a canonical isomorphism
`α_{f,g}`: compactify `g` as `Y ⟶ Ȳ ⟶ S` and `v ∘ f` as `X ⟶ X̄ ⟶ Ȳ`, and use proper base change
for `X̄ ×_Ȳ Y`. Only the existence is stated here. -/
theorem nonempty_iso_rightDerivedLowerShriek_comp (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Nonempty (R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]) :=
  sorry

/-- **A chosen composition isomorphism** `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`, an arbitrary choice among
the isomorphisms that `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`
provides. It stands in for the blueprint's canonical `α_{f,g}` (`sk-thm-sf-comp-composition`);
see the module docstring for what is and is not known about it. -/
@[no_expose]
noncomputable def rightDerivedLowerShriekCompIso (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A] :=
  Classical.choice (nonempty_iso_rightDerivedLowerShriek_comp A f g)

/-- Blueprint `sk-lem-sf-mate`: Mate calculus for a pasted adjunction

*Clause (b).* The composition isomorphism `c_{f,g} : R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` of the exceptional
inverse images: the conjugate, under `R(f ≫ g)_! ⊣ R(f ≫ g)^!` and the composite adjunction
`Rf_! ⋙ Rg_! ⊣ Rg^! ⋙ Rf^!`, of the chosen composition isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`. Its units and counits are the pasted
ones. It depends on the choice made in `rightDerivedLowerShriekCompIso`. -/
@[no_expose]
noncomputable def rightDerivedUpperShriekCompIso (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    R(f ≫ g)^![A] ≅ R(g)^![A] ⋙ R(f)^![A] :=
  conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (f ≫ g))
    ((rightDerivedUpperShriekAdjunction A f).comp (rightDerivedUpperShriekAdjunction A g))
    (rightDerivedLowerShriekCompIso A f g).symm

end Etale

end AlgebraicGeometry
