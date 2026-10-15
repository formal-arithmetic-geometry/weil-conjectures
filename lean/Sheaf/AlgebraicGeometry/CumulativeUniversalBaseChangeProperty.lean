/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso

/-!
# The cumulative universal base-change property

Source: blueprint, sec-smooth-base-change/sk-def-bc/sbc-def-base-change-property.md;
Stacks Project, Tag 0F02, Remark `remark-base-change-holds`
(blueprint: sbc-def-base-change-property).

The fixed-degree condition is the existing `Etale.BaseChangeProperty`, specialized to
`ULift.{u + 1} (ZMod n)`. Its universal form is `Etale.UniversalBaseChangeProperty`.
The fixed-base cumulative form is `∀ r : ℕ, r ≤ q → BaseChangeProperty Λ f (r : ℤ)`.
Only the cumulative universal condition needs a new name.

The lift of the coefficient ring is solely the size convention for module sheaves.
Sheaves of modules over this ring are exactly abelian sheaves annihilated by `n`.
The positivity and invertibility assumptions restrict the definition to the coefficient
conventions of `Etale.IsSmoothBaseChangeCoefficients`; the ring is automatically finite
and annihilated by `n`.

The Cartesian squares in the existing predicates are expressed using `IsPullback`.
A `ChosenCartesianSquare h e f g` supplies this property, and a pullback square supplies
its canonical chosen identification with the fibre product. Thus the chosen identification
of the dependency does not impose any extra condition on the quantified squares.
The degreewise map is the dependency's existing bounded-below presentation
`Etale.baseChangeHomologyMap`, namely homology of the exchange on a sheaf in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The cumulative universal property `UBC^{≤q}(f,n)`: for each nonnegative degree at most
`q`, the degreewise base-change map is an isomorphism after every base change of `f`,
for every quasi-compact quasi-separated horizontal morphism and every `ZMod n`-module
sheaf. Those quantifiers and the map itself are the existing `UniversalBaseChangeProperty`
and `BaseChangeProperty`, with their existing `baseChangeHomologyMap`.
Here `n ≥ 1` and `n` is invertible on the base, as required by the coefficient conventions.
Source: blueprint, sec-smooth-base-change/sk-def-bc/sbc-def-base-change-property.md;
Stacks Project, Tag 0F02, Remark `remark-base-change-holds`
(blueprint: sbc-def-base-change-property). -/
def CumulativeUniversalBaseChangeProperty {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℕ) (_hn : 0 < n) (_hinv : IsUnit (n : Γ(S, ⊤))) (q : ℕ) : Prop :=
  ∀ r : ℕ, r ≤ q → UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (r : ℤ)

end AlgebraicGeometry.Etale
