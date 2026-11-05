/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!

# Lower shriek along a morphism admitting a compactification

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.LowerShriek.Defs`.

For a morphism `f : X ⟶ Y` together with a compactification `X ⟶[i] Z ⟶[g] Y` (`i` an
open immersion, `g` proper), the lower shriek on small pro-étale sites is the composition
`f_! := i_! ⋙ g_*` of the extension by zero along `i` with the pushforward
`AlgebraicGeometry.ProEtale.lowerStar` along `g`.

## Main definitions

- `AlgebraicGeometry.ProEtale.Compactification.lowerShriek`: the lower shriek `i_! ⋙ g_*`
  associated with a compactification `X ⟶[i] Z ⟶[g] Y` of `f`.
- `AlgebraicGeometry.ProEtale.lowerShriek`: the lower shriek `f_!` of a morphism `f`
  satisfying `HasCompactification f`, *definitionally* equal to the composition associated
  with the chosen compactification `HasCompactification.compactification f`, see
  `ProEtale.lowerShriek_eq`.

## Main results

- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_lowerShriek`: the lower shriek `f_!`
  with values in an abelian category is left exact. This one needs sheafification to be
  *exact*, not merely to exist.

## Implementation notes

- The pushforward `g_*` of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` is
  defined along the base change functor, which exists for an *arbitrary* morphism `g` — in
  contrast to the localization functor `MorphismProperty.Over.map ⊤ h` of
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`, which
  requires `WeaklyEtale g`. This is essential for compactifications, whose structure morphism is
  proper and in general is not weakly étale.
- The open immersion of a compactification is weakly étale, being étale, so the extension
  by zero along it is available; the Kan extension it needs exists because an open immersion
  is a monomorphism. Hence `f_!` carries no hypotheses beyond the standing assumptions
  on `A`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}}

namespace ProEtale

namespace Compactification

variable {f : X ⟶ Y} (c : Compactification f)

end Compactification

variable (f : X ⟶ Y) [HasCompactification f]

end ProEtale

--TODO: the composition isomorphism : `(fg)_! ≅ f_! g_!`

--TODO: invarience with choice of compcatification

end AlgebraicGeometry
