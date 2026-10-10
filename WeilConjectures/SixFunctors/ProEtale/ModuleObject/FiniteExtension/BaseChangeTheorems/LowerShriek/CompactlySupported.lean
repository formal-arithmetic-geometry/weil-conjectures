/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.BaseChangeTheorems.LowerShriek.MorphismDefs

/-!

# The base change theorem for the lower shriek on bounded constructible module objects

Let `T` be a commutative topological ring and fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`.
This file deduces from the proper base change theorem
(`ProEtale.ContinuousMapRing.isIso_boundedConstructibleBaseChange_of_isProper`) and base change
for extension by zero
(`ProEtale.ContinuousMapRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`)
that the compact-support base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`

on the bounded constructible derived categories of module objects over `A_X(T) = C(-, T)` is an
isomorphism, where `c' = c.baseChange sq`. No properness is assumed on `f` itself: the
properness enters only through the structure morphism `p` of the compactification. For
`T = E` this is the base change theorem for the compactly supported direct image of `E`-sheaves.

## Main statements

- `ProEtale.ContinuousMapRing.isIso_boundedConstructibleLowerShriekBaseChange`: the base change
  theorem for the lower shriek on bounded constructible complexes.

-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

variable {X Y X' Y' : Scheme.{u}}
  [NoetherianSpace X] [NoetherianSpace Y] [NoetherianSpace X'] [NoetherianSpace Y']
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The base change theorem for the lower shriek** on bounded constructible module objects over
`C(-, T)`: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`, the compact-support base-change morphism
`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` is an isomorphism of functors
`Dᵇc(X)⟦T⟧ ⥤ Dᵇc(Y')⟦T⟧`, where `c' = c.baseChange sq`. In the defining composite, the
direct-image exchange is an isomorphism by proper base change for the proper structure
morphism `p`, and the extension-by-zero exchange is an isomorphism by base change for
extension by zero. -/
theorem isIso_boundedConstructibleLowerShriekBaseChange (c : Compactification f)
    (sq : IsPullback g' f' f g) [NoetherianSpace c.Z] [NoetherianSpace ↥(pullback c.g g)] :
    IsIso (boundedConstructibleLowerShriekBaseChange T c sq) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper T (c.baseChange_isPullback_g sq)
  rw [boundedConstructibleLowerShriekBaseChange_eq]
  infer_instance

end AlgebraicGeometry.ProEtale.ContinuousMapRing
