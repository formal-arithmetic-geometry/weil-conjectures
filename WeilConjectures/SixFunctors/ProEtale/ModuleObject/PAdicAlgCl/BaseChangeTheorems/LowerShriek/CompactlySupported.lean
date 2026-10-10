/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.BaseChangeTheorems.LowerShriek.MorphismDefs

/-!

# The base change theorem for the lower shriek on bounded constructible module objects

Let `ℓ` be a prime and fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`.
This file deduces from the proper base change theorem
(`ProEtale.PadicAlgClRing.isIso_boundedConstructibleBaseChange_of_isProper`) and base change
for extension by zero
(`ProEtale.PadicAlgClRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`)
that the compact-support base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`

on the bounded constructible derived categories of module objects over `ℚ̄_ℓ,X` is an
isomorphism, where `c' = c.baseChange sq`. No properness is assumed on `f` itself: the
properness enters only through the structure morphism `p` of the compactification. This is
the base change theorem for the compactly supported direct image of `ℚ̄_ℓ`-sheaves.

## Main statements

- `ProEtale.PadicAlgClRing.isIso_boundedConstructibleLowerShriekBaseChange`: the base change
  theorem for the lower shriek on bounded constructible complexes.

-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

variable {X Y X' Y' : Scheme.{u}}
  [NoetherianSpace X] [NoetherianSpace Y] [NoetherianSpace X'] [NoetherianSpace Y']
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The base change theorem for the lower shriek** on bounded constructible module objects over
`ℚ̄_ℓ`: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`, the compact-support base-change morphism
`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` is an isomorphism of functors
`Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̄_ℓ⟧`, where `c' = c.baseChange sq`. In the defining composite, the
direct-image exchange is an isomorphism by proper base change for the proper structure
morphism `p`, and the extension-by-zero exchange is an isomorphism by base change for
extension by zero. -/
theorem isIso_boundedConstructibleLowerShriekBaseChange (c : Compactification f)
    (sq : IsPullback g' f' f g) [NoetherianSpace c.Z] [NoetherianSpace ↥(pullback c.g g)] :
    IsIso (boundedConstructibleLowerShriekBaseChange ℓ c sq) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper ℓ (c.baseChange_isPullback_g sq)
  rw [boundedConstructibleLowerShriekBaseChange_eq]
  infer_instance

end AlgebraicGeometry.ProEtale.PadicAlgClRing
