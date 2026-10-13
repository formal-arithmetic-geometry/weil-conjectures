/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs

/-!

# The compactly supported base change theorem for constructible `E`- and `ℚ̄_ℓ`-sheaves

Let `ℓ` be a prime and `E` a finite extension of `ℚ_ℓ`, with condensed ring `E̲ = C(-, E)`
(`Profinite.continuousMapRingObj E`). Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`.
This file deduces from the proper base change theorem
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper`) and base change
for extension by zero
(`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`)
that the compact-support base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`

on the bounded constructible derived categories of `E`-sheaves, and of `ℚ̄_ℓ`-sheaves for the
condensed ring `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`, is an isomorphism, where
`c' = c.baseChange sq`. No properness is imposed on `f` itself: the properness enters only
through the structure morphism `p` of the compactification.

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes are
separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all
morphisms are morphisms over `Spec k`. The compactification `Z` of `f` and its base change
`Z ×_Y Y'` are then separated and of finite type over `k` as well
(`WeilConjectures.Compactification.Over`).

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekBaseChange`: the base change
  theorem for the compactly supported direct image of bounded constructible `E`-sheaves.
- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl`: the same
  for bounded constructible `ℚ̄_ℓ`-sheaves.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [f.IsOver (Spec (.of k))]
  [g.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

include ℓ k in
/-- **The base change theorem for the compactly supported direct image** of bounded
constructible `E`-sheaves, `E` a finite extension of `ℚ_ℓ`: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`, the compact-support base-change morphism
`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` is an isomorphism of functors
`Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`, where `c' = c.baseChange sq`. In the defining composite, the
direct-image exchange is an isomorphism by proper base change for the proper structure
morphism `p`, and the extension-by-zero exchange is an isomorphism by base change for
extension by zero. -/
theorem isIso_boundedConstructibleLowerShriekBaseChange (c : Compactification f)
    (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekBaseChange
      (Profinite.continuousMapRingObj E) ℓ k c sq) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper ℓ E k (c.baseChange_isPullback_g sq)
  rw [boundedConstructibleLowerShriekBaseChange_eq]
  infer_instance

/-- **The base change theorem for the compactly supported direct image** of bounded
constructible `ℚ̄_ℓ`-sheaves: for a cartesian square of schemes `sq : IsPullback g' f' f g` and a
compactification `c` of `f`, the compact-support base-change morphism
`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}` is an isomorphism of functors
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̲̄_ℓ⟧`, where `c' = c.baseChange sq`. -/
theorem isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl (c : Compactification f)
    (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekBaseChange
      (Profinite.padicAlgClRingObj ℓ) ℓ k c sq) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ k
    (c.baseChange_isPullback_g sq)
  rw [boundedConstructibleLowerShriekBaseChange_eq]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
