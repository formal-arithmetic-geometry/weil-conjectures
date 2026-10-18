/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne

/-!
# Base change along `X ×_K S ⟶ S` for morphisms of finite type `K`-schemes

Let `K` be a field, `Λ` a finite ring whose exponent is invertible in `K`, `X` a Noetherian
`K`-scheme and `γ : T ⟶ S` a separated morphism of schemes of finite type over `K`. For a
constructible sheaf `F` of `Λ`-modules on `T`, the base-change maps of the cartesian square

```
X ×_K T --e--> T
   |           |
   h           γ
   v           v
X ×_K S --p--> S
```

are isomorphisms in every degree
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_finiteType`). Factor `γ` as an open
immersion `j : T ⟶ T̄` followed by a proper `T̄ ⟶ S` (Nagata). Deligne's generic base change
theorem over the base `Spec K`, whose only nonempty open is everything, says that `Rj_* F`
commutes with the base change along `X ×_K T̄ ⟶ T̄`; the proper base change theorem says that
`R(T̄ ⟶ S)_*` commutes with the base change along `X ×_K S ⟶ S`; and the base-change maps of a
vertical composite of squares compose.

This is the finite-type case of blueprint `lem-kun-0f1i`, replacing the open-immersion lemma
`lem-kun-0f1h` of the blueprint by Deligne's theorem.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Base change along `X ×_K S ⟶ S` for a separated morphism `γ : T ⟶ S` of schemes of finite
type over a field `K`, a Noetherian `K`-scheme `X` and a constructible sheaf of `Λ`-modules,
`Λ` finite with exponent invertible in `K`. -/
theorem Etale.isIso_baseChangeHomologyMap_of_finiteType [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X S T X' Y : Scheme.{u}} [IsNoetherian X]
    (aX : X ⟶ Spec (.of K)) (aS : S ⟶ Spec (.of K)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (γ : T ⟶ S) [LocallyOfFiniteType γ] [QuasiCompact γ] [IsSeparated γ]
    (b : X' ⟶ X) (p : X' ⟶ S) (_hb : IsPullback b p aX aS)
    (e : Y ⟶ T) (h : Y ⟶ X') (sq : IsPullback e h γ p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsConstructibleSheaf F] (q : ℤ) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

end AlgebraicGeometry
