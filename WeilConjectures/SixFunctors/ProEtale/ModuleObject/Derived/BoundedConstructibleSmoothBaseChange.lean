/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!

# Smooth base change for bounded constructible `ℚ̄_ℓ`-complexes

For a commutative square
```
X' --u--> X
|         |
p'        p
v         v
Y' --v--> Y
```
of separated `k`-schemes of finite type, the *base change map* of the derived pushforward,
`Lv^* Rp_* ⟶ Rp'_* Lu^*` on the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧`, is
`ProEtale.CondensedRing.boundedConstructibleBaseChange`. This file states smooth base change for
it at `Λ = ℚ̲̄_ℓ`.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_smooth`: **smooth
  base change** for `Λ = ℚ̲̄_ℓ`, blueprint `sk-thm-sbc-coefficients` (section
  `sec-six-functors-basics`): for a cartesian square with `v` smooth, the base change map is an
  isomorphism on bounded constructible complexes.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {p : X ⟶ Y} {v : Y' ⟶ Y} {p' : X' ⟶ Y'} {u : X' ⟶ X}

/-- **Smooth base change** for bounded constructible `ℚ̄_ℓ`-complexes (blueprint
`sk-thm-sbc-coefficients`, section `sec-six-functors-basics`, at the coefficient ring `ℚ̄_ℓ`):
for a cartesian square with `v` smooth, the base change map `Lv^* Rp_* K ⟶ Rp'_* Lu^* K` is an
isomorphism for every bounded constructible `K`. -/
theorem isIso_boundedConstructibleBaseChange_of_smooth (sq : IsPullback u p' p v)
    [Smooth v.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleBaseChange ℓ
      sq.toCommSq).app K) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
