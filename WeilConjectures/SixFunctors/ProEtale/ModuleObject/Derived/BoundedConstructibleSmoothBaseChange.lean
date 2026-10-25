/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
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
`Lv^* Rp_* ⟶ Rp'_* Lu^*` on the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧`
(`ProEtale.CondensedRing.boundedConstructibleLowerStarBaseChange`), is the mate of the
pullback comparison `Lp'^* Lv^* ≅ Lu^* Lp^*` under the adjunctions `Lp^* ⊣ Rp_*` and
`Lp'^* ⊣ Rp'_*`.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarBaseChange_of_smooth`: **smooth
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

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [IsFinitenessCoefficient ℓ Λ]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {p : X ⟶ Y} {v : Y' ⟶ Y} {p' : X' ⟶ Y'} {u : X' ⟶ X}

/-- The *base change map* `Lv^* Rp_* ⟶ Rp'_* Lu^*` of a commutative square `u ≫ p = p' ≫ v` on
bounded constructible complexes: the mate of the pullback comparison `Lp'^* Lv^* ≅ Lu^* Lp^*`
(`boundedConstructiblePullbackSquareComparison`) under `Lp^* ⊣ Rp_*` and `Lp'^* ⊣ Rp'_*`. At `K`
it is the adjoint of `Lp'^* Lv^* Rp_* K ≅ Lu^* Lp^* Rp_* K ⟶ Lu^* K`. -/
noncomputable def boundedConstructibleLowerStarBaseChange (sq : CommSq u p' p v) :
    boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleUpperStar Λ ℓ v ⟶
      boundedConstructibleUpperStar Λ ℓ u ⋙ boundedConstructibleLowerStar Λ ℓ p' :=
  mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom

/-- **Smooth base change** for bounded constructible `ℚ̄_ℓ`-complexes (blueprint
`sk-thm-sbc-coefficients`, section `sec-six-functors-basics`, at the coefficient ring `ℚ̄_ℓ`):
for a cartesian square with `v` smooth, the base change map `Lv^* Rp_* K ⟶ Rp'_* Lu^* K` is an
isomorphism for every bounded constructible `K`. -/
theorem isIso_boundedConstructibleLowerStarBaseChange_of_smooth (sq : IsPullback u p' p v)
    [Smooth v.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((boundedConstructibleLowerStarBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq).app K) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
