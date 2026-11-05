/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GenericBaseChange

/-!

# Generic base change along a structure morphism

Let `X` and `Y` be separated `k`-schemes of finite type and
```
P ──p₁──▶ X
│ p₂       │ a_X
▼          ▼
Y ──a_Y──▶ Spec k
```
a cartesian square. Its base change morphism `La_Y^* Ra_X_* ⟶ Rp₂_* Lp₁^*` on
`Dᵇc(-)⟦ℚ̲̄_ℓ⟧` is an isomorphism
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isPullback_toPoint`).

The square is the horizontal pasting of the square
```
P ──(p₂, p₁)──▶ Y ⨯ X
│ p₂              │ 𝟙 × a_X
▼                 ▼
Y ──(𝟙, a_Y)──▶ Y ⨯ Spec k
```
whose horizontal maps are isomorphisms, with the product square
`ProEtale.CondensedRing.commSq_prodMap_snd (a_X)`, whose base change morphism is an isomorphism by
generic base change (`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_prodMap`).

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isPullback_toPoint`: generic
  base change along `Y ⟶ Spec k` for any cartesian square over the base point.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y P : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

end AlgebraicGeometry.ProEtale.CondensedRing
