/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.FiniteSupportInduction

/-!

# Direct image is conservative on finite support

Let `q : Y ⟶ B` be a morphism of separated `k`-schemes of finite type and `T ⊆ Y` a closed subset
finite over `B`. A bounded constructible `ℚ̄_ℓ`-complex `E` on `Y` supported on `T` with
`Rq_* E = 0` vanishes
(`ProEtale.CondensedRing.isZero_of_isZero_rightDerivedLowerStar_of_isFinite`). This is the node
`det-sp-constant-family-conservative` of the blueprint subsection `sk-lem-tf-sp-constant-family`,
stated here for `ℚ̄_ℓ`-coefficients as an input of the proof of blueprint
`det-sp-zero-section-affine-space`.

The subset `T`, the image of a morphism `t : T' ⟶ Y` finite over `B`, is closed; give it the
structure of the scheme-theoretic image `u : T₀ ⟶ Y` of `t`.
As `E` vanishes on the open complement (a finite union of the given neighbourhoods), the
open–closed triangle gives `E ≅ Ru_* Lu^* E`, so `R(u ≫ q)_* Lu^* E ≅ Rq_* E = 0`. The morphism
`u ≫ q` is proper with finite fibres, hence finite, and finite direct image is conservative
(`ProEtale.CondensedRing.isZero_of_isZero_lowerStar_of_isFinite`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

end AlgebraicGeometry.ProEtale.CondensedRing
