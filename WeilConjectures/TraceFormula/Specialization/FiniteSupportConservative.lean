/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# Direct image is conservative on finite support

Let `q : Y ⟶ B` be a morphism of separated `k`-schemes of finite type and `T ⊆ Y` a closed subset
finite over `B`. A bounded constructible `ℚ̄_ℓ`-complex `E` on `Y` supported on `T` with
`Rq_* E = 0` vanishes
(`ProEtale.CondensedRing.isZero_of_isZero_rightDerivedLowerStar_of_isFinite`). This is the node
`det-sp-constant-family-conservative` of the blueprint subsection `sk-lem-tf-sp-constant-family`,
stated here for `ℚ̄_ℓ`-coefficients as an input of the proof of blueprint
`det-sp-zero-section-affine-space`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Direct image is conservative on finite support** (blueprint
`det-sp-constant-family-conservative`, a node of the subsection `sk-lem-tf-sp-constant-family`, for
`ℚ̄_ℓ`-coefficients): let `q : Y ⟶ B` be a morphism of separated `k`-schemes of finite type and
`T ⊆ Y` a closed subset finite over `B`, given as the image of a morphism `t : T' ⟶ Y` with
`T' ⟶ B` finite. If `E` is bounded constructible on `Y` and supported on `T` (every point outside
`T` has an open neighbourhood on which `E` vanishes) and `Rq_* E = 0`, then `E = 0`. -/
theorem isZero_of_isZero_rightDerivedLowerStar_of_isFinite {Y B : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (q : Y ⟶ B)
    {T : Scheme.{u}} (t : T ⟶ Y.left) [IsFinite (t ≫ q.left)]
    (E : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hE : ∀ y ∉ Set.range t.base, ∃ (V : Scheme.{u}) (g : V ⟶ Y.left), IsOpenImmersion g ∧
      y ∈ Set.range g.base ∧
      IsZero ((L((g)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj E.obj))
    (hq : IsZero ((R((q.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj E.obj)) :
    IsZero E.obj :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
