/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationProductExchangeDefs
import WeilConjectures.AlgebraicGeometry.CompactificationProductExchangeOpenIsIso
import WeilConjectures.AlgebraicGeometry.CompactificationProductExchangeProperIsIso

/-! # Invertibility of the compactification factors

A component of the compactification product-projection argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Fix the intrinsic pro-etale localization, which uses the standard derived category.
attribute [local instance 50000] proEtaleRingModules_hasDerivedCategory
/-- Both factors of compactification product exchange are invertible.

Source: latest blueprint det-tf-ibc-pasting.proof.md, steps 5 and 6.
(blueprint: compactification-product-exchange-pasting-isIso).

Proof: apply the proper-factor theorem at Rj_* M and the open-factor theorem at M,
using the explicit intermediate-geometry hypotheses, and return their conjunction. -/
theorem compactificationProductExchange_pasting_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k) (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, 0 < r ∧ ((l ^ r : ℕ) : A) = 0)
    (X Y T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (j : X ⟶ B) [IsOpenImmersion j.left] [QuasiCompact j.left]
    (p : B ⟶ Y) [IsProper p.left] (M : proEtaleDerivedCategory X.left A)
    (_hM : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} A) X.left) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X.left A).essImage M) :
    IsIso ((compactificationProductExchange A p T).app
      ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor.obj M)) ∧
    IsIso ((compactificationProductExchange A j T).app M) := by
  exact ⟨compactificationProductExchange_proper_isIso
      D l _hl _hne A _hA X Y T B j p M _hM,
    compactificationProductExchange_open_isIso D l _hl _hne A _hA X Y T B j p M _hM⟩

end AlgebraicGeometry.Scheme
