/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleExtContinuityFinite
/-! Algebraic-closure coefficient Ext continuity on a Noetherian quasi-compact scheme.

Source: blueprint `sk-lem-constructible-ext-continuity`, clause (1).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The degree-zero filtered-colimit factorization of `Ext` out of constant-model
constructible sheaves, for `ℚ̄_ℓ` coefficients, on a locally Noetherian quasi-compact scheme.
Source: blueprint `sk-lem-constructible-ext-continuity`, clause (1).

Proof: the `ℚ̄_ℓ` case of `constantModelExtContinuity_of_isLocallyNoetherian`; the
underlying `constructible_sheaf_ext_continuity` reduces to finite subextensions. -/
theorem padicAlgCl_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] [IsCommMonObj (Profinite.padicAlgClRingObj ℓ)]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    ConstantModelExtContinuity (Profinite.padicAlgClRingObj ℓ) X :=
  constantModelExtContinuity_of_isLocallyNoetherian ℓ ⟨⊥, inferInstance⟩
    (Profinite.padicAlgClCondensedRing ℓ) (Or.inr rfl) X

end AlgebraicGeometry.ProEtale
