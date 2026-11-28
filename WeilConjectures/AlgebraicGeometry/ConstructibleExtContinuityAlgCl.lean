/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleExtContinuityFinite
/-! Algebraic-closure coefficient Ext continuity on a locally Noetherian quasi-compact scheme.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- On a locally Noetherian quasi-compact scheme, maps out of a constant-model constructible
sheaf with `ℚ̄_ℓ` coefficients into a shifted filtered colimit factor through a stage. -/
theorem padicAlgCl_ext_continuity
    (ℓ : ℕ) [Fact ℓ.Prime] [IsCommMonObj (Profinite.padicAlgClRingObj ℓ)]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    ConstantModelExtContinuity (Profinite.padicAlgClRingObj ℓ) X :=
  constantModelExtContinuity_of_isLocallyNoetherian ℓ ⟨⊥, inferInstance⟩
    (Profinite.padicAlgClCondensedRing ℓ) (Or.inr rfl) X

end AlgebraicGeometry.ProEtale
