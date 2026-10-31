/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ReductionLowerShriekShift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# The counit of the derived extension of scalars commutes with shifts

Let `Ψ = - ⊗ᴸ_Λ Λ'` be the derived extension of scalars along a surjective ring morphism with
principal kernel (`AlgebraicGeometry.Etale.derivedExtendScalars`), with the commutation with the
shifts induced, as a left adjoint, by the one of the restriction of scalars. Its counit
`Qh ⋙ Ψ ⟶ K(Λ' ⊗_Λ -) ⋙ Qh` commutes with the shifts
(`AlgebraicGeometry.Etale.commShift_derivedExtendScalarsCounit`). By
`CategoryTheory.Functor.commShift_leftDerivedTensorComparisonApp`, this is what is needed for the
tensor comparison `Ψ(K ⊗ᴸ M) ⟶ Ψ K ⊗ᴸ Ψ M` to commute with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory

-- the instances used in the definition of the derived tensor product of étale sheaves
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u})

/-- The counit `Qh ⋙ Ψ ⟶ K(Λ' ⊗_Λ -) ⋙ Qh` of the derived extension of scalars commutes with the
shifts. -/
instance commShift_derivedExtendScalarsCounit :
    NatTrans.CommShift (derivedExtendScalarsCounit hρ ha X) ℤ :=
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  (Sheaf.extendScalarsAdjunction X.smallEtaleTopology
    ρ).commShift_leftDerivedFunctorCounit_of_adjunction

end AlgebraicGeometry.Etale
