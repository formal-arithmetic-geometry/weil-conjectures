/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilHomClosedStructure

/-! # Pointwise left adjoints of native derived internal Hom

## Implementation details

The left adjoint is constructed on the Frobenius ringed action-site realization: for a fixed
native derived object `K`, total relative tensor with a K-flat flat-term representative of
`K` descends to the derived category, and the tensor--Hom adjunction on complexes, combined
with the native-to-standard row-sign conversion, identifies its right adjoint with the
native product-total Hom. No boundedness, constructibility or nonzero-object assumption
enters.

## References

* Stacks Project, Tags 06YS, 08J9 and 0A97
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Every fixed-source native derived internal Hom has a left adjoint. -/
theorem native_weil_hom_isRightAdjoint
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    (Prod.sectR (op K) _ ⋙ M.weilHom).IsRightAdjoint := by
  obtain ⟨S⟩ := native_weil_hom_closed_structure k₀ l X M
  let _ := S.monoidal
  exact (S.adjunction K).isRightAdjoint

end AlgebraicGeometry.ProEtaleWeilSheaf
