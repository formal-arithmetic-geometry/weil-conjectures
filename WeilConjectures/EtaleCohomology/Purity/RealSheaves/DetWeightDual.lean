/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations
public import WeilConjectures.RepresentationTheory.Dual

/-!
# Determinant weights of the contragredient

Let `ρ` be a finite-dimensional Weil representation. The determinant of the contragredient is
`det(γ | ρ^∨) = det(γ | ρ)⁻¹`, so `dw_ι(ρ^∨) = -dw_ι(ρ)`
(`AlgebraicGeometry.WeilGroup.detWeight_dual`). The annihilators of a composition series of `ρ`
form a composition series of `ρ^∨` whose factors are the contragredients of those of `ρ`
(`Representation.CompositionSeries.exists_equiv_dual`), hence
`DW(ρ^∨) = -DW(ρ)`, with multiplicities (`AlgebraicGeometry.WeilGroup.detWeightMultiset_dual`).

## Main statements

- `AlgebraicGeometry.WeilGroup.detWeight_dual`: `dw_ι(ρ^∨) = -dw_ι(ρ)`.
- `AlgebraicGeometry.WeilGroup.detWeightMultiset_dual`: `DW(ρ^∨) = -DW(ρ)` (blueprint
  `proposition-determinant-weights-tensor-operations--3`).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]

namespace WeilGroup

variable {W : WeilGroup p} {l : ℕ} [Fact l.Prime] {V : Type u} [AddCommGroup V]
  [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
  (ρ : Representation (PadicAlgCl l) W.carrier V) (ι : PadicAlgCl l →+* ℂ)

/-- The determinant weight of the contragredient is the negative of the determinant weight:
`det(γ | ρ^∨) = det(γ | ρ)⁻¹` and `ρ^∨` has the same rank as `ρ`. -/
theorem detWeight_dual : W.detWeight l ρ.dual ι = -W.detWeight l ρ ι := by
  have hdet : LinearMap.det (ρ.dual W.frobeniusLift) = (LinearMap.det (ρ W.frobeniusLift))⁻¹ := by
    change LinearMap.det (ρ W.frobeniusLift⁻¹).dualMap = _
    rw [LinearMap.det_dualMap, ← Representation.coe_detCharacter_apply,
      ← Representation.coe_detCharacter_apply, map_inv, Units.val_inv_eq_inv_val]
  rw [detWeight, detWeight, hdet, frobeniusWeight_inv, Subspace.dual_finrank_eq, neg_div]

/-- Blueprint `proposition-determinant-weights-tensor-operations--3`: `DW(V^∨) = -DW(V)`.

The determinant weights of the composition factors of the contragredient `ρ^∨` of a
finite-dimensional Weil representation `ρ` are the negatives of those of `ρ`, with
multiplicities: the composition factors of `ρ^∨` are the contragredients of those of `ρ`
(`Representation.CompositionSeries.exists_equiv_dual`), and `dw_ι(A^∨) = -dw_ι(A)`
(`AlgebraicGeometry.WeilGroup.detWeight_dual`). -/
theorem detWeightMultiset_dual :
    W.detWeightMultiset l ρ.dual ι = (W.detWeightMultiset l ρ ι).map Neg.neg := by
  let s := ρ.exists_compositionSeries.some
  let c := ρ.dual.exists_compositionSeries.some
  obtain ⟨e, he⟩ := s.exists_equiv_dual c
  change (Finset.univ : Finset (Fin c.length)).val.map (fun j ↦ W.detWeight l (c.factor j) ι) =
    ((Finset.univ : Finset (Fin s.length)).val.map
      fun i ↦ W.detWeight l (s.factor i) ι).map Neg.neg
  rw [Multiset.map_map, ← Multiset.map_univ_val_equiv e, Multiset.map_map]
  refine Multiset.map_congr rfl fun j _ ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, ← detWeight_of_equiv ι (he j).some,
    detWeight_dual]

end WeilGroup

end AlgebraicGeometry
