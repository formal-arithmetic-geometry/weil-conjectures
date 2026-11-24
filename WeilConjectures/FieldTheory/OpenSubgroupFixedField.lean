/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open subgroups and finite separable fixed fields

## Main results

- `openSubgroup_fixedField_finite_separable`: open subgroups of the absolute Galois group have
  finite separable fixed fields and finite discrete coset spaces, and point stabilizers of finite
  transitive discrete continuous Galois sets are open with finite separable fixed fields.

## Implementation details

Both parts use the infinite Galois correspondence for the open (hence closed) subgroup;
compactness of the Krull topology makes the coset space finite and openness makes it discrete.

## References

* Stacks Project, Tags 03QR and 03SF, with the Galois correspondence in Tag 0BML.
-/

@[expose] public section

universe u v w

/-- For an open subgroup of the absolute Galois group, the fixed field is finite and separable,
and its fixing subgroup is the original subgroup. The quotient is finite and discrete;
its left translation action is continuous. Conversely, a point in a finite transitive
discrete continuous G-set has open stabilizer, whose fixed field is finite separable. -/
theorem openSubgroup_fixedField_finite_separable
    (K : Type u) (Ks : Type v) [Field K] [Field Ks] [Algebra K Ks]
    [IsSepClosure K Ks] :
    (∀ H : Subgroup Gal(Ks/K), IsOpen (H : Set Gal(Ks/K)) →
      FiniteDimensional K (IntermediateField.fixedField H) ∧
      Algebra.IsSeparable K (IntermediateField.fixedField H) ∧
      (IntermediateField.fixedField H).fixingSubgroup = H ∧
      Finite (Gal(Ks/K) ⧸ H) ∧ DiscreteTopology (Gal(Ks/K) ⧸ H) ∧
      ContinuousSMul Gal(Ks/K) (Gal(Ks/K) ⧸ H)) ∧
    (∀ (X : Type w) [TopologicalSpace X] [DiscreteTopology X] [Finite X]
      [MulAction Gal(Ks/K) X] [ContinuousSMul Gal(Ks/K) X]
      [MulAction.IsPretransitive Gal(Ks/K) X] (x : X),
      IsOpen (MulAction.stabilizer Gal(Ks/K) x : Set Gal(Ks/K)) ∧
      FiniteDimensional K
        (IntermediateField.fixedField (MulAction.stabilizer Gal(Ks/K) x)) ∧
      Algebra.IsSeparable K
        (IntermediateField.fixedField (MulAction.stabilizer Gal(Ks/K) x))) := by
  have forward : ∀ H : Subgroup Gal(Ks/K), IsOpen (H : Set Gal(Ks/K)) →
      FiniteDimensional K (IntermediateField.fixedField H) ∧
      Algebra.IsSeparable K (IntermediateField.fixedField H) ∧
      (IntermediateField.fixedField H).fixingSubgroup = H ∧
      Finite (Gal(Ks/K) ⧸ H) ∧ DiscreteTopology (Gal(Ks/K) ⧸ H) ∧
      ContinuousSMul Gal(Ks/K) (Gal(Ks/K) ⧸ H) := by
    intro H hH
    have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
      InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩
    have hfinite : FiniteDimensional K (IntermediateField.fixedField H) :=
      (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hfix]; exact hH)
    exact ⟨hfinite, inferInstance, hfix, H.quotient_finite_of_isOpen hH,
      QuotientGroup.discreteTopology hH, inferInstance⟩
  refine ⟨forward, ?_⟩
  intro X _ _ _ _ _ _ x
  have hopen := stabilizer_isOpen Gal(Ks/K) x
  exact ⟨hopen, (forward _ hopen).1, (forward _ hopen).2.1⟩
