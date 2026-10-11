/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Open subgroups and finite separable fixed fields

Source: Stacks Project, Tags 03QR and 03SF, with the Galois correspondence in Tag 0BML
(blueprint: lem-exc-etale-open-subgroup-fixed-field).
-/

universe u v w

/-- (blueprint: lem-exc-etale-open-subgroup-fixed-field) Stacks, Tags 03QR and 0BML.
For an open subgroup of the absolute Galois group, the fixed field is finite and separable,
and its fixing subgroup is the original subgroup. The quotient is finite and discrete;
its left translation action is continuous. Conversely, a point in a finite transitive
discrete continuous G-set has open stabilizer, whose fixed field is finite separable.

For the first clause, apply the fixed-field Galois correspondence to the open (hence closed)
subgroup, as in `lem-exc-etale-open-subgroup-fixed-field-galois`. Compactness of the Krull
topology makes its coset space finite, while openness makes that space discrete, as in
`lem-exc-etale-open-subgroup-quotient-finite-discrete`. For the converse, continuity on a
discrete set makes the point stabilizer open; apply the fixed-field correspondence again. -/
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
  sorry
