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

Source: Stacks Project, Tags 03QR and 03SF, with the Galois correspondence in Tag 0BML.
-/

@[expose] public section

universe u v w

/-- For an open subgroup `H` of the absolute Galois group, the fixed field is finite and
separable, its fixing subgroup is `H`, and the quotient by `H` is finite and discrete with a
continuous left translation action. Conversely, a point of a finite transitive discrete
continuous `G`-set has an open stabilizer, whose fixed field is finite separable.
Source: Stacks, Tags 03QR and 0BML. -/
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
