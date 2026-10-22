/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.CommonTensorComparisonDescent
import Sheaf.Paper.RationalComparisonValid
import Sheaf.Paper.CommonTensorComparisonConstruction

/-! # Tensor comparisons through rationalization and common finite fields

Source: Weil blueprint, main-20261015, order 1826, final coefficient paragraph,
and order 1868; the conditional descent argument of the DAG
(blueprint: lem-sf-tensor-comparison-localization-descent).

All raw localizations and common-stage quotients below are the existing constructions.
The auxiliary records only organize the hypotheses and the normalized conclusions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u c h

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace WeilConjectures.TensorComparisonDescent

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

variable {l Ω}
  (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear
      (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]

/-- Tensor comparisons descend through raw rationalization and the actual common-stage
categories with exactly their specified component formulas.
Source: blueprint main-20261015, orders 1826 and 1868; the conditional argument in the DAG
(blueprint: lem-sf-tensor-comparison-localization-descent).

Proof, following the eleven DAG steps:
1. Use lem-sf-perfect-scalar-tensor-coherence for the integer-to-field maps, integer
   inclusions and rational squares. Its bounded finite-projective models give bounded
   finite-dimensional cohomology over each field.
2. Extend composition and tensor pairings by def-weil-module-base-change. On pure tensors
   interchange and associativity are multiplication of scalars. Extend constraints by one.
3. The balanced map a tensor f maps to a times B(F(f)); the tensor universal property
   gives functoriality, first on pure tensors and then on sums.
4. Compose B(tau) with the balanced scalar tensorator. Naturality, signed symmetry,
   associativity and both unitors follow from the integral and balanced diagrams.
5. Extend transitions and their comparisons on pure tensors. The balanced identification
   of the two scalar towers gives phi and its identity, tower, tensor and unit equations.
6. Conjugate representatives by phi inverse at the source and phi at the target. Its
   tower equation proves compatibility with transport. The field comparison, normalized
   on every complex, identifies derived B with the termwise field scalar functor and the
   tower of lem-weil-derived-field-scalar-extension-tower. Cancellation proves functor laws.
7. Construct tensors at common fields. The transition tensorator and two tower maps give
   d. Monoidality of the towers gives its cocycle. This proves independence of tensor
   representatives. Represent constraints at one larger field, where their diagrams hold.
8. Expand gamma_L F_L(d) phi_inverse. The scalar tensor square and the two phi tower
   equations identify it with B(gamma_K) e. For incomparable fields use a further compositum.
9. Naturality of tau and phi at one common field gives naturality on classes. Equal
   representatives become equal at a further stage, so the formula is independent of them.
10. The rational scalar unit square identifies the unit from every base field, including
    repeated fields using their specified identity isomorphisms.
11. Move every finite constraint diagram to one common field. The rational associativity,
    Koszul symmetry and both unit diagrams commute there, hence in the Hom colimits.
    Inverse representatives prove invertibility. No full faithfulness is assumed. -/
theorem tensor_comparison_localization_descent (A : IntegralData C) (hA : A.Valid) :
    ∃ rs : RationalStructures C,
      letI := rs
      ∃ R : RationalData C A, RationalData.Valid C A R ∧
        ∃ cs : CommonStructures R,
          letI := cs
          ∃ M : CommonData R, M.Valid := by
  let rs := rationalStructures C
  let R := rationalDatum A hA
  have hR : RationalData.Valid C A R := rationalDatum_valid A hA
  obtain ⟨cs, hcs⟩ := common_tensor_comparison_construction (C := C) A R hR
  exact ⟨rationalStructures C, R, hR, cs, hcs⟩

end WeilConjectures.TensorComparisonDescent
