/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.Paper.FiniteQuotientCoefficientLayerData
import Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Paper.AdicCoefficientFiltration

/-! # The actual coefficient-layer triangle
Source: Stacks Project, Tag 0942.
(blueprint: lem-weil-pbc-finite-quotient-coefficient-layer-triangle).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Tensoring the actual coefficient short exact sequence gives the required triangle.
No local model, support bound, or finiteness of cohomology is assumed or asserted.

Source: Stacks Project, sites-cohomology.tex, Tag 0942, lemma-bounded, proof (1).
(blueprint: lem-weil-pbc-finite-quotient-coefficient-layer-triangle).

Proof: The quotient of constant coefficient rings is locally the surjection
A/I^(n+2) -> A/I^(n+1). Its kernel is therefore the actual sheaf kernel used in
finiteQuotientLayerObject. Take a flat-term K-flat resolution of M, extend its
scalars to A/I^(n+2), and tensor with the kernel-unit-quotient sequence. Flatness
makes this a short exact sequence of complexes, giving a distinguished triangle.
The derived tensor representative comparison identifies the first term with the
specified layer object. The unit tensor isomorphism identifies the middle term
with the successor reduction. Associativity of scalar extension, normalized by
the unit and counit on pure tensors, identifies the third term with the previous
reduction restricted to the successor ring. The equality of the completed
projection followed by a quotient with the previous projection makes this the
actual previous object. Transport the triangle along these isomorphisms. Neither
finite-perfect local models nor any cohomology calculation enters this step. -/
theorem finiteQuotient_coefficient_layer_triangle
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) :
    ∃ T : Triangle (DerivedCategory (SheafOfModules.{t + 1}
      (completedAdicFiniteRing X d (n + 1)))),
      T ∈ distTriang _ ∧
      Nonempty (T.obj₁ ≅ finiteQuotientLayerObject X d M n) ∧
      Nonempty (T.obj₂ ≅ (completedAdicQuotientReduction X d (n + 1)).obj M) ∧
      Nonempty (T.obj₃ ≅ finiteQuotientPreviousObject X d M n) := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    finiteQuotient_coefficient_layer_core X d M n
  let T := DerivedCategory.triangleOfSES hS
  refine ⟨T, DerivedCategory.triangleOfSES_distinguished hS, ?_, ?_, ?_⟩
  · exact ⟨e₁.symm⟩
  · exact ⟨e₂.symm⟩
  · exact ⟨e₃.symm⟩

end AlgebraicGeometry.Scheme
