/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteQuotientCoefficientLayerData
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Representative short exact sequence for the finite coefficient layer
Source: Stacks Project, sites-cohomology.tex, Tag 0942.
(blueprint: lem-weil-pbc-finite-quotient-coefficient-layer-triangle-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The flat representative and coefficient sequence underlying the coefficient-layer triangle.
The construction resolves the successor reduction by a flat-term K-flat complex, tensors the
actual kernel-unit-quotient sequence, and records the resulting degreewise short exact sequence.
The later triangle theorem only applies `triangleOfSES` and identifies the three representatives.

Source: Stacks Project, sites-cohomology.tex, Tag 0942, lemma-bounded, proof (1).
(blueprint: lem-weil-pbc-finite-quotient-coefficient-layer-triangle-core).
-/
theorem finiteQuotient_coefficient_layer_core
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) :
    ∃ S : ShortComplex (CochainComplex
      (SheafOfModules.{t + 1} (completedAdicFiniteRing X d (n + 1))) ℤ),
      S.ShortExact ∧
      Nonempty (finiteQuotientLayerObject X d M n ≅ DerivedCategory.Q.obj S.X₁) ∧
      Nonempty ((completedAdicQuotientReduction X d (n + 1)).obj M ≅
        DerivedCategory.Q.obj S.X₂) ∧
      Nonempty (finiteQuotientPreviousObject X d M n ≅ DerivedCategory.Q.obj S.X₃) := by
  sorry

end AlgebraicGeometry.Scheme
