/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cohomology of finite projective complexes over coherent rings

Source: Stacks Project, More on Algebra, Lemma 0EWZ and Algebra, Lemma 05CX
(blueprint: lem-sc-coherent-ring-perfect-complex-cohomology).

The complex here is the affine module complex mentioned in `def-pc-perfect-complex`,
not its associated complex of sheaves. Coherence is expressed by the defining ideal
condition of Stacks, Algebra, Definition 10.90.1 (section Tag 05CU).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Every cohomology module of a bounded complex of finite projective modules over a
commutative coherent ring is finitely presented.
Source: Stacks Project, More on Algebra, Lemma 0EWZ; Algebra, Lemmas 05CW and 05CX
(blueprint: lem-sc-coherent-ring-perfect-complex-cohomology).

Proof: Each term is finitely presented by
`lem-weil-pbc-finite-projective-finitely-presented`. Apply
`lem-sc-coherent-ring-fp-kernel-cokernel` to the differentials: their kernels (cycles)
and images (boundaries) are finitely presented. The differential squares to zero, so
boundaries include into cycles. Apply the same closure lemma to that inclusion; its
cokernel, the cohomology module, is finitely presented. This is also the strictly
perfect specialization of 0EWZ, using 05CX to identify coherent and finitely presented
modules. -/
theorem finitePresentation_homology_of_coherent
    {R : Type u} [CommRing R]
    (hR : ∀ I : Ideal R, I.FG → Module.FinitePresentation R I)
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hterms : ∀ n : ℤ, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n))
    (q : ℤ) : Module.FinitePresentation R (P.homology q) := by
  sorry

end CochainComplex
