/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Continuous linear retraction onto a finite p-adic subfield

Source: Weil blueprint, main-20261015, `sec-six-functors-basics`,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), arithmetic expansion
(blueprint: lem-sfb-finite-subfield-continuous-linear-retraction).

The closure has its extended norm, and intermediate fields carry the induced norm topology.
Writing the upper field as an intermediate field over the lower one encodes their inclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Padic

/-- A finite intermediate field of the normed algebraic closure admits a continuous
linear retraction over any finite intermediate coefficient subfield.

Source: Weil blueprint, main-20261015, `sec-six-functors-basics`,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), arithmetic expansion
(blueprint: lem-sfb-finite-subfield-continuous-linear-retraction).

Proof:
1. The restriction of the extended norm to E is its unique extending p-adic absolute
   value (lem-weil-l-adic-extension-absolute-value). E is complete
   (lem-weil-l-adic-extension-complete), nontrivially normed since the norm of l is
   l inverse (def-weil-l-adic-numbers), and proper
   (lem-weil-l-adic-extension-proper). Any two elements of the closure lie in a common
   finite subextension (def-weil-finite-subextension-directed-set), where the strong
   triangle inequality holds, so the ambient norm is ultrametric.
2. Choose an E-basis of F. Its coordinate maps F to E are continuous by
   lem-sfb-finite-dimensional-linear-map-continuous. The topology on F is the subspace
   topology from the closure because its norm is the restriction of the same norm.
3. Extend each coordinate map continuously to the closure by
   lem-sfb-proper-ultrametric-scalar-extension. The hypotheses follow from step 1;
   this extension theorem requires no completeness of the ambient vector space.
4. Sum the extended coordinates times their basis vectors. Each summand is continuous
   into F, and the finite sum is E-linear and continuous. On F the original coordinate
   expansion gives the identity. No multiplicativity, equivariance or norm bound is asserted.
-/
theorem exists_finiteSubfield_continuousLinearRetraction
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : IntermediateField (Padic l) Ω) [FiniteDimensional (Padic l) E]
    (F : IntermediateField E Ω) [FiniteDimensional (Padic l) F] :
    ∃ p : Ω →L[E] F, ∀ a : F, p (a : Ω) = a := by
  sorry

end Padic
