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
import Sheaf.Analysis.Normed.Module.ProperUltrametricScalarExtension
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.NumberTheory.Padics.ProperSpace
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
  classical
  let : NormedAlgebra E Ω :=
    { norm_smul_le c x := norm_mul_le (c : Ω) x }
  let : IsUltrametricDist Ω := IsUltrametricDist.of_normedAlgebra (Padic l)
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra (Padic l)
  let : CompleteSpace E := FiniteDimensional.complete (Padic l) E
  let : ProperSpace E := FiniteDimensional.proper (Padic l) E
  let : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite (Padic l) E F
  let W : Submodule E Ω := F.toSubalgebra.toSubmodule
  let b := Module.finBasis E F
  let f : Fin (Module.finrank E F) → W →L[E] E :=
    fun i ↦ (b.coord i).toContinuousLinearMap
  have hext (i : Fin (Module.finrank E F)) :
      ∃ g : Ω →L[E] E, ∀ w : W, g (w : Ω) = f i w :=
    ContinuousLinearMap.exists_extension_of_proper_ultrametric (K := E) (V := Ω)
      (NormedField.exists_norm_lt_one E) W (f i)
  choose g hg using hext
  let p : Ω →L[E] F := ∑ i, (g i).smulRight (b i)
  refine ⟨p, fun a ↦ ?_⟩
  change (∑ i, (g i).smulRight (b i)) (a : Ω) = a
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  simp only [hg _ (show W from a)]
  exact b.sum_repr a

end Padic
