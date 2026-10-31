/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.ProjectiveOfFlatOfNilpotentQuotient

/-! # Flat quotients with projective reductions and split completed sequences

Source: Stacks Project, Algebra, Tag 05D3, `lemma-split-completed-sequence`
(blueprint: lem-trf-flat-projective-reduction-completion-splitting).
-/

universe u v w z

open scoped TensorProduct

@[expose] public section

namespace Module

/-- A flat quotient with projective reduction gives a split exact sequence after completion.

Source: Stacks Project, Algebra, Tag 05D3, `lemma-split-completed-sequence`
(blueprint: lem-trf-flat-projective-reduction-completion-splitting).

Proof: At each positive adic level, tensor the original short exact sequence with the
corresponding quotient of the ring and identify the tensor products with module quotients.
Flatness gives levelwise exactness.  The quotient of the flat module is flat, and its
reduction modulo the nilpotent image of the ideal is the assumed projective module; the
nilpotent lifting lemma therefore makes every level projective.  Projectivity lifts the
identity through each levelwise surjection, inductively choosing compatible sections.
Their componentwise inverse-limit map is an `R`-linear section of the completed quotient.
The levelwise injections and exactness pass to the inverse limit by compatibility of the
components, yielding injectivity and equality of image with kernel for the completed maps.
-/
theorem flat_projective_reduction_completion_splitting
    (R : Type u) [CommRing R] (I : Ideal R)
    (K : Type v) [AddCommGroup K] [Module R K]
    (E : Type w) [AddCommGroup E] [Module R E]
    (M : Type z) [AddCommGroup M] [Module R M]
    (u : K →ₗ[R] E) (v : E →ₗ[R] M)
    (hu : Function.Injective u) (hv : Function.Surjective v)
    (h_exact : LinearMap.range u = LinearMap.ker v)
    [Module.Flat R M]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Function.Injective (AdicCompletion.map I u) ∧
      Function.Surjective (AdicCompletion.map I v) ∧
      LinearMap.range (AdicCompletion.map I u) = LinearMap.ker (AdicCompletion.map I v) ∧
      ∃ s : AdicCompletion I M →ₗ[R] AdicCompletion I E,
        (LinearMap.restrictScalars R (AdicCompletion.map I v)).comp s =
          LinearMap.id := by
  sorry

end Module

end
