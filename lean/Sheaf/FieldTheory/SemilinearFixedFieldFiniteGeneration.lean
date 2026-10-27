/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite generation of fixed fields for compatible finite actions

Source: Stacks Project, Fields, Tags 09I3 and 09GH; Algebra, Tag 00IK;
agent extraction for de Jong, Lemma 5.2 proof, p. 613
(blueprint: lem-sfb-semilinear-fixed-field-finite-generation).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- Compatible finite actions on a finitely generated field extension induce a finitely
 generated extension between the fixed fields. The last existential bundles E^H as an
 intermediate field over k^H; its underlying subfield is specified exactly, so the algebra
 structure is the one induced by the original inclusion k → E.

Source: Stacks Project, Fields, Tag 09I3 (lemma-galois-over-fixed-field) and Tag 09GH
(lemma-algebraic-finitely-generated); Algebra, Tag 00IK (lemma-Noetherian-basic).
Agent extraction for de Jong, Lemma 5.2 proof, p. 613
(blueprint: lem-sfb-semilinear-fixed-field-finite-generation).

Proof:
1. Compatibility sends each k^H-element into E^H. Fixed points are subfields because
   automorphisms preserve the field operations.
2. Apply lem-wf-finite-field-action-fixed-degree to the two finite automorphism images
   of H. Their fixed fields are unchanged, giving finite separable k/k^H and E/E^H.
   Thus neither original action has to be faithful.
3. By def-weil-finite-dimensional-subspace, choose a finite k^H-spanning family of k.
   Together with the given field generators of E/k it generates E/k^H: the field it
   generates contains the whole linear span k and hence E. Call this family z₁, …, z_N.
4. For each zᵢ, the product of T-b over its distinct H-orbit elements b is monic,
   has positive degree, vanishes at zᵢ and has H-fixed coefficients. Let S be the finite
   set of all these coefficients and C = k^H(S) ⊆ E^H. Each zᵢ is algebraic over C,
   and E = C(z₁, …, z_N). By lem-weil-pbc-algebraic-generators-finite-extension,
   E is finite-dimensional over C.
5. The field C is Noetherian (def-weil-pbc-noetherian-ring): a nonzero ideal contains
   a nonzero x and hence x⁻¹x = 1. The finite-dimensional E is a finite C-module
   (def-weil-finitely-generated-module). Its C-submodule E^H is finite by
   lem-weil-pbc-noetherian-submodule-finite. A finite C-spanning family b₁, …, b_m
   generates E^H as a field over C. Adjoining S and this family to k^H proves the claim.
-/
theorem semilinear_fixed_field_finite_generation
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    (hfg : (⊤ : IntermediateField k E).FG)
    (H : Type w) [Group H] [Finite H]
    [MulSemiringAction H k] [MulSemiringAction H E]
    (hcompat : ∀ (h : H) (a : k),
      h • algebraMap k E a = algebraMap k E (h • a)) :
    (∀ a : k, a ∈ FixedPoints.subfield H k →
      algebraMap k E a ∈ FixedPoints.subfield H E) ∧
    FiniteDimensional (FixedPoints.subfield H k) k ∧
    Algebra.IsSeparable (FixedPoints.subfield H k) k ∧
    FiniteDimensional (FixedPoints.subfield H E) E ∧
    Algebra.IsSeparable (FixedPoints.subfield H E) E ∧
    (⊤ : @IntermediateField (FixedPoints.subfield H k) E _ _
      (Algebra.compHom E (FixedPoints.subfield H k).subtype)).FG ∧
    ∃ F : @IntermediateField (FixedPoints.subfield H k) E _ _
        (Algebra.compHom E (FixedPoints.subfield H k).subtype),
      F.toSubfield = FixedPoints.subfield H E ∧ F.FG := by
  sorry

end Algebra
