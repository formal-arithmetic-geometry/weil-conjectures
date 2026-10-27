/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocusDual
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity

/-!
# Nonzero line bundle maps and tensor-dual degree

Source: Stacks Project, Varieties, Tag 0B40, proof of (5), and Tag 0AYX,
`lemma-degree-tensor-product`, in rank one
(blueprint: lem-sfb-curve-nonzero-line-map-degree).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A map of line bundles is canonically a section of the target tensor the source dual.
The additive isomorphism below is linear over `Γ(C, ⊤)`: multiplication by a function `r`
on a morphism is postcomposition with `B.smulHom r`.

Its defining equation uses the existing canonical `Hom.adjointSection`: the inverse of
`dualEvaluation A` followed by `φ` tensored with the identity of the dual. In local bases
`φ(e_A) = h e_B`, this is exactly the section `h e_B ⊗ e_A^∨`.

The dual and tensor-dual are invertible, evaluation is an isomorphism, and their degrees
are respectively `-deg A` and `deg B - deg A`. A nonzero map gives a nonzero section and
nonnegative tensor-dual degree.

Source: Stacks Project, Varieties, Tag 0B40, proof of (5), and Tag 0AYX, rank one
(blueprint: lem-sfb-curve-nonzero-line-map-degree).

Proof:
1. Apply lem-pc-tensor-dual-invertible: the dual, the tensor-dual and the canonical
   evaluation have the asserted invertibility properties.
2. Trivialize A and B on a common Zariski cover. Send the local coefficient h of a map
   to h e_B tensor e_A-dual. Under e_A' = u e_A and e_B' = v e_B, the coefficient becomes
   u v-inverse h and the dual basis becomes u-inverse e_A-dual. The tensor section is
   unchanged, so the sections glue. Reverse this construction for the inverse. Both
   constructions preserve addition and multiplication by functions. They agree with
   the inverse evaluation defining Hom.adjointSection. Thus zero corresponds to zero.
3. Degree of the structure sheaf is zero. Apply lem-trf-curve-degree-tensor-additive
   to A and its dual, and use evaluation. The isomorphism and its inverse induce
   inverse maps on each cohomology group, hence preserve Euler characteristic and
   degree. This gives degree of the dual equals minus degree of A. Apply tensor
   additivity to B and the dual of A for the second identity. Dimension one implies
   dimension at most one, as needed by tensor additivity.
4. For a nonzero map the section from Step 2 is nonzero. Apply
   lem-trf-curve-section-degree-positivity to the invertible tensor-dual bundle on the
   integral proper curve C to obtain its nonnegative degree. -/
theorem curve_nonzero_line_map_degree
    (k : Type u) [Field k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsIntegral C] [IsProper (C ↘ Spec (.of k))] (hC : topologicalKrullDim C = 1)
    (A B : C.Modules) [A.IsInvertible] [B.IsInvertible] :
    (dual A).IsInvertible ∧ (B ⊗ dual A).IsInvertible ∧
      IsIso (dualEvaluation A) ∧
      (dual A).degree k = -A.degree k ∧
      (B ⊗ dual A).degree k = B.degree k - A.degree k ∧
      ∃ E : (A ⟶ B) ≃+ Γ(B ⊗ dual A, ⊤),
        (∀ (r : Γ(C, ⊤)) (φ : A ⟶ B), E (φ ≫ B.smulHom r) = r • E φ) ∧
        (∀ φ : A ⟶ B,
          homOfGlobalSection (B ⊗ dual A) (E φ) = Hom.adjointSection φ) ∧
        (∀ φ : A ⟶ B, φ ≠ 0 → E φ ≠ 0 ∧ 0 ≤ (B ⊗ dual A).degree k) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
