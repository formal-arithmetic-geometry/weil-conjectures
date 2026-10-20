/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.TraceFormula.AffineTwoTermDeterminantData

/-! # Determinants over affine schemes

Source: Stacks Project, More on Algebra, Tags 0FJI--0FJM.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
variable [d : ∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Good diagrams construct the determinant functor on affine schemes, compatibly
with arbitrary affine base change. Source: Stacks Project, More on Algebra, Tag 0FJM,
using Tags 0FJI--0FJL; Perfect Complexes, Tag 0FJY
(blueprint: lem-trf-affine-two-term-determinant).

Proof: on Spec A use finite projective two-term models. A bounded projective complex is
K-projective, so derived isomorphisms are homotopy classes of chain quasi-isomorphisms.
For a map a:P→Q choose a finite free surjection F→Q⁻¹. Adjoin the contractible complex
[F→F] to P; projection b to P and the map c to Q given in degrees -1 and 0 by
(a⁻¹,p) and (a⁰,d_Q p) are surjective quasi-isomorphisms, and c is homotopic to ab.
The map on determinant lines is T_c T_b⁻¹, where T is the kernel-normalized map.
The degreewise fibre product of two such diagrams is finite projective and gives a
diagram for the composite. The calculus composition law gives multiplication of their
maps. A diagram for the identity has homotopic legs and gives the identity. Composing
with a fixed diagram for a homotopy inverse then proves independence of diagrams;
a homotopy of a leaves its diagram admissible, proving homotopy independence.
Thus these maps define a functor on the derived core, transported along models.
The determinant modules are invertible by their local top exterior descriptions,
including varying ranks and rank zero. On the identity complex the map to zero is
contraction with det(1), hence evaluation after the displayed symmetry.
For A→B, tensoring the split term sequences preserves their kernels and the acyclic
kernel differential. The exact-sequence wedge formula, its inverse dual, and evaluation
commute with scalar extension. Therefore every T_c T_b⁻¹ does too. On pure wedge tensors
the identity and two successive scalar extensions agree with the direct extension.
This proves naturality and both pullback equations, with the fixed recorded derived
comparisons: finite projective complexes are K-flat, so their ordinary scalar extension
computes derived extension with those counits. The affine derived equivalence and
pullback/tensor comparison identify these constructions with the asserted sheaf data.
No flatness assumption is made on A→B. The zero ring is covered by the same formulas. -/
theorem exists_affineTwoTermDeterminantData
    [∀ (X : Scheme.{u}) (U : X.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (κ : TwoTermDeterminantPullbackCoherence.{u, w}) :
    Nonempty (AffineTwoTermDeterminantData κ) := by
  sorry

end AlgebraicGeometry
