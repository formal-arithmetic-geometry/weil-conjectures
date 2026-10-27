/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Jacobson.Ring
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen

/-!+# Positive degree gives a section with affine nonvanishing locus

Source: Stacks Project, Varieties, Tag 0B5X, `lemma-ample-curve`, second proof
paragraph, from "Assume degree positive" through the affine nonvanishing locus
(blueprint: lem-trf-positive-degree-affine-section).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module of positive degree on a proper integral curve over an arbitrary
field has a nonzero global section of a positive tensor power with affine nonvanishing
locus. The open `U` represents exactly the existing set `nonvanishingLocus`.

Source: Stacks Project, Varieties, Tag 0B5X, `lemma-ample-curve`, second proof paragraph
(blueprint: lem-trf-positive-degree-affine-section).

Proof, following the six steps of the node:
1. By lem-trf-proper-field-invertible-coherent, the curve is Noetherian and invertible
   modules are coherent. The underlying topology is Noetherian by
   lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. Integrality gives nonemptiness
   and irreducibility; lem-sc-scheme-sober gives sobriety and the Kolmogorov property.
   Choose a nonempty affine open U by lem-weil-pbc-affine-opens-basis. Its complement
   is finite by lem-sc-nonempty-open-complement-finite-dim-le-one, and consists of
   closed points by lem-sc-dim-one-point-outside-open-closed.
2. Properness includes finite type. On finite-type affine charts the boundary residue
   fields are finite over k by lem-weil-pbc-zariski-lemma. Let B be the sum of their
   k-dimensions; the empty sum is zero.
3. Put d = deg(N) > 0 and a = chi(O_C). Tensor powers are invertible by
   lem-weil-pbc-invertible-pullback-tensor. The degree definition gives deg(O_C) = 0;
   induction using lem-trf-curve-degree-tensor-additive gives deg(N^m) = md and hence
   chi(N^m) = md + a for every m >= 0.
4. By lem-pc-euler-characteristic-well-defined the coherent cohomology is finite
   dimensional. By lem-sc-noetherian-cohomology-above-dimension it vanishes above one.
   Since H^0 is global sections (pqf-def-cohomology), h^0(N^m) >= md + a. Choose
   n = B + |a| + 1 >= 1; since d is a positive integer, h^0(N^n) > B.
5. Evaluate global sections at the finitely many boundary points. The rank-one fibre
   description of def-sc-invertible-module makes the target dimension B. The dimension
   inequality gives a nonzero vector s in the kernel, so s vanishes at every boundary
   point. This uses injectivity and dimension, not surjectivity of evaluation.
6. By def-weil-pbc-ample-invertible-module, the nonvanishing locus C_s is contained in
   U. Lemma lem-sc-affine-cap-section-open makes U intersect C_s affine. This intersection
   is C_s, giving the required positive exponent, nonzero section, and affine open. -/
theorem exists_nonzero_section_affine_of_degree_pos
    (k : Type u) [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
    [IsIntegral C] [IsProper (C ↘ Spec (.of k))]
    (hdim : topologicalKrullDim C = (1 : WithBot ℕ∞))
    (N : C.Modules) [N.IsInvertible] (hdeg : 0 < N.degree k) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : (N.tensorPow n).val.presheaf.obj (Opposite.op ⊤),
      s ≠ 0 ∧ ∃ U : C.Opens, IsAffineOpen U ∧
        (U : Set C) = nonvanishingLocus (N.tensorPow n) s := by
  sorry

end AlgebraicGeometry.Scheme.Modules
