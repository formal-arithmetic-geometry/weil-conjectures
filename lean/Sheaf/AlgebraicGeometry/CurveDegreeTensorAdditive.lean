/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CurveEulerTensorGenericRank
import Sheaf.AlgebraicGeometry.DegreeWeightedIrreducibleComponents
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# Additivity of line bundle degree on proper schemes of dimension at most one

Source: Stacks Project, Varieties, Tag 0AYX, `lemma-degree-tensor-product`,
specialized to two locally free sheaves of rank one
(blueprint: lem-trf-curve-degree-tensor-additive).

The scheme may be empty, disconnected, singular, or nonreduced. Degree is the existing
difference of Euler characteristics, and tensor is the existing sheaf tensor product.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The degree of the tensor product of two invertible modules on a proper scheme of
topological Krull dimension at most one over a field is the sum of their degrees.

Source: Stacks Project, Varieties, Tag 0AYX, rank-one specialization
(blueprint: lem-trf-curve-degree-tensor-additive).

Proof:
1. A proper scheme over a field is Noetherian: a field is Noetherian, its spectrum is
   Noetherian, and a finite-type scheme over a Noetherian scheme is Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Invertible modules are quasi-coherent
   and of finite type, hence coherent by pqf-lem-coherent-ft-locnoeth. The same holds
   for the proper integral components below.
2. The tensor of the two invertible modules is invertible by
   lem-weil-pbc-invertible-pullback-tensor. Apply
   lem-trf-degree-weighted-irreducible-components to both factors and their tensor.
   All three degrees are sums over the same one-dimensional reduced irreducible
   components, weighted by the same finite generic lengths. Isolated zero-dimensional
   components and embedded points require no additional term.
3. On each component, pull back both factors by the closed immersion. They remain
   invertible, and the second factor is coherent of generic rank one. Apply
   lem-trf-curve-euler-tensor-generic-rank to obtain chi(L tensor M) = deg(L) + chi(M).
   Subtract chi(O) to get degree additivity on that component. The pullback/tensor
   comparison of lem-weil-pbc-invertible-pullback-tensor identifies this tensor with
   the restriction of the original tensor; isomorphic sheaves have the same Euler
   characteristic and degree (def-pc-euler-characteristic, def-pc-degree-line-bundle).
4. Substitute these component identities into the weighted sum and distribute the
   finite sum in the integers. If there are no one-dimensional components, including
   when the scheme is empty, all three sums and all three degrees are zero. -/
theorem degree_tensorObj_of_topologicalKrullDim_le_one
    (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X ≤ 1)
    (L M : X.Modules) [L.IsInvertible] [M.IsInvertible] :
    (L ⊗ M).degree k = L.degree k + M.degree k := by
  sorry

end AlgebraicGeometry.Scheme.Modules
