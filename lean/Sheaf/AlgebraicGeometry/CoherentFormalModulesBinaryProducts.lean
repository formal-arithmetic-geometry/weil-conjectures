/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections

/-! # Binary products preserve coherent formal modules

Source: Stacks Project, Section 0EHN and Lemma 087X, binary-sum argument written out.
(blueprint: lem-weil-pbc-coherent-formal-finite-products-binary-products)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Binary products of coherent formal modules are coherent formal.
Source: Stacks Project, Cohomology of Schemes, Section 0EHN and Lemma 087X,
binary-sum argument written out.
(blueprint: lem-weil-pbc-coherent-formal-finite-products-binary-products).

Take the inverse system H with H_n = F_n ⊞ G_n and diagonal transition maps.
The coherent kernel/cokernel theorem gives coherence of H_n. On an affine open,
the ideal-times-quasi-coherent-affine-sections theorem identifies multiplication
by I^(n+1) on H_n with the sum of the two ideal products. Both summands vanish,
so the ideal product vanishes. The same section calculation identifies
H_(n+1)/I^(n+1)H_(n+1) with the sum of the two quotients. Their given transition
isomorphisms therefore give an isomorphism to H_n, whose composite with the
quotient projection is the diagonal transition map. These affine identities
glue because the maps are induced by the canonical inclusions and projections.
Products of module sheaves and inverse systems are computed termwise, and in
this abelian category binary products are biproducts. Thus H is an ambient
binary product. Any other limiting binary cone is uniquely isomorphic to H.
Transport termwise coherence through these isomorphisms, and ideal products
and cokernels by their universal properties, to prove the assertion for every
limiting binary cone, including when one or both factors are zero.
-/
theorem coherentFormalModules_closedUnderBinaryProducts (X : Scheme.{u})
    [IsNoetherian X] (I : X.IdealSheafData) :
    (IsCoherentFormalModule I).IsClosedUnderBinaryProducts := by
  sorry

end AlgebraicGeometry
