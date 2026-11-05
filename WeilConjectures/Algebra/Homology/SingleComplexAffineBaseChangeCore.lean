/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.Algebra.Homology.AffineBaseChangeCohomologyModel
import Mathlib.RingTheory.LocalProperties.Exactness

/-! # The affine single-complex base-change criterion

Source: Stacks Project, Tag 0DJ8, affine proof, and Tag 0DJ9
(blueprint: lem-pc-rf-single-complex-affine-base-change).

The affine case of the single-complex criterion, stated with the objects of the
qcqs statement `singleComplexBaseChangeQcqsInduction`: a cartesian square of the
spectra S = Spec R, X = Spec A, S' = Spec R', X' = Spec A', objects K, K' of the
quasi-coherent derived categories (which correspond to complexes M, N of A- and
A'-modules under the affine equivalence), a derived morphism L(g')^*K -> K', the
stalkwise condition `SingleComplexBaseChange.StalkCondition`, and the derived
base-change comparison map followed by Rf'_* of the given morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
