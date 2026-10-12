/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Two nonvanishing loci represented in a common tensor degree

Source: Stacks Project, Properties, proof of Lemma 01PY and Lemma 01PT.
(blueprint: lem-weil-pbc-nonvanishing-common-degree)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Two sections of positive tensor powers can be replaced by sections of one invertible
module without changing either nonvanishing locus.

Source: Stacks Project, Properties, proof of Lemma 01PY, second paragraph, and Lemma 01PT.
(blueprint: lem-weil-pbc-nonvanishing-common-degree)

Proof: put `M = L.tensorPow (p * q)`. Tensor powers of an invertible module are invertible.
Take the q-fold tensor power of s and the p-fold tensor power of t, and transport them
along the canonical tensor-power multiplication isomorphisms (and p*q = q*p).
At each point the fibres of all these modules are one-dimensional vector spaces over
the residue field. A positive tensor power of a vector in a one-dimensional vector
space is nonzero exactly when that vector is nonzero: choose a basis and use that a
positive power of a field element is zero exactly when that element is zero.
The tensor-germ and fibre comparison maps identify the values of these sections with
those tensor powers. The fibre maps of the canonical isomorphisms are isomorphisms,
so they preserve nonzero values. This proves both asserted equalities of loci.
-/
theorem exists_common_degree_nonvanishing {X : Scheme.{u}} (L : X.Modules)
    [L.IsInvertible] (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (s : (L.tensorPow p).val.presheaf.obj (Opposite.op ⊤))
    (t : (L.tensorPow q).val.presheaf.obj (Opposite.op ⊤)) :
    ∃ M : X.Modules, M.IsInvertible ∧
      ∃ s' t' : M.val.presheaf.obj (Opposite.op ⊤),
        nonvanishingLocus M s' = nonvanishingLocus (L.tensorPow p) s ∧
        nonvanishingLocus M t' = nonvanishingLocus (L.tensorPow q) t := by sorry

end AlgebraicGeometry.Scheme.Modules
