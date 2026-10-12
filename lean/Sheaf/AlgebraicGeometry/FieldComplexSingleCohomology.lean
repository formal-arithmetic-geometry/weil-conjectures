/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Contraction of a field complex onto its single cohomology

Source: blueprint lem-pc-perfect-locus, proof step 4, vector-space splitting argument.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A complex of module sheaves on a field spectrum contracts onto its sole cohomology.

Source: blueprint lem-pc-perfect-locus, proof step 4, as recorded in
`lem-pc-finite-free-single-field-fibre`, proof step 2.
(blueprint: new-field-complex-single-cohomology).

Proof: Global sections identify module sheaves on Spec R with R-vector spaces and
preserve homology. In each degree n, choose a complement H_n of the boundaries B_n
inside the cycles Z_n, and a complement C_n of Z_n inside P_n. Then
P_n = B_n ⊕ H_n ⊕ C_n, and the differential identifies C_n with B_(n+1).
Project onto H_n and include it to obtain chain maps to and from the complex with
zero differentials on the H_n. Define a degree-minus-one homotopy by the inverse
of C_(n-1) → B_n on B_n, and zero on H_n and C_n. Its differential plus its
composition with the differential is the identity minus the cohomology projection.
The reverse composite is the identity. Vanishing of cohomology outside j eliminates
all H_n except H_j, which is canonically isomorphic to P.homology j. Transport
these maps and homotopies back along the global-sections equivalence. No boundedness
or finite-dimensionality is required: each formula involves only adjacent degrees.
For an acyclic complex the same formula contracts the whole complex, and no
nonzero cohomology or positive rank is assumed. -/
theorem homotopyEquiv_single_cohomology_of_field
    {R : CommRingCat.{u}} (hR : IsField R)
    (P : CochainComplex (Spec R).Modules ℤ) (j : ℤ)
    (hzero : ∀ q : ℤ, q ≠ j → IsZero (P.homology q)) :
    Nonempty (HomotopyEquiv P
      ((CochainComplex.singleFunctor (Spec R).Modules j).obj (P.homology j))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
