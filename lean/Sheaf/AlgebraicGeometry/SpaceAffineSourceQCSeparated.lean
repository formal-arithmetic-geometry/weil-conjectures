/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine étale charts of quasi-separated algebraic spaces

Source: Stacks Project, Perfect Complexes on Algebraic Spaces, Tag 08IL,
`lemma-tor-qc-qs`, first paragraph of proof
(blueprint: lem-sfb-space-affine-source-qc-separated).

Quasi-separatedness is absolute, expressed by the existing affine-pair criterion
of Properties of Spaces, Tag 0AHR. The base scheme is arbitrary.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale map from an affine scheme to an absolutely quasi-separated algebraic
space is quasi-compact and separated. No quasi-compactness of the target is required.
Source: Stacks Project, Perfect Complexes on Algebraic Spaces, Tag 08IL,
`lemma-tor-qc-qs`, first paragraph of proof
(blueprint: lem-sfb-space-affine-source-qc-separated).

Proof:
1. For an affine test V -> Y, the fibre product R = U times_Y V is a scheme by
   lem-trf-space-fibre-products-etale-covers, using representable étaleness of j.
   Put P = U times_Spec(Z) V. It is affine by
   lem-weil-pbc-fibre-product-affine-spectra and quasi-compact by
   lem-weil-pbc-affine-scheme-qcqs. The map R -> P is the base change of the
   absolute diagonal of Y along (j,g). Absolute quasi-separatedness makes this
   map quasi-compact; lem-weil-pbc-qcqs-morphism-permanence (2) makes R
   quasi-compact. Equivalently, use the affine-pair criterion defining
   IsAbsolutelyQuasiSeparated. The identity atlas of R gives exactly the
   affine-test predicate of lem-trf-space-qc-separated-etale-local.
2. D = U times_Y U is again a scheme. The absolute diagonal
   U -> U times_Spec(Z) U is a closed immersion, by
   lem-weil-pbc-affine-source-morphism-separated and def-weil-proper-morphism.
   Its pullback along (p1,p2) : D -> U times_Spec(Z) U is the relative diagonal
   of j: on sections, a pair with equal image in Y and equal components is
   uniquely a section of U. Apply lem-weil-pbc-closed-immersion-base-change
   first to this square and then to every scheme test of D. This is precisely
   IsSeparatedPresheafMap j, the second predicate from
   lem-trf-space-qc-separated-etale-local. -/
theorem quasiCompact_separated_of_affine_etale
    {S : Scheme.{u}} (Y : AlgebraicSpace S) (hY : IsAbsolutelyQuasiSeparated Y)
    (U : Over S) [IsAffine U.left] (j : yoneda.obj U ⟶ Y.obj.obj)
    (hj : IsEtale j) :
    IsQuasiCompactPresheafMap j ∧ IsSeparatedPresheafMap j := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
