/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Finite presentation over a qcqs algebraic space

Source: Stacks Project, Morphisms of Spaces, Tag 06G5,
lemma-finite-presentation-quasi-compact-quasi-separated
(blueprint: lem-sfb-space-fp-qcqs-source).

Quasi-compactness is compactness of the existing atlas-topological point space.
Quasi-separatedness of a space is absolute, expressed by the existing affine-test
criterion equivalent to quasi-compactness of its diagonal over Spec Z.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The source of a finitely presented morphism to a qcqs algebraic space is qcqs.
Source: Stacks Project, Morphisms of Spaces, Tag 06G5
(blueprint: lem-sfb-space-fp-qcqs-source).

Proof:
1. Extend affine-test quasi-compactness to all quasi-compact algebraic-space tests.
   For C to B, choose a surjective etale affine scheme atlas U to C by
   [lem-sfb-qc-space-affine-etale-atlas]. The pullback A times_B U is quasi-compact.
   Its projection to A times_B C is surjective etale by
   [lem-trf-space-fibre-products-etale-covers], hence continuous and surjective on
   points by [lem-a1-space-point-open-calculus]. Pulling back an open cover and taking
   a finite subcover proves quasi-compactness downstairs. Conversely affine schemes
   are quasi-compact by [lem-weil-pbc-affine-scheme-qcqs].
2. Quasi-compact maps are stable under base change: an affine test of a base change
   is the original affine test, by the sheaf fibre-product universal property.
   They are stable under composition: first pull back the second map to an affine
   test, then apply step 1 to the first map and that quasi-compact pullback.
3. Finite presentation supplies quasi-compactness of f. Apply step 1 to the identity
   test Y to Y. Since Y is quasi-compact, X times_Y Y, canonically X, is quasi-compact.
4. Over Z = Spec Z, the map X times_Y X to X times_Z X is the base change of the
   absolute diagonal of Y along f times f: matching pairs correspond to triples
   (x1,x2,y) with f(x1) = y = f(x2). It is quasi-compact by step 2 and absolute
   quasi-separatedness of Y. Composing it with the quasi-compact relative diagonal
   of f gives the absolute diagonal of X. Step 2 proves this composite quasi-compact,
   hence X absolutely quasi-separated by the equivalent affine-test criterion
   [def-sfb-space-absolute-quasi-separated]. No separation property of S is needed. -/
theorem qcqs_source_of_finitePresentation {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hYqc : CompactSpace (Point Y.obj.obj))
    (hYqs : IsAbsolutelyQuasiSeparated Y)
    (hfqc : MapIsQuasiCompact f.hom.hom)
    (hfqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (hflfp : MapIsLocallyOfFinitePresentation f) :
    CompactSpace (Point X.obj.obj) ∧ IsAbsolutelyQuasiSeparated X := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
