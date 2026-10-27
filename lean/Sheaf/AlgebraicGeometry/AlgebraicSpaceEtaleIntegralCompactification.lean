/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Integral compactification of a separated étale scheme chart

Source: Stacks Project, Morphisms of Spaces, Tag 0ABS
(`lemma-quasi-finite-separated-quasi-affine`), with Tag 03WS
(blueprint: lem-sfb-space-quasifinite-integral-compactification).

All morphism properties are expressed by the existing scheme-test interface
`IsRepresentableWith`. In particular, quasi-compactness is relative quasi-compactness,
and no quasi-compactness or quasi-separatedness of the base or target is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact separated étale scheme chart factors through an integral algebraic
space by a quasi-compact open immersion.
Source: Stacks Project, Morphisms of Spaces, Tag 0ABS, with Morphisms Tag 03WS
(blueprint: lem-sfb-space-quasifinite-integral-compactification).

Proof:
1. On each scheme test, étaleness implies unramifiedness and local finite presentation.
Apply `lem-weil-pbc-unramified-quasi-finite-at-points` to obtain quasi-finiteness at
every point, including the finite-type neighbourhood condition of
`pqf-def-quasifinite`. Together with the assumed quasi-compactness this makes the
chart finite type, as in `def-weil-finite-type-morphism`.
2. Apply `lem-sfb-space-relative-integral-factorization` to obtain the relative
normalization factorization through an algebraic space B integral over X. The
identity of each quasi-compact scheme pullback is the required étale atlas.
By `lem-sfb-space-integral-qcqs-permanence`, the integral map is separated. Its
diagonal has quasi-compact scheme tests, since a closed subscheme of an affine
scheme is quasi-compact (`def-weil-closed-immersion`). Apply
`lem-sfb-space-qc-cancellation` to the factorization to make its first map
quasi-compact, first on affine tests and then on all scheme tests.
3. Apply `lem-sfb-space-normalization-quasifinite-locus` to this representable,
finite-type separated chart and its normalization. It supplies an open subspace
of B whose inverse image is the quasi-finite locus and over which the first map
is an isomorphism. Step 1 makes that locus all of U, so this first map is an
open immersion. Step 2 already gives its quasi-compactness, integrality of the
second map, and the factorization equality. No global finiteness or normality
assumption is used, and the empty chart is included. -/
theorem exists_integral_compactification_of_etale
    {S : Scheme.{u}} (U : Over S) (X : AlgebraicSpace S)
    (a : yoneda.obj U ⟶ X.obj.obj)
    (haqc : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) a)
    (hasep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal a))
    (haet : IsEtale a) :
    ∃ (B : AlgebraicSpace S) (π : B ⟶ X) (j : yoneda.obj U ⟶ B.obj.obj),
      IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) π.hom.hom ∧
      IsRepresentableWith
        (fun _ _ p ↦ IsOpenImmersion p.left ∧ QuasiCompact p.left) j ∧
      j ≫ π.hom.hom = a := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
