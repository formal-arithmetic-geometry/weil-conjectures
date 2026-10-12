/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Algebra.Homology.SingleComplexAffineBaseChange
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.AlgebraicGeometry.QuasiCompactOpenInduction
import Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection
import Sheaf.AlgebraicGeometry.RelativeMayerVietoris

/-! # Quasi-compact quasi-separated base change for one complex

Source: Stacks Project, perfect.tex, Tag 0DJ9, lemma-single-complex-base-change
(blueprint: lem-pc-rf-single-complex-qcqs-induction).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- A stalkwise single-complex condition implies qcqs derived base change.
The hypothesis uses the canonical localized tensor-cohomology comparison followed
by the given phi, expressed in K-flat representative coordinates. The conclusion
is the canonical base-change morphism followed by Rf'_* of that same phi.

Proof (the four steps of the node):
1. Invertibility is local on S'. Restrict to affine opens of S' mapping into
   affine opens of S. Derived pullback, direct image and the canonical map restrict
   compatibly; X is then qcqs.
2. For an affine U in X, use lem-pc-affine-qcoh-derived-equivalence and
   lem-pc-derived-direct-image-preserves-qcoh to identify the restricted objects
   with complexes of modules. By lem-pc-affine-derived-pullback-tensor-tilde,
   pullback is derived scalar extension. The stalk condition then gives the
   affine comparison isomorphism by lem-pc-rf-single-complex-affine-base-change.
3. Define P(W) as invertibility of the comparison on a quasi-compact open W.
   Affine opens satisfy P by step 2. Apply lem-sc-invert-s-cohomology-induction.
   In its induction step U is quasi-compact and V affine; their intersection is
   quasi-compact by pqf-lem-qs-intersection-qc, since X is quasi-separated.
4. Apply lem-pc-rf-single-complex-relative-mayer-vietoris to U union V: the
   comparisons on U, V and their intersection are isomorphisms, so the comparison
   on their union is an isomorphism. Induction gives P(X), proving the result.
Source: Stacks Project, perfect.tex, Tag 0DJ9
(blueprint: lem-pc-rf-single-complex-qcqs-induction). -/
theorem singleComplexBaseChangeQcqsInduction
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
      (schemeDerivedDirectImage f').map φ) := by
  sorry

end AlgebraicGeometry
