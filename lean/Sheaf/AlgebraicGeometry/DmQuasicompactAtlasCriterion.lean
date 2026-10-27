/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.StackTopologyOpenSubstacks
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Quasi-compactness and affine atlases of Deligne--Mumford stacks

Source: Stacks Project, stacks-properties.tex, Tag 04YC (lemma-quasi-compact-stack),
conditions (1), (2), (3), (5), restricted to Deligne--Mumford stacks
(blueprint: lem-sfb-dm-quasicompact-atlas-criterion).

Quasi-compactness uses the existing topology on the existing field-point quotient.
Representable smoothness uses the existing algebraic-space scheme tests, and
surjectivity is explicitly surjectivity on point classes.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A DM stack is quasi-compact exactly when it has an affine smooth surjective
scheme atlas, a quasi-compact smooth surjective scheme atlas, or a surjection from
a quasi-compact DM stack. Smoothness is tested on every étale scheme chart of each
algebraic-space base change; the last morphism need only be surjective on points.
Source: Stacks Project, stacks-properties.tex, Tag 04YC, conditions (1), (2), (3), (5)
(blueprint: lem-sfb-dm-quasicompact-atlas-criterion).

Proof:
1. Choose an étale surjective scheme atlas by def-sfb-stable-pointed-moduli-groupoids
and refine it by affine opens using lem-pc-fppf-affine-open-cover. The inclusions are
étale by lem-weil-pbc-open-immersion-etale. Their composites with the atlas are
representable étale, hence smooth, flat and locally finitely presented, by
lem-sfb-stack-chartwise-smooth-etale-calculus. Regard each chart as an algebraic
space by def-trf-scheme-algebraic-space. Its point image is open by
lem-sfb-stack-point-topology-flat-lfp-open. These images cover by the atlas's
surjectivity and the field-lifting/chart-test equivalence in the calculus node.
The topology agrees with the étale atlas topology of lem-sfb-stack-topology-open-substacks.
2. Compactness selects finitely many of these images. Form the coproduct of their
affine charts using lem-weil-pbc-scheme-coproduct-family. The coproduct clause of
lem-sfb-stack-chartwise-smooth-etale-calculus gives a representable étale, hence
smooth, map from this coproduct, and its images cover all point classes. By
lem-weil-pbc-finite-affine-coproduct-spectrum this finite coproduct is the spectrum
of the product of the chart rings. This proves (1) implies (2). The empty family
gives Spec of the zero ring, and covers exactly the empty stack.
3. An affine scheme is quasi-compact by lem-weil-pbc-affine-scheme-qcqs, so (2)
implies (3), with the same map.
4. Regard the scheme in (3) as its discrete representable stack. Scheme fibre
products (def-pc-fibre-product) represent its diagonal; its identity is an étale
atlas by lem-weil-pbc-open-immersion-etale. The Yoneda sheaf is an algebraic space
by def-trf-scheme-algebraic-space, and sheaf gluing is precisely discrete stack
descent. Its point topology is the usual scheme topology by
lem-sfb-stack-topology-open-substacks. Thus (3) implies (4).
5. For (4) implies (1), the point map is continuous by
lem-sfb-stack-point-topology-flat-lfp-open. Pull an open cover back to the source,
choose a finite subcover by its compactness, and use surjectivity to show the
corresponding finitely many original opens cover the target. No separation,
finite-type or field-base hypothesis is needed. Universe maxima allow the source
witness to contain both the given stack and the scheme category. -/
theorem dm_quasicompact_atlas_criterion {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (hF : IsDeligneMumfordModuliStack F) :
    (CompactSpace (ModuliPoints F) ↔
      ∃ (A : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj A)) F),
        IsAffine A.left ∧ ModuliSpaceTest @Smooth a ∧
          Function.Surjective (moduliPointMap a)) ∧
    (CompactSpace (ModuliPoints F) ↔
      ∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
        CompactSpace U.left ∧ ModuliSpaceTest @Smooth a ∧
          Function.Surjective (moduliPointMap a)) ∧
    (CompactSpace (ModuliPoints F) ↔
      ∃ (V : BasedCategory.{max u v₁ v₂, max (u + 1) w₁ w₂} (Over S))
        (f : BasedFunctor V F),
        IsDeligneMumfordModuliStack V ∧ CompactSpace (ModuliPoints V) ∧
          Function.Surjective (moduliPointMap f)) := by
  sorry

end CategoryTheory
