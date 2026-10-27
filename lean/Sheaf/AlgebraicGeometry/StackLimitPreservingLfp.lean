/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.FibredGroupoidLimitPreserving
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Limit criterion for local finite presentation of an algebraic stack

Source: Stacks Project, stacks-limits.tex, Tag 0CMY,
proposition-characterize-locally-finite-presentation, with scheme target;
Tag 0CMX, lemma-locally-finite-presentation-limit-preserving
(blueprint: lem-sfb-stack-limit-preserving-lfp).

Local finite presentation is expressed on a smooth surjective scheme atlas.
The existing limit-preservation predicate retains objects, their isomorphisms,
and eventual equality of isomorphisms, rather than only isomorphism classes.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- An algebraic stack over a scheme is locally of finite presentation exactly when
its groupoids of points preserve directed affine limits.
Source: Stacks Project, Tags 0CMX and 0CMY
(blueprint: lem-sfb-stack-limit-preserving-lfp).

Proof:
1. Suppose a smooth surjective atlas U has locally finitely presented structural
   map U → S. By lem-sfb-etale-smooth-atlas-fppf-descent the stack has effective
   fppf descent. The relation space R = U ×_F U parametrizes triples (u,v,alpha).
   Its projections are smooth base changes of the atlas, so R → S is locally of
   finite presentation by lem-sfb-stack-chartwise-smooth-etale-calculus.
   Apply lem-sfb-lfp-space-scheme-limit-test to U and R: maps descend to stages
   and equalities of maps hold eventually.
2. For x over an affine limit T, lem-sfb-smooth-space-cover-etale-sections gives
   étale local lifts to U. These are fppf, and lem-pc-fppf-affine-refinement gives
   a finite affine refinement. Descend it to a standard fppf covering of a stage
   by lem-sfb-standard-fppf-cover-limit-descent. Pair and triple overlaps are
   affine with the required limits: their rings are tensor products, whose maps
   are precisely compatible pairs of ring maps.
3. Descend the finitely many local maps to U and the transition arrows to R
   using lem-sfb-lfp-space-scheme-limit-test. Increase the stage to impose their
   source, target and cocycle equalities. Fppf effectiveness glues an object at
   this stage; the isomorphism sheaf condition identifies its restriction with x.
   This proves ObjectsDescend.
4. Given a limit isomorphism between stage objects, choose common finite affine
   fppf covers at that stage lifting both objects to U. On this cover the
   isomorphism is a finite family of maps to R. Descend these maps and impose
   their source, target and overlap compatibility equations by eventual equality
   into U and R. The isomorphism sheaf condition glues a stage isomorphism.
   For two stage arrows equal at the limit, the same cover reduces equality to
   finitely many equalities into R, which hold at a common later stage. Sheaf
   descent gives equality there. This proves ArrowsDescend and ArrowEqualitiesDescend.
5. Conversely, choose a smooth surjective atlas U → F. It is representable and
   locally of finite presentation by lem-sfb-stack-chartwise-smooth-etale-calculus.
   Its relative object descent follows from lem-sfb-representable-lfp-object-limit-test.
   For u over T, ObjectsDescend first descends its image in F; relative object
   descent for the atlas then descends u itself, with the specified identification.
   Scheme fibres are discrete, so this is descent of the actual map to U.
   Apply the reverse direction of lem-sfb-representable-lfp-object-limit-test to
   h_U → h_S. Thus U → S is locally of finite presentation, as required by the
   smooth-atlas definition on the left. -/
theorem locallyOfFinitePresentation_iff_isLimitPreserving
    {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F) :
    (∃ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧ LocallyOfFinitePresentation U.hom) ↔
      FibredGroupoidLimit.IsLimitPreserving F := by
  sorry

end CategoryTheory
