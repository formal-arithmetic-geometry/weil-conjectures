/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.Maximal

/-! # Closed points in affine smooth charts of finite-type stack points

Source: Stacks Project, stacks-morphisms.tex, Tags 06FX and 06G3
(blueprint: lem-sfb-stack-finite-type-smooth-closed-chart).

The self-relation is specified by its test-scheme arrows and their composition.
The residue-field representative is the actual canonical scheme map composed with the chart.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- The canonical residue-field map followed by the specified chart.
Source: Stacks, Tag 06FX, (2) implies (1)
(blueprint: lem-sfb-stack-finite-type-smooth-closed-chart). -/
def moduliResidueFieldChart {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    {U : Over S} (q : BasedFunctor (discreteModuli (yoneda.obj U)) F) (z : U.left) :
    BasedFunctor
      (discreteModuli (yoneda.obj (Over.mk (U.left.fromSpecResidueField z ≫ U.hom)))) F :=
  (discreteModuliMap (yoneda.map
    (Over.homMk (U.left.fromSpecResidueField z) rfl :
      Over.mk (U.left.fromSpecResidueField z ≫ U.hom) ⟶ U))).comp q

/-- The self-relation of a particular map, with its projections and composition.
The unique-arrow condition says precisely that R represents the triples (x,y,alpha)
with alpha an isomorphism between their images in the stack. The composition field
fixes the groupoid multiplication to composition of those actual isomorphisms.
Source: Stacks, algebraic.tex, Tag 04T4; stacks-morphisms.tex, Tag 06G3
(blueprint: lem-sfb-stack-finite-type-smooth-closed-chart). -/
structure ModuliSelfRelationGroupoid {S : Scheme.{u}} {U : Over S}
    {F : BasedCategory.{v, w} (Over S)} (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (R : AlgebraicSpace S) (s t : R.obj.obj ⟶ yoneda.obj U)
    (e : yoneda.obj U ⟶ R.obj.obj) (i : R.obj.obj ⟶ R.obj.obj)
    (c : pullback s t ⟶ R.obj.obj) where
  groupoid : AlgebraicSpace.IsPresheafGroupoid s t e i c
  arrows : ModuliTwoIso ((discreteModuliMap s).comp a)
    ((discreteModuliMap t).comp a)
  fully_faithful : ∀ (T : Over S) (x y : yoneda.obj T ⟶ yoneda.obj U)
    (β : a.obj (CostructuredArrow.mk x) ⟶ a.obj (CostructuredArrow.mk y)),
    F.p.IsHomLift (𝟙 T) β →
      ∃! r : {r : yoneda.obj T ⟶ R.obj.obj // r ≫ s = x ∧ r ≫ t = y},
        spaceGroupoidPresentationArrow (U := AlgebraicSpace.schemeSpace U)
          s t a arrows x y r = β
  composition : ∀ (T : Over S) (x y z : yoneda.obj T ⟶ yoneda.obj U)
    (r : {r : yoneda.obj T ⟶ R.obj.obj // r ≫ s = x ∧ r ≫ t = y})
    (q : {q : yoneda.obj T ⟶ R.obj.obj // q ≫ s = y ∧ q ≫ t = z})
    (d : {d : yoneda.obj T ⟶ R.obj.obj // d ≫ s = x ∧ d ≫ t = z})
    (p : yoneda.obj T ⟶ pullback s t),
    p ≫ pullback.fst s t = q.val → p ≫ pullback.snd s t = r.val → p ≫ c = d.val →
      spaceGroupoidPresentationArrow (U := AlgebraicSpace.schemeSpace U)
          s t a arrows x y r ≫
        spaceGroupoidPresentationArrow (U := AlgebraicSpace.schemeSpace U)
          s t a arrows y z q =
        spaceGroupoidPresentationArrow (U := AlgebraicSpace.schemeSpace U)
          s t a arrows x z d

/-- A finite-type stack point has an affine smooth chart with a closed point above it,
and its canonical residue-field representative has a locally finite-type self-relation.
Source: Stacks, stacks-morphisms.tex, Tag 06FX, (1) implies (2) and (2) implies (1);
Tag 06G3, first proof paragraph; algebraic.tex, Tag 04T4
(blueprint: lem-sfb-stack-finite-type-smooth-closed-chart).

Proof:
1. Choose a locally finite-type field representative a0 and a smooth surjective atlas V.
The representable-diagonal theorem makes V times_X Spec K an algebraic space. Its projection
to V is locally finite type and its projection to Spec K is surjective. An etale scheme atlas
E of this space is nonempty and its composite to V is locally finite type. Use
lem-sfb-stack-diagonal-space-source-representability, def-trf-scheme-algebraic-space,
def-trf-algebraic-space, lem-sfb-stack-chartwise-smooth-etale-calculus, and
lem-sfb-space-local-properties-chart-test.
2. Choose a nonempty affine open W of E. A maximal ideal gives a closed point w of W
(lem-weil-pbc-proper-ideal-contained-in-maximal). Its canonical residue-field map is locally
finite type by lem-sfb-finite-type-field-point-characterization, using the degree-one field
extension. Compose it with W to E to V, using lem-weil-pbc-open-immersion-etale and the
chartwise calculus and scheme chart-test. Applying the field-point criterion again shows
that its image u is closed in some affine open U of V. No Jacobson assumption is used.
3. The composite q of U to V with the atlas is smooth. The actual 2-pullback comparison
identifies its residue-field point with the original representative after a common field
extension, using lem-weil-pbc-morphism-from-spec-field. Hence q(u) is x in ModuliPoints.
4. The canonical Spec kappa(u) to U is locally finite type by the field-point criterion;
composing with smooth q gives the stated representative a. By
lem-sfb-self-relation-quotient-embedding, the self-pullback is an algebraic space and its
arrows, projections and composition are precisely those of ModuliSelfRelationGroupoid.
Both projections are base changes of a along a. The chartwise base-change law proves
local finite type for both. Use def-weil-residue-field and the scheme chart-test to
identify the canonical map and its scheme property throughout. -/
theorem stack_finiteType_smooth_closed_chart {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (x : ModuliPoints F)
    (hx : ∃ (K : Type u) (_ : Field K) (b : Spec (.of K) ⟶ S)
      (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) F),
      ModuliSpaceTest @LocallyOfFiniteType a ∧ x ∈ Set.range (moduliPointMap a)) :
    ∃ (U : Over S) (q : BasedFunctor (discreteModuli (yoneda.obj U)) F) (z : U.left),
      IsAffine U.left ∧ ModuliSpaceTest @Smooth q ∧ IsClosed ({z} : Set U.left) ∧
      z ∈ moduliChartPreimage q {x} ∧
      ModuliSpaceTest @LocallyOfFiniteType (moduliResidueFieldChart q z) ∧
      ∃ (R : AlgebraicSpace S)
        (s t : R.obj.obj ⟶ yoneda.obj (Over.mk (U.left.fromSpecResidueField z ≫ U.hom)))
        (e : yoneda.obj (Over.mk (U.left.fromSpecResidueField z ≫ U.hom)) ⟶ R.obj.obj)
        (i : R.obj.obj ⟶ R.obj.obj) (c : pullback s t ⟶ R.obj.obj),
        Nonempty (ModuliSelfRelationGroupoid (moduliResidueFieldChart q z) R s t e i c) ∧
        ∀ (V : Over S) (b : yoneda.obj V ⟶ R.obj.obj), AlgebraicSpace.IsEtale b →
          LocallyOfFiniteType (yoneda.preimage (b ≫ s)).left ∧
          LocallyOfFiniteType (yoneda.preimage (b ≫ t)).left := by
  sorry

end CategoryTheory
