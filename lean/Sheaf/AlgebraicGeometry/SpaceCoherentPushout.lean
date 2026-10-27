/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.Ring.Constructions
import Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.SpaceModuleBaseChangeFlatProperSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport
import Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Support

/-! # Infinitesimal pushout gluing of proper-support coherent families

Source: Stacks Project, quot.tex, Situation 08KB and Tag 08LQ, lemma-coherent-RS-star
(blueprint: lem-sfb-space-coherent-pushout).

The total category is the existing CoherentModuli category, with its actual modules,
maps to B, and tensor-pullback isomorphisms. A span over Z -> Y and Z -> Z' records
an object on each piece and a specified identification over Z. Its pushout over Y'
expresses essential surjectivity and the unique gluing of all compatible arrows.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Restriction of proper-support coherent families across a nilpotent pushout is
an equivalence of groupoids, in the total-category formulation.

The objects x,y,z and arrows a,b record the specified overlap isomorphism: arrows
in CoherentModuli are cartesian tensor-pullback isomorphisms. The conclusion gives
an object t over P and its identifications with y,z. IsPushout retains commutativity
with a,b and the unique gluing of every compatible pair of arrows, hence full
faithfulness including automorphisms. Conversely an equivalence of the restriction
on fibres gives this total-category pushout: first glue the base maps to any target
base by the scheme pushout, pull the target back along that map, and use full
faithfulness in the fibre. This formulation chooses no arbitrary equivalence.

Source: Stacks Project, Tag 08LQ, Situation 08KB
(blueprint: lem-sfb-space-coherent-pushout).

Proof:
1. lem-sfb-space-affine-thickening-pushout upgrades the scheme pushout to an
   algebraic-space pushout, so compatible maps to B glue uniquely. Fix their
   common extension; all the spaces are now the canonical X times_B T.
2. The chart test lem-sfb-space-local-properties-chart-test and the affine finite
   presentation/base-change lemmas make X_T -> T locally finitely presented,
   hence locally of finite type, for every test scheme T.
3. lem-sfb-space-module-base-change-flat-proper-support preserves quasi-coherence,
   finite presentation, relative flatness, and proper support under restriction.
   The normalized tensor-composition isomorphisms give the overlap comparison.
4. lem-sfb-space-relative-flat-module-pushout glues the flat modules with their
   specified overlap isomorphism. Its finite-presentation clause applies by step 2.
5. lem-sfb-space-module-proper-carrier-support constructs the annihilator support.
   The finite-module support-annihilator formula and lem-sfb-space-etale-chart-support
   identify its points with module support. Thickening base change and
   lem-sfb-space-finite-type-support-pullback identify its restriction with the
   given proper support. lem-sfb-space-proper-support-closed-operations makes this
   restricted closed subspace proper.
6. lem-sfb-space-thickening-topological-properties transfers quasi-compactness,
   separatedness and universal closedness to the glued support. It is locally of
   finite type as a closed subspace of X_P, so it is proper. The carrier-support
   lemma gives the required closed pushforward description of the glued module.
7. Full faithfulness of relative flat-module patching glues all module maps
   uniquely; gluing inverse maps shows compatible isomorphisms glue to an iso.
   Step 1 supplies the base map. For targets over other schemes, first glue their
   base maps by the base pushout and pull the target back. This is exactly the
   total-category universal property below. No ambient flatness or Noetherian
   assumption occurs. -/
theorem coherent_pushout (f : X ⟶ B) (hfp : ProperQuotFinitePresentation f)
    {Z Y Z' P : Over S} (i : Z ⟶ Z') (v : Z ⟶ Y) (j : Y ⟶ P) (k : Z' ⟶ P)
    (hi : IsFiniteOrderThickening i.left) [IsAffineHom v.left]
    (hp : IsPushout v.left i.left j.left k.left)
    (x : Functor.Fiber (CoherentModuli.category f).p Z)
    (y : Functor.Fiber (CoherentModuli.category f).p Y)
    (z : Functor.Fiber (CoherentModuli.category f).p Z')
    (a : x.val ⟶ y.val) (b : x.val ⟶ z.val)
    (ha : (CoherentModuli.category f).p.IsHomLift v a)
    (hb : (CoherentModuli.category f).p.IsHomLift i b) :
    ∃ (t : Functor.Fiber (CoherentModuli.category f).p P)
      (c : y.val ⟶ t.val) (d : z.val ⟶ t.val),
      (CoherentModuli.category f).p.IsHomLift j c ∧
      (CoherentModuli.category f).p.IsHomLift k d ∧ IsPushout a b c d := by
  sorry

/-- The affine square-zero specialization, using the explicit ring fibre product.
All four S-structures and the arrows over S are arbitrary subject to the displayed
canonical underlying Spec maps. Thus no choice of S-structure or restriction to
nonzero rings is implicit. The pt of CommRingCat.pullbackCone is the subring of
D' times A consisting of pairs with equal images in D.

Source: Stacks Project, Tag 08LQ and Situation 08KB, with Tag 0ET0
(blueprint: lem-sfb-space-coherent-pushout).

Proof: apply lem-sfb-affine-closed-pinching-pushout to q and alpha; it identifies
Spec(D' times_D A) with the required scheme pushout, with the very projections
specified below. Surjectivity of q gives a closed immersion Spec D -> Spec D';
the square-zero kernel makes it a finite-order thickening. Every morphism of
affine schemes is affine. Apply coherent_pushout, retaining the specified overlap
arrows, the lifts of the two inclusions and their full pushout universal property. -/
theorem coherent_pushout_affine (f : X ⟶ B) (hfp : ProperQuotFinitePresentation f)
    {A D D' : CommRingCat.{u}} (alpha : A ⟶ D) (q : D' ⟶ D)
    (hq : Function.Surjective q.hom) (hzero : RingHom.ker q.hom ^ 2 = ⊥)
    (sZ : Spec D ⟶ S) (sY : Spec A ⟶ S) (sZ' : Spec D' ⟶ S)
    (sP : Spec (CommRingCat.pullbackCone q alpha).pt ⟶ S)
    (i : Over.mk sZ ⟶ Over.mk sZ') (v : Over.mk sZ ⟶ Over.mk sY)
    (j : Over.mk sY ⟶ Over.mk sP) (k : Over.mk sZ' ⟶ Over.mk sP)
    (hi : i.left = Spec.map q) (hv : v.left = Spec.map alpha)
    (hj : j.left = Spec.map (CommRingCat.pullbackCone q alpha).snd)
    (hk : k.left = Spec.map (CommRingCat.pullbackCone q alpha).fst)
    (x : Functor.Fiber (CoherentModuli.category f).p (Over.mk sZ))
    (y : Functor.Fiber (CoherentModuli.category f).p (Over.mk sY))
    (z : Functor.Fiber (CoherentModuli.category f).p (Over.mk sZ'))
    (a : x.val ⟶ y.val) (b : x.val ⟶ z.val)
    (ha : (CoherentModuli.category f).p.IsHomLift v a)
    (hb : (CoherentModuli.category f).p.IsHomLift i b) :
    ∃ (t : Functor.Fiber (CoherentModuli.category f).p (Over.mk sP))
      (c : y.val ⟶ t.val) (d : z.val ⟶ t.val),
      (CoherentModuli.category f).p.IsHomLift j c ∧
      (CoherentModuli.category f).p.IsHomLift k d ∧ IsPushout a b c d := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
