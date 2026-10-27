/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCartesianChartFamily
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Quasi-coherent modules and cartesian families on all étale charts

Source: Stacks Project, Properties of Spaces, Tags 03LY and 03LZ
(blueprint: lem-sfb-space-qcoh-cartesian-chart-family).

The functor is canonical restriction, including its action on maps and its transition
isomorphisms. Its equivalence asserts both effective reconstruction of every family
and existence and uniqueness of the global map associated to any compatible family
of chart maps. All charts use the localized étale-site convention of `etalePullback`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical transition between direct and repeated chart restriction.
Source: Stacks Project, Properties of Spaces, Tag 03LY
(blueprint: lem-sfb-space-qcoh-cartesian-chart-family). -/
noncomputable def moduleChartTransition {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : X.Modules) {W V : X.EtaleSite} (f : W ⟶ V) :
    (X.etalePullbackMap f).obj ((X.etalePullback V).obj M) ≅
      (X.etalePullback W).obj M :=
  (SheafOfModules.overFunctorMap X.structureSheaf f).app M

/-- The canonical restriction identifications satisfy the identity law on sections.
Source: Stacks Project, Properties of Spaces, Tags 03LY and 03LZ
(blueprint: lem-sfb-space-qcoh-cartesian-chart-family).
Proof: the inverse component of `Over.mapId` is the identity on the underlying
chart, so the displayed restriction is the original module's identity restriction.
The identity axiom for its presheaf of modules gives the equality (node step 1). -/
theorem moduleChartRestriction_identity {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : X.Modules) (V : X.EtaleSite) (A : Over V)
    (s : ((X.etalePullbackMap (𝟙 V)).obj ((X.etalePullback V).obj M)).val.obj (op A)) :
    (moduleChartTransition X M (𝟙 V)).hom.val.app (op A) s =
      ((X.etalePullback V).obj M).val.map ((Over.mapId V).inv.app A).op s := by
  sorry

/-- The canonical restriction identifications satisfy the composition law on sections.
Source: Stacks Project, Properties of Spaces, Tags 03LY and 03LZ
(blueprint: lem-sfb-space-qcoh-cartesian-chart-family).
Proof: the inverse component of `Over.mapComp` is the identity on the underlying
chart. The identity restriction of M therefore identifies direct and repeated
restriction, which have the same section map (node step 1). -/
theorem moduleChartRestriction_composition {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : X.Modules) {T W V : X.EtaleSite} (g : T ⟶ W) (f : W ⟶ V) (A : Over T)
    (s : ((X.etalePullbackMap (g ≫ f)).obj ((X.etalePullback V).obj M)).val.obj (op A)) :
    (moduleChartTransition X M (g ≫ f)).hom.val.app (op A) s =
      (moduleChartTransition X M g).hom.val.app (op A)
        ((moduleChartTransition X M f).hom.val.app (op ((Over.map g).obj A))
          (((X.etalePullback V).obj M).val.map ((Over.mapComp g f).inv.app A).op s)) := by
  sorry

/-- Canonical restriction to every chart, on objects and module maps, with the
canonical `overFunctorMap` transition identifications.
Source: Stacks Project, Properties of Spaces, Tags 03LY and 03LZ
(blueprint: lem-sfb-space-qcoh-cartesian-chart-family). -/
noncomputable def moduleChartRestriction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.Modules ⥤ CartesianModuleChartFamily X where
  obj M :=
    { obj := fun V ↦ (X.etalePullback V).obj M
      transition := fun f ↦ moduleChartTransition X M f
      identity := fun V A s ↦ moduleChartRestriction_identity X M V A s
      composition := fun g f A s ↦ moduleChartRestriction_composition X M g f A s }
  map h :=
    { app := fun V ↦ (X.etalePullback V).map h
      comm := fun f ↦ (SheafOfModules.overFunctorMap X.structureSheaf f).hom.naturality h }


/-- Restriction to a chart preserves local presentations, hence quasi-coherence.
Source: Stacks Project, Properties of Spaces, Tag 03LZ; Modules on Sites, Tag 03DL
(blueprint: lem-sfb-space-qcoh-cartesian-chart-family).

Proof (step 1 of the node): for an object T → V of the localized site, apply the
local-presentation definition of M to the same object T → X. Its covering is still
a covering in X_et/V. The iterated slice over each covering member is canonically
the original slice over that member, with the same restricted structure sheaf.
Thus the free-module presentation for M is precisely a presentation for its chart
restriction. This works for every object of the localized site. -/
theorem chartRestriction_isQuasicoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    (M : X.QCoh) (V : X.EtaleSite) :
    ((X.etalePullback V).obj M.obj).IsQuasicoherent := by
  sorry

/-- Canonical restriction of a quasi-coherent module and its maps to all charts.
Source: Stacks Project, Properties of Spaces, Tags 03LY and 03LZ
(blueprint: lem-sfb-space-qcoh-cartesian-chart-family). -/
noncomputable def qcChartRestriction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.QCoh ⥤ X.CartesianQCohChartFamily where
  obj M := ⟨X.moduleChartRestriction.obj M.obj, fun V ↦ chartRestriction_isQuasicoherent X M V⟩
  map h := ObjectProperty.homMk (X.moduleChartRestriction.map h.hom)

/-- Quasi-coherent modules on an algebraic space are equivalent, by restriction, to
cartesian quasi-coherent module families on every étale chart. Essential surjectivity
is reconstruction with compatible restriction isomorphisms; full faithfulness is
existence and uniqueness of maps realizing compatible families of chart maps.
Source: Stacks Project, Properties of Spaces, Tags 03LY and 03LZ
(blueprint: lem-sfb-space-qcoh-cartesian-chart-family).

Proof:
1. Restriction is quasi-coherent by `chartRestriction_isQuasicoherent`; repeated
   restriction gives the canonical identity and composition laws. Maps restrict
   compatibly. This defines `qcChartRestriction`.
2. For a family F, define M(V) = F_V(V). Its module structure is the one supplied by
   F_V on the terminal chart. For f : W → V, define restriction as restriction inside
   F_V followed by the W-component of c_f. This map is semilinear over the actual
   regular-function restriction (def-weil-sheaf-of-modules-category).
3. The identity condition gives identity restrictions. Naturality of c_f and its
   composition law give restriction along g followed by f equal to restriction along
   their composite. The T-component of c_a, for a : T → V, identifies F_V with the
   restriction of the constructed presheaf M to X_et/V, naturally in T.
4. For a covering of V, these identifications convert a matching family in M to a
   matching family in F_V. The sheaf axiom for F_V gives the unique amalgamation.
   It also treats an empty covering. Thus M is a module sheaf, and the chartwise
   presheaf identifications are module-sheaf isomorphisms.
5. Evaluating on T → W verifies compatibility of these isomorphisms with c_f by
   its cocycle. The local presentations of F_V then give the local presentations
   of M on every chart (def-trf-space-quasi-coherent-module). Hence M is quasi-coherent.
6. For compatible maps h_V, define h(V) to be the terminal component of h_V.
   Their compatibility and naturality prove that h commutes with restrictions.
   Its restriction to each chart is h_V under the constructed identifications.
   This respects identity maps and composition.
7. Starting with M, evaluation of its restricted family recovers precisely M(V)
   and its restriction maps. Starting with F, the isomorphisms of steps 3–5 identify
   the reconstructed family with F, naturally by step 6. This gives the two
   quasi-inverse identifications. A global map with the prescribed chart maps has
   its component at V forced by the terminal component of h_V, proving uniqueness.
These are the node's steps, using Tags 03LY/03LZ and the explicit evaluation
construction of Sites, Tag 0GWK. No preservation of cokernels by section evaluation
is required. -/
theorem qcChartRestriction_isEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.qcChartRestriction.IsEquivalence := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
