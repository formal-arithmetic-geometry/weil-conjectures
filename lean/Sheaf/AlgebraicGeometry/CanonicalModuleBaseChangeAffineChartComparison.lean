/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps

import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction

/-! # The canonical module base-change arrow in affine charts

Source: Stacks Project, Tags 08IB (local reduction), 08HY (the canonical mate),
and 08FE (restriction of derived direct image).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Restriction and affine charts identify the canonical *arrow*, without asserting
that it is invertible. Both the restricted scheme and its module are explicit.
Source: Stacks Project, Tag 08IB, first paragraph of the proof; Tag 08HY and Tag 08FE.
(blueprint: lem-pc-canonical-module-base-change-affine-chart-comparison).

Proof: put U = f^{-1}(V), Y = U.toScheme, A = Gamma(S,V), B = Gamma(S',W).
Compose f restricted to V with V.isoSpec.hom to obtain fA. Compose W.isoSpec.inv,
g restricted from W to V, and V.isoSpec.hom to obtain gA. The universal property
identifies the chosen pullback of fA and gA with the inverse image of W under f'.
Its projection to Y is g' restricted to this inverse image, with the source chart
W.isoSpec.inv inserted. This identification preserves both projections.

Apply derived pullback composition and exact open restriction to the source.
Apply derived direct-image restriction to the full inverse images U and f'^{-1}(W),
and derived direct-image composition to the target. Transport along the chart
isomorphisms. Since the charts are isomorphisms their module pullbacks are exact;
the resulting object comparisons are the displayed isomorphisms a and b in D(W).

Write hc as the witnessing left-derived counit epsilon and its single-complex
identification. Restrict epsilon to f'^{-1}(W), then transport through the
projection-preserving pullback isomorphism. Exact restriction commutes with
termwise tensor pullback and with the single-complex construction. The left-derived
universal property therefore gives a counit for the affine projection and hence c0
with IsDerivedModulePullbackComparison. Use this transported counit, rather than
selecting an independent comparison. The underived open-restriction identity for
base-change mates, followed by the derived adjunction unit/counit equations, shows
that these object comparisons also identify the arrows. Composing with the
transported comparison c0 gives the displayed commuting square. This calculation
requires neither relative flatness nor quasi-coherence nor an affine invertibility
hypothesis. All constructions also apply to empty opens and the zero module. -/
theorem exists_canonicalModuleBaseChange_affineChart_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    (V : S.affineOpens) (W : S'.affineOpens) (hWV : W.1 ≤ g ⁻¹ᵁ V.1) :
    let U := f ⁻¹ᵁ V.1
    let fA := (f ∣_ V.1) ≫ V.2.isoSpec.hom
    let gA := W.2.isoSpec.inv ≫ g.resLE V.1 W.1 hWV ≫ V.2.isoSpec.hom
    let H := (schemeOpenRestriction X U).obj G
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let E0 := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj H
    let R := (schemeOpenRestriction S' W.1).mapDerivedCategory
    let T := schemeDerivedDirectImage W.2.isoSpec.inv
    ∃ c0 : (derivedPullback (pullback.fst fA gA)).obj E0 ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H),
      IsDerivedModulePullbackComparison (pullback.fst fA gA) H c0 ∧
      ∃ a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≅
          T.obj ((derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E0)),
      ∃ b : R.obj ((schemeDerivedDirectImage f').obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback g').obj G))) ≅
          T.obj ((schemeDerivedDirectImage (pullback.snd fA gA)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H))),
        R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
            (schemeDerivedDirectImage f').map c) ≫ b.hom =
          a.hom ≫ T.map
            (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
              pullback.condition E0 ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
      := by sorry

end AlgebraicGeometry
