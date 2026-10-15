/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.FiniteStability
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
import Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Degree-zero flat base change for étale sheaves of sets

Source: Stacks Project, Tags 0EYS and 0EZX; blueprint sec-smooth-base-change,
sk-prop-deg0 (blueprint: sbc-lem-degree-zero-flat-base-change).

The exchange arrow is the existing `Etale.setBaseChangeArrow`, constructed using
the unit, direct-image composition comparisons, and counit.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Flat, locally finitely presented base change with geometrically reduced fibres
commutes with direct image for every étale sheaf of sets.
Source: Stacks Project, Tags 0EYS, 0EZX and 0EY5
(blueprint: sbc-lem-degree-zero-flat-base-change).

Proof:
1. For every étale object over X, its composite with f is flat and locally of finite
   presentation, and has geometrically reduced fibres: use lem-pc-flat-compose,
   lem-weil-pbc-finite-presentation-base-change-composition, and
   etale-proposition-etale-reduced after every field extension. Apply
   lem-sbc-flat-reduced-etale-connected-charts to cover it by charts U → V → S,
   where V → S is étale and U → V is flat, quasi-compact, with nonempty
   geometrically connected fibres.
2. Set G = g_*F. By lem-weil-pbc-sets-etale-inverse-image-restriction and
   lem-weil-pbc-sets-etale-inverse-image-composition-units, the sections theorem
   lem-weil-pbc-etale-sections-flat-qc-connected-fibres gives the canonical
   bijection A : G(V) → (f⁻¹G)(U), compatible with the unit for f.
3. Fibre-product pasting identifies U ×_X Y with U ×_V (V ×_S T).
   The base change of U → V is flat and quasi-compact by
   lem-weil-pbc-flat-morphism-base-change and lem-pc-quasi-compact-base-change,
   and has nonempty geometrically connected fibres by their definition.
4. Apply the same sections theorem after this base change, with the restriction
   and composition comparisons, to obtain B : F(V ×_S T) → (e⁻¹F)(U ×_X Y).
   Direct-image evaluation identifies the sources of A and B. The adjoint-transpose
   equation defining exchange, and the unit equations in the comparison nodes,
   give β(U) ∘ A = B, so β(U) is bijective on each good chart.
5. Sheaf separatedness gives injectivity on every object by its good-chart cover.
   For a target section, the unique local lifts agree on overlaps by that
   injectivity. The equalizer sheaf axiom glues them, proving surjectivity.
   Inverses to the bijective components are natural and give an inverse sheaf map.
6. In the smooth case sbc-lem-smooth-criterion supplies flatness and local finite
   presentation, and sbc-lem-smooth-geometrically-reduced supplies reduced fibres.
   Apply the preceding argument. No condition on g or torsion is used. -/
theorem isIso_etaleSetDegreeZeroBaseChange_of_flat
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} (sq : ChosenCartesianSquare h e f g)
    [Flat f] [LocallyOfFinitePresentation f]
    (hf : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s))
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (Etale.setBaseChangeArrow sq F) := by
  sorry

/-- The smooth special case of degree-zero base change, with arbitrary base change
and arbitrary sheaves of sets. Source: Stacks Project, Tag 0EYS; blueprint
sk-prop-deg0, Step 4 (blueprint: sbc-lem-degree-zero-flat-base-change).

Proof: sbc-lem-smooth-criterion makes f flat and locally of finite presentation;
sbc-lem-smooth-geometrically-reduced gives geometrically reduced fibres.
Apply isIso_etaleSetDegreeZeroBaseChange_of_flat, with the same square and sheaf. -/
theorem isIso_etaleSetDegreeZeroBaseChange_of_smooth
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} (sq : ChosenCartesianSquare h e f g) [Smooth f]
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (Etale.setBaseChangeArrow sq F) := by
  sorry

end AlgebraicGeometry
