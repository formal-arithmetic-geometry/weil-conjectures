# AlgebraicGeometry.Etale.smallModel_nonempty_strictLocalBaseChange_continuityPresentation

## Reason

Complete the DIFFERENT retirement listed in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation. Its theorem and the
adopted theorem share a public name but have different strict-local base schemes:
the assigned theorem uses strictHenselizationScheme/strictHenselizationStructuralMap;
the adopted theorem uses strictLocalization/strictLocalizationToBase. An import swap
would change the original mate and would not preserve the statement.

Withdraw the ambiguous Sheaf module and preserve its complete theorem in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateContinuityPresentation with the explicit
smallModel_ prefix. The signature and entire proof body are byte-identical modulo the
theorem name. The existing model-specific DAG node follows this retained realization;
its statement, dependencies and unit route stay unchanged. No new node is needed.
The only direct importer changes its private import and theorem call. Its public
signature, visibility, imports and mathematical proof remain unchanged. All three current
downstream consumers are unclaimed. No adopted-source declaration or file changes.
No target meaning changes and no semantic target review is reopened.

The new module publicly imports only the continuity presentation, structural map and
base-change definitions needed by its statement. Geometry and cohomology-germ APIs are
private proof imports. The former direct private import of injective source sections is
redundant: the projection-formula proof module already imports that dependency. Its
mathematics remains needed and is not declared pruned.

## Old

The withdrawn module, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalMateProjectionFormulas

/-! # Presenting the strict-local mate as projection restriction

Source: Stacks Project, Tag 03Q9, the neighbourhood-colimit construction and the
injective-complex restriction maps in its final proof paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Present the source of the strict-local mate as neighbourhood hypercohomology,
and identify its germ components with projection pullbacks to the limit.
This supplies the input to derived continuity, without applying continuity and without
asserting that either the target cocone is a colimit or the mate is invertible.
Source: Stacks Project, Tag 03Q9, proof paragraphs 1 and 3; Tag 03Q8
(blueprint: lem-weil-pbc-strict-local-mate-continuity-presentation).

Proof: use the small representative category of affine pointed neighbourhoods of s.
It is cofiltered by strictHenselization_properties. Base change its diagram along f,
with limit the pullback of the strict henselization; the fibre-product limit theorem
and the characterisation of the structural map identify its cone legs. Its stages
are qcqs since the neighbourhoods are affine and f is qcqs; transitions are affine
since morphisms between affine schemes and their base changes are affine.
Take the diagram F of neighbourhood hypercohomology of the inverse images of K.
Choose a bounded-below injective representative J of K. Restriction along the etale
stage projections preserves injectives, so sections of J compute these groups, and
restriction of sections gives exactly the transition formula in the presentation.
By 03Q8 and invariance of geometric stalks under sheafification, the stalk of H^n Rf_*K
is the colimit of F. The canonical germ restriction is an isomorphism; exact inverse
image commutes with homology. Transport the stalk cocone through these two isomorphisms
to obtain sourceLegs and sourceIsColimit, with vertex the displayed source group.
Exact strict-local global sections and the Leray homology isomorphism identify the
displayed target with hypercohomology of the limit, giving limitIso. On J the
adjunction mate is restriction of sections along the pullback square. Thus each
source germ, followed by the mate and limitIso, is the projection pullback on
hypercohomology. This is precisely the restriction equation of the presentation.
This construction uses no continuity assertion and no isomorphism assertion for the mate.
It applies in negative degrees as well as positive degrees, and to the zero complex;
qcqs is used for the stages, not imposed on S or X separately. -/
theorem nonempty_strictLocalBaseChange_continuityPresentation
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (GlobalCohomologyContinuityPresentation X K n
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K)))) := by
  classical
  obtain ⟨Q⟩ := nonempty_strictLocalNeighbourhoodGeometry f s
  obtain ⟨E⟩ := smallModel_nonempty_strictLocalMateProjectionData f s K n Q
  let := (Scheme.strictHenselization_properties s).2.1
  obtain ⟨hsource⟩ := smallModel_isColimit_strictLocalCohomologySourceLegs s
    ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
  let : ∀ i, CompactSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.compact
  let : ∀ i, QuasiSeparatedSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.quasiSeparated
  let : ∀ {i j} (a : i ⟶ j), IsAffineHom ((strictLocalNeighbourhoodDiagram f s).map a) := Q.affine
  refine ⟨{
    I := SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)
    D := strictLocalNeighbourhoodDiagram f s
    c := Cone.mk _ Q.smallModelLegs
    isLimit := Q.smallModelIsLimit
    t := strictLocalNeighbourhoodProjection f s
    p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    «over» := Q.smallModelOver
    F := strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    e := E.e
    transition := E.transition
    sourceLegs := smallModel_strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    sourceIsColimit := hsource
    limitIso := smallModel_strictLocalBaseChangeTargetIso f s K n
    restriction := fun i ↦ E.restriction i }⟩

end AlgebraicGeometry.Etale
```

## New

The retained small-model realization, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.CohomologyGerms
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit
import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalMateProjectionFormulas

/-! # Projection-restriction presentation on the small strict-local model

This theorem uses `strictHenselizationScheme` and `strictHenselizationStructuralMap`.
The adopted theorem with the unprefixed name uses `strictLocalization` instead.

Source: Stacks Project, Tag 03Q9, the neighbourhood-colimit construction and the
injective-complex restriction maps in its final proof paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Present the source of the strict-local mate as neighbourhood hypercohomology,
and identify its germ components with projection pullbacks to the limit.
This supplies the input to derived continuity, without applying continuity and without
asserting that either the target cocone is a colimit or the mate is invertible.
Source: Stacks Project, Tag 03Q9, proof paragraphs 1 and 3; Tag 03Q8
(blueprint: lem-weil-pbc-strict-local-mate-continuity-presentation).

Proof: use the small representative category of affine pointed neighbourhoods of s.
It is cofiltered by strictHenselization_properties. Base change its diagram along f,
with limit the pullback of the strict henselization; the fibre-product limit theorem
and the characterisation of the structural map identify its cone legs. Its stages
are qcqs since the neighbourhoods are affine and f is qcqs; transitions are affine
since morphisms between affine schemes and their base changes are affine.
Take the diagram F of neighbourhood hypercohomology of the inverse images of K.
Choose a bounded-below injective representative J of K. Restriction along the etale
stage projections preserves injectives, so sections of J compute these groups, and
restriction of sections gives exactly the transition formula in the presentation.
By 03Q8 and invariance of geometric stalks under sheafification, the stalk of H^n Rf_*K
is the colimit of F. The canonical germ restriction is an isomorphism; exact inverse
image commutes with homology. Transport the stalk cocone through these two isomorphisms
to obtain sourceLegs and sourceIsColimit, with vertex the displayed source group.
Exact strict-local global sections and the Leray homology isomorphism identify the
displayed target with hypercohomology of the limit, giving limitIso. On J the
adjunction mate is restriction of sections along the pullback square. Thus each
source germ, followed by the mate and limitIso, is the projection pullback on
hypercohomology. This is precisely the restriction equation of the presentation.
This construction uses no continuity assertion and no isomorphism assertion for the mate.
It applies in negative degrees as well as positive degrees, and to the zero complex;
qcqs is used for the stages, not imposed on S or X separately. -/
theorem smallModel_nonempty_strictLocalBaseChange_continuityPresentation
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (GlobalCohomologyContinuityPresentation X K n
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.natTrans.app K)))) := by
  classical
  obtain ⟨Q⟩ := nonempty_strictLocalNeighbourhoodGeometry f s
  obtain ⟨E⟩ := smallModel_nonempty_strictLocalMateProjectionData f s K n Q
  let := (Scheme.strictHenselization_properties s).2.1
  obtain ⟨hsource⟩ := smallModel_isColimit_strictLocalCohomologySourceLegs s
    ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
  let : ∀ i, CompactSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.compact
  let : ∀ i, QuasiSeparatedSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.quasiSeparated
  let : ∀ {i j} (a : i ⟶ j), IsAffineHom ((strictLocalNeighbourhoodDiagram f s).map a) := Q.affine
  refine ⟨{
    I := SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)
    D := strictLocalNeighbourhoodDiagram f s
    c := Cone.mk _ Q.smallModelLegs
    isLimit := Q.smallModelIsLimit
    t := strictLocalNeighbourhoodProjection f s
    p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    «over» := Q.smallModelOver
    F := strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    e := E.e
    transition := E.transition
    sourceLegs := smallModel_strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    sourceIsColimit := hsource
    limitIso := smallModel_strictLocalBaseChangeTargetIso f s K n
    restriction := fun i ↦ E.restriction i }⟩

end AlgebraicGeometry.Etale
```

The direct consumer Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology changes:

```diff
-import Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation
+import Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateContinuityPresentation
-  obtain ⟨P⟩ := nonempty_strictLocalBaseChange_continuityPresentation f s K n
+  obtain ⟨P⟩ := smallModel_nonempty_strictLocalBaseChange_continuityPresentation f s K n
```

## Users

Complete current downstream.py census, also searched by declaration name. The only
direct importer and caller is StrictLocalBaseChangeGlobalHomology; no current
quarantined Lean file imports the withdrawn module. The two other modules are checked
unchanged against the adapted direct consumer. The module-system visibility changes
therefore preserve every actual consumer's statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | unclaimed | Private import and theorem-call rename; signature and proof argument preserved. |
| Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso | unclaimed | Unchanged; compiled against the adapted consumer and narrower public imports. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeModelGlobalHomology | unclaimed | Unchanged; compiled against the adapted consumer and narrower public imports. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateContinuityPresentation | new, G6 | Retains the exact original theorem under an unambiguous name. |

## Status

landed 20261023T042719-L-2050548 2026-10-23 (merge of deliver/G6/Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation)
