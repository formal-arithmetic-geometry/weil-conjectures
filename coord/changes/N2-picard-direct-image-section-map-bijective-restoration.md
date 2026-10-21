# AlgebraicGeometry.Scheme.picardDirectImageSectionMap_bijective

## Reason

Restore the complete quarantined implementation named in coord/rework.tsv, row
lem-sc-picard-direct-image-section-map-bijective. The live Lean path is absent
because of the 2026-10-20 cluster-restore rollback, not because of mathematical
withdrawal. The node and the unfinished parent still need this theorem.

The archive compiles unchanged against the current library in 26.8 seconds, with
no errors or warnings. Its complete proof already establishes the specified
fixed-map bijectivity: transport invertibility to the tensor pullback, apply
flat-invertible base change in the cartesian iterated-pullback square, compose
with the single-pullback comparison, use the degree-zero homology bijection,
and evaluate at one followed by the restriction along equal top opens.
The final functoriality calculation identifies this composite with exactly the
fixed section map. No nonemptiness or higher-cohomology vanishing is assumed.

This packet restores a zero-hole theorem; it is an actual source addition to
the live library. It introduces no new mathematical assumption, statement,
definition, choice, axiom, or proof obligation.

## Old

The live path lean/Sheaf/AlgebraicGeometry/PicardDirectImageSectionMapBijective.lean
is absent. Its preserved quarantine source has this exact signature:

```lean
theorem picardDirectImageSectionMap_bijective
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) {T : Scheme.{v}} (t : T ⟶ W) :
    Function.Bijective (picardDirectImageSectionMap f L W k t)
```

## New

Restore the module byte for byte from
quarantine/Sheaf/AlgebraicGeometry/PicardDirectImageSectionMapBijective.lean.
The restored signature is unchanged:

```lean
theorem picardDirectImageSectionMap_bijective
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) {T : Scheme.{v}} (t : T ⟶ W) :
    Function.Bijective (picardDirectImageSectionMap f L W k t)
```

All binders, universes, hypotheses, declaration visibility, the proof body, five
public imports and four private proof imports are preserved. Only the node's
Lean restoration metadata changes. No target statement or interpretation changes.

## Users

The live module is missing, so the live downstream inventory alone cannot find
its archived consumers. The combined lean/ and quarantine/ import graph, using
the live source whenever both exist, has one direct importer and fourteen
transitive importers. They are all separate quarantined rework assignments.
The direct importer PicardDirectImageSectionNaturality constructs AddEquiv.ofBijective
from the fixed map and this exact theorem. That use, including all flatness,
properness, finite-presentation and invertibility hypotheses, is preserved.
The parent DAG node lem-sc-picard-direct-image-section-naturality still lists
this node in its proof dependencies and proof step uses. Its attachment remains.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapBijective | N2 | Restore the complete archived theorem and proof. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionNaturality | separate quarantined rework; not adapted | Direct proof importer; the original theorem type and visibility are restored. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | separate quarantined rework; not adapted | Transitive importer; unchanged theorem type, visibility and imports require no adaptation. |

No consumer adaptation is forced by an identical restored interface. No consumer
or adopted-source file is changed. The delivery's independent reader checks the
source identity, consumer inventory, node attachment and original statement.

## Status

landed 20261021T021920-L-2792513 2026-10-21 (merge of deliver/N2/Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapBijective)
