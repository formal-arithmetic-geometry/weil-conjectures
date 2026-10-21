# AlgebraicGeometry.derivedPullbackComposition_mate_unit

## Reason

Restore the quarantined stage-3 item listed in coord/rework.tsv. Compiling the
archived source reports at line 28 that Lean cannot set `[local irreducible]` on
`derivedPullback`, which is already irreducible. The current adopted source defines
it using `irreducible_def`. Remove that redundant local attribute entry, preserving
the complete archived proof and interface.

The retirement census coord/changes/retire-sheaf-twins-kept-20261020.tsv keeps this
Sheaf module: replacing it by the upstream twin would expose upstream copies of
other retained dependencies. Preserve its existing public and proof imports and
DAG attachment. The quarantine archive is not changed.

## Old

```lean
attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullback
  schemeHomPullbackAdjunction
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Adjunction.comp DerivedCategory.Qh
```

The assigned source is
quarantine/Sheaf/AlgebraicGeometry/DerivedPullbackCompositionMateUnit.lean.

## New

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback
  schemeHomPullbackAdjunction
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnit
  CategoryTheory.Adjunction.comp DerivedCategory.Qh
```

The existing irreducibility of derivedPullback remains in force. The theorem,
private proved helpers, signatures, universes, options, documentation and all imports
are verbatim from the archive. There is no change to a definition or to the proof
route, and no target statement review is reopened. The archived and restored module
both have zero direct proof holes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit | N4 | Restore the assigned source and remove the rejected local attribute entry. |
| WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate | not adapted | Uses the same theorem name through the upstream twin; does not import this Sheaf module. |

A source search of lean/Sheaf, lean/WeilConjectures and quarantine/Sheaf finds no
current Lean importer of the Sheaf module. tools/downstream.py cannot enumerate an
absent quarantined module and reports it as unknown. The node
lem-sc-derived-direct-image-square-mate still cites this node in its first proof
step and proof_deps; its current Lean attachment is the upstream square-mate module.
Its application at line 89 was read and needs exactly the preserved statement.
No consumer adaptation is forced. The node and both declared counit-normalization
dependencies are retained unchanged, as is the unit route in sk-thm-picard-duality.
No upstream file is edited.

## Status

landed 20261021T214847-L-1871806 2026-10-21 (merge of deliver/N4/Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit)
