# AlgebraicGeometry.derivedPullbackComposition_counit_normalization

## Reason

Restore the quarantined module assigned by coord/rework.tsv. The current
WeilConjectures.AlgebraicGeometry.DerivedPullback defines derivedPullback with
irreducible_def. Lean rejects setting its local irreducibility again; this is
the recorded rework failure. Remove that redundant name from the local attribute
command, retaining the archived theorem and proof verbatim.

The upstream twin has the same correction already, but the retirement census
coord/changes/retire-sheaf-twins-kept-20261020.tsv keeps this Sheaf module because
its upstream twin reaches upstream copies of other retained dependencies.
Preserve both existing proof imports and the original DAG attachment.

## Old

```lean
attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullback
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh canonicalDerivedPullbackComposition schemeHomPullbackAdjunction
```

The assigned source is archived at
quarantine/Sheaf/AlgebraicGeometry/DerivedPullbackCompositionCounitNormalization.lean.

## New

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh canonicalDerivedPullbackComposition schemeHomPullbackAdjunction
```

The restored module compiles through lcompile.py in 28.9 seconds. The original
proof applies the pinned Hom normalization, the private counit_of_normalization
helper and derivedPullbackComposition_localized_counit. All remain unchanged.
The theorem has zero direct holes before and after this repair.
The attribute is local; derivedPullback keeps its upstream irreducibility.
All declaration signatures, universes, proof bodies, public and private imports,
options and docstrings are identical to the archive. No target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization | K3 | Restore the assigned module and remove the redundant local attribute entry. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit | unclaimed in the current local claim records; quarantined | Sole direct importer and theorem user; identical public statement and imports, no adaptation forced. |

A source search covered lean/Sheaf and quarantine/Sheaf. The archived parent uses
this theorem in the final mate_transpose_to calculation. Its own redundant local
attribute and quarantined public dependency are separate rework issues; restoring
this module does not cause them. No consumer or upstream module is edited.
The existing node lem-sc-derived-pullback-composition-counit-normalization retains
its Lean attachment and all statement and proof dependencies. No route changes.
The quarantine archive is preserved.

## Status

landed 20261020T153011-L-2862472 2026-10-20 (merge of deliver/K3/Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization)
