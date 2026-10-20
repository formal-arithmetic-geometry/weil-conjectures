# AlgebraicGeometry.kFlat_pullback_adjunction_comparison

## Reason

Restore `Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison` from its
`coord/rework.tsv` quarantine after upstream sync `5f7b33eac`. The archived
statement and private helper refer to `CochainComplex.IsAcyclicTensorKFlat`.
The upstream public import closure now exports `CochainComplex.IsKFlatTensor`
instead. Add a direct public import of the existing module defining the former
predicate, because the public statement needs it. Both predicates express the
same acyclic-total-tensor condition and are definitionally equal in the scheme
universes. The existing proof consumes the upstream K-flat counit without a
conversion lemma. No declaration signature, definition, or proof body changes.

## Old

The archived module header is:

```lean
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
```

The module is absent from `lean/`, preserved at
`quarantine/Sheaf/AlgebraicGeometry/KFlatPullbackAdjunctionComparison.lean`.
Its full archived statement and proof are restored verbatim.

## New

```lean
module

public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
```

Only this statement-dependency import is added to the archived source.
The comparison is still simultaneous in all target complexes and chain maps,
with exactly the original K-flat hypothesis and pinned adjunction.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison
--allow-missing --uses AlgebraicGeometry.kFlat_pullback_adjunction_comparison`
reports no active downstream modules: the module and its dependent tree are
quarantined. A source search including quarantine finds the following direct
importer and sole external use of the theorem. Its source and DAG dependency
are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison | G2 | restore archived declarations and add the public import needed by their unchanged types |
| Sheaf.AlgebraicGeometry.DerivedPullbackConeSquareTransposition | quarantined; unchanged | its K-flat hypotheses and application retain exactly the same types; full archive compilation is blocked by an independent duplicate derivedPullback import |

The full unchanged archived consumer was tried with `lcompile.py`; it fails
before elaborating its declarations because one of its other imports loads
`Sheaf.AlgebraicGeometry.DerivedPullback` into an environment already containing
`AlgebraicGeometry.derivedPullback` from
`WeilConjectures.AlgebraicGeometry.DerivedPullback`. This is its pre-existing
quarantine/import-migration defect, not a signature change from this repair.
A separate scratch consumer checks the original comparison theorem signature
and the definitional conversion to the upstream K-flat predicate.

The item node and its parent node
`lem-pc-derived-pullback-cone-square-transposition` remain attached and unchanged.
No target statement or definition used by a target is changed. Import-direction
check confirms the added import introduces no cycle.

## Status

landed 20261020T145511-L-2403379 2026-10-20 (merge of deliver/G2/Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison)
