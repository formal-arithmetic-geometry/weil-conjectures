## What changed

Restored lean/Sheaf/CategoryTheory/MappedSmartTruncationTower.lean verbatim from
its quarantine archive. The recorded DoubleComplexTotal collision is resolved
by the dependency import migration already landed in main. Included exact current
copies of DoubleComplexTruncationDecalage and SmartTruncationDecalageTower to
recompile their migrated imports in the sandbox; neither source changes.

The complete finite-limit argument, concrete tower constructions and naturality
proof are retained. Each dependency and the item compiled individually within
60 seconds. The exact quarantined direct consumer
CartanEilenbergSmartTruncationSpectralObject also compiled unchanged (7.6 s),
then its temporary source copy was removed. The item's node, proof dependencies,
Lean attachment and parent obligations are preserved. Change record:
coord/changes/C1-mapped-smart-truncation-tower-restoration.md.

## Proved and sorry left

This is a zero-hole quarantine restoration, not a newly closed proof hole.
The archive contains 0 sorries; the restored module contains 0 sorries.
Holes closed: none (0). Holes added: none (0). Holes split off: none (0).
A server-side #print axioms probe of all five restored declarations reported only
propext, Classical.choice and Quot.sound (2.1 s); no sorryAx occurs.

The restored completed declarations are:
- CategoryTheory.embeddingUpNat_extend_preservesLimitsOfShape;
- CategoryTheory.CartanEilenbergPresentation.mappedSmartTruncationTower;
- CategoryTheory.CartanEilenbergPresentation.mappedSmartTruncationTowerMap;
- CategoryTheory.CartanEilenbergPresentation.mappedSmartTruncationTowerIso;
- CategoryTheory.CartanEilenbergPresentation.mappedSmartTruncationTowerIso_naturality.

The three definitions retain concrete constructions. The extension proof treats
nonnegative degrees by evaluation and negative degrees by the zero functor;
whiskering the existing truncation comparison gives the tower isomorphism, and
totalizing its naturality square proves the concluding theorem.

## No longer needed

None. No imports, declarations, nodes or modules are pruned. In particular,
lem-sp-extended-smart-truncation-map-iso and
lem-sp-smart-truncation-decalage-tower remain needed, as does the presentation
node. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item is assigned for quarantine restoration, rather than because it contains
an unfinished proof: its archive is already fully proved. The recorded collision
still occurs with the published compiled dependency snapshot, but current source
imports have already been migrated by the DoubleComplexTotal retirement.
Recompiling those current dependencies verifies the complete restored module.
The absence of its source is not withdrawal; its DAG attachment and quarantined
consumers remain relevant and are retained.

Searches: LeanFinder returned homological-complex evaluation/finite-limit APIs;
Loogle found no HomologicalComplex.extendFunctor identifier; Mathlib grep found
no ready extension-preserves-limits theorem. The existing direct argument uses
the evaluation API and needs no new lemmas or nodes.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
