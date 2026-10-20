## What changed

Restored the quarantined module Sheaf.AlgebraicGeometry.TorsionExchangeFilteredPassage
from its coord/rework.tsv archive. In the proof of
AlgebraicGeometry.Etale.isIso_exchange_of_isIso_torsion_pieces, replaced the retired
Scheme.PositiveNat alias with its original body PNat.DvdOrder. This repairs the
unknown-identifier error and the consequent filtered-index instance failures.
The filteredness construction, torsion argument, colimit comparison, component
exchange hypothesis and naturality transport now compile against the current library.
Replaced the thin-category parallel-map equality tactic with rfl.
Removed the unused private coefficient import; retained both public imports.

The theorem signature and docstring are verbatim from the archive. Its node attachment
and both proof dependencies are preserved; the existing proof plan still describes
the Lean proof exactly, so no node field is changed. The archived consumer
Sheaf.Targets.BaseChangeTowardsFields applies this exact theorem in
baseChange_towardsSpecField; its application and coefficient visibility require no
adaptation. No upstream source or target statement is changed.

Validation: single-file lcompile.py compiled the final restored module cleanly in
8.0 seconds. The initial alias-only repair also compiled. The statement was compared
verbatim with the archive. Searches used LeanFinder, Loogle, and local rg; the existing
colimit and naturality lemmas already supply the shortest route.

Change record: coord/changes/a3-torsion-exchange-filtered-passage-restore.md.

## Proved and sorry left

The assigned item is a quarantined compile repair, with zero original textual holes.
AlgebraicGeometry.Etale.isIso_exchange_of_isIso_torsion_pieces is restored with a
complete proof from its existing declared dependencies
(blueprint: lem-kun-torsion-exchange-filtered-passage).
Holes closed: 0. Holes added: 0. Holes remaining in the delivered module: 0.
No theorem is split off, and no definition contains a hole.

## No longer needed

Removed the unused proof import
WeilConjectures.SixFunctors.Etale.Derived.Coefficients.
No DAG dependency, node, or module is withdrawn: InvertibleOrdersColimit and
AbelianExchangeFilteredColimit are both used. This import removal does not assert
that the coefficient module is globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The archived proof referred to Scheme.PositiveNat, an abbreviation retired by
coord/changes/retire-torsion-etale-sheaf.md. Its expanded type PNat.DvdOrder is
exactly the current fieldInvertibleTorsionDiagram index. The mathematical statement
and its two-step DAG proof need no correction. The rework row correctly identifies
the obsolete identifier; restoring the archive rather than withdrawing its node
preserves the unfinished parent's intended dependency.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
