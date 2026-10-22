## What changed

Restored Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison from its
quarantine archive. Replaced its public import of the withdrawn Sheaf structural-map
wrapper by WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap. The theorem
signature, docstring and proof are unchanged. The node retains its Lean attachment, proof,
proof dependencies and proof origin; its Lean statement now records the archive's actual
IsTorsionModuleSheaf spelling.

The proof applies projectiveLine_originalStalk_totalCohomologyExchange and
exists_addEquiv_strictLocal_totalCohomology_exchange, then composes the first pair of
additive equivalences with the inverses of the second. Injectivity and the two exchange
identities give the conclusion. Both dependencies are used and remain imported privately.
The sk-thm-p1 unit route is preserved. The repaired single file compiles on the project
server without errors or warnings (29.4 seconds).

Searches: LeanFinder returned scheme-stalk identities rather than this exchange theorem;
Loogle confirmed AddEquiv.trans_apply; the Mathlib grep found no strict-local exchange
comparison. The adopted source comparison has different model hypotheses, so the
existing two-dependency argument is retained.

Change record: coord/changes/C3-strict-local-stalk-exchange-restoration.md.

## Proved and sorry left

This is a quarantined import repair with zero original holes, zero holes closed and zero
holes added. AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison
retains its complete existing proof (node
lem-weil-pbc-p1-strict-local-stalk-exchange-comparison). No sorry remains in the item;
no new declarations or split-off lemmas are added. This restoration is not claimed as
net proof-hole progress.

## No longer needed

Removed the obsolete public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap,
which is already withdrawn and empty. No mathematical dependency, node, or additional
module is pruned. Both existing proof dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean because it is quarantined, not because the
comparison was withdrawn. The archive has zero sorry holes. Its structural-map import
became unusable after the wrapper was retired. The original server compile confirms
unknown identifiers strictHenselizationScheme and strictHenselizationStructuralMap in
its public signature. Importing their source-library owner repairs that exposure.

The existing node's Lean statement still used IsTorsionSheaf, while the archive already
uses IsTorsionModuleSheaf; only that record is refreshed. The canonical source theorem
uses different strictLocalization hypotheses, so substituting it would change the
archived statement. No source-library file or quarantine archive is changed.

The first compiler attempt selected a local mirror lacking Mathlib.olean. Subsequent
compiles use lcompile.py's supported LCOMPILE_NO_LOCAL=1 setting to use the project server.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
