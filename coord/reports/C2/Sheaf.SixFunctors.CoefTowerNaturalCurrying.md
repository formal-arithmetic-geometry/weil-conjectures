## What changed

Pruned the unused, disputed theorem WeilConjectures.coefTowerNaturalCurrying from
Sheaf.SixFunctors.CoefTowerNaturalCurrying. All 27 surviving construction declarations
retain their signatures, bodies and attributes, and all public imports are unchanged.
The structure docstring now describes its data interface instead of referring to the
withdrawn existence theorem. Removed six unused proof imports listed below. The return
repair also removes the unused warn.sorry option that triggered the landing census.

The existing two definition nodes retain the module's Lean attachments: the quotient
tower node also records its target and target-evaluation constructions, and the model
node records all the other surviving constructions. The old theorem node has lean
explicitly null, while its mathematical statement and planned proof remain intact.

The current server queue classifies this item as disputed. The rework row and older
build-error file record a quarantine-related bad-import cascade. The original current
source compiled against the published artifacts in 44.8 seconds; the edited module
compiled in 46.1 seconds. This is an actual removal of the disputed declaration, not a
no-op restoration or a claim that this compile alone repairs quarantined dependencies.
The four direct consumers compiled unchanged against the changed file:
IntegralDualizingMappingTower (5.7 s), NormalizedTowerTensorEvaluation (39.3 s),
FiniteAdjunctionTransitionData (9.5 s), and FiniteAdjunctionTransition (9.7 s).
Their temporary source copies were removed after compilation. The same multi-file
run reported 105.1 s for the item, with exit code zero despite the longer elapsed
time. A subsequent profiler run completed in 47.1 s (kernel type checking 28.8 s,
elaboration 5.79 s), without any semantic change. The profiler options were removed
before delivery. The delivered unprofiled file is the version that compiled alone
in 46.1 s; the delivery probe and related-module checks validate it again.

Change record: coord/changes/C2-unused-arbitrary-trace-currying.md.

## Proved and sorry left

- Original item: one hole, WeilConjectures.coefTowerNaturalCurrying
  (lem-coef-tower-natural-currying).
- Proved: zero. The false unused declaration is removed, not proved or decomposed.
- Removed holes by pruning: one, WeilConjectures.coefTowerNaturalCurrying.
- Added holes: zero. Split-off theorems: zero. Remaining holes in this delivery: zero.

## No longer needed

The removed theorem WeilConjectures.coefTowerNaturalCurrying and its Lean attachment
on lem-coef-tower-natural-currying are unused. Both the current server DAG scan
(stmt_deps, proof_deps and every proof-step uses, including nodes of quarantined
parents) and a whole-library Lean search found no parent or consumer. Its unit
sk-prop-sf-biduality-general has no realized statement or step requiring it.

The existing replacement route is the coherent strict-tower comparison
WeilConjectures.integralDualizing_mapping_tower_finite_comparison in
Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComparison, node
lem-coef-integral-dualizing-mapping-tower-finite-comparison. It constructs the trace
from the actual finite exceptional counits and explicitly excludes the arbitrary-trace
claim. Its remaining proof obligation is unchanged. No parent rewrite is needed in
this delivery: the replacement route was already present in the current server DAG.

Removed these proof-only imports from the item:

- Sheaf.CategoryTheory.SequentialTowerEvaluationFull
- Sheaf.CategoryTheory.DiagramSiteRealization
- Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
- WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
- Mathlib.CategoryTheory.Abelian.FunctorCategory
- Sheaf.Algebra.Homology.ScalarInternalHomAdjunction

These are not claims that those modules are globally unused. The nonempty item module
remains needed by IntegralDualizingMappingTower, FiniteAdjunctionTransitionData,
NormalizedTowerTensorEvaluation and FiniteAdjunctionTransition. The surviving
quotient-tower and model nodes stay attached and every construction they need remains.
No module is withdrawn and deleted.txt is unnecessary.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old Lean statement quantified over arbitrary eTrace and required
only its composite with the finite trace, without compatibility with the pairing's
specified dualizing comparison. On two disjoint geometric points the canonical finite
trace is the row (1,1). The invertible matrix [[1,-1],[0,1]] changes it to (1,0),
compatibly at every quotient. For K supported on the second component, the specified
evaluation pairing lands in that component and this trace kills it. The curried map
is zero between nonzero towers, contradicting the asserted IsIso conclusion. All
dimension, constructibility and uniform finite Tor hypotheses hold in this example.

The blueprint and mathematical node require the actual compatible exceptional counits;
they do not justify this arbitrary-isomorphism formulation. Keeping this unused false
Lean declaration as an axiom-like hole would serve no target proof. The data interfaces
remain useful and are preserved; the correct mathematical statement and unit route are
unchanged. Current server records were read because the shared queue lacked the item's
current disputed row. Returned-delivery repair (reviewer C-61f10, head 61f1083f956): the reviewer passed
this pruning, but landing failed with <unattributed:41:1833>. The exact source-only
sorry_ledger.scan_text call reproduced the marker at set_option warn.sorry false.
Its qualified option name was counted as a literal hole outside a declaration.
Removing that unused warning-suppression option fixes the reported failure without
changing any surviving declaration. The repaired census reports zero hole rows and
zero lexer warnings, and sorry_ledger.missing_gate against current server main
returns no failures. No tool was changed. Node lean edits were reapplied to current
server records; all their other fields remain current. The delivery tool rebases
onto current sheaf-dag. The repaired module compiled on the server in 39.1 seconds, with no warnings.
The explicit delivery dry run passed compilation, all four related consumers and
server preflight (dry-run commit 6995ae9ff9b, CODEX review class). The push uses
the same repaired Lean source and rebased node edits.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefTowerNaturalCurrying": "3dc544a73d30c72cf18504f6c178134c12dbf4df"}, "results": {"Sheaf.SixFunctors.FiniteAdjunctionTransition": {"hash": "3a428e3f0f437e89c570bcd131849bdfba1181c9", "status": "OK"}, "Sheaf.SixFunctors.FiniteAdjunctionTransitionData": {"hash": "e1d9fceef133ba570f5850bae9577f162b492ed8", "status": "OK"}, "Sheaf.SixFunctors.IntegralDualizingMappingTower": {"hash": "07eabf7461c4984dac7cdddeee3d70a19a647ee1", "status": "OK"}, "Sheaf.SixFunctors.NormalizedTowerTensorEvaluation": {"hash": "9090a947c3f93cb84be42fb93e058c3b8f2c8b64", "status": "OK"}}, "seconds": 130, "time": "2026-10-28T10:09:12+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
