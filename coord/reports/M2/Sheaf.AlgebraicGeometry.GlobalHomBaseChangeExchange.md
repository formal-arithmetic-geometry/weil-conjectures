## What changed

Restored lean/Sheaf/AlgebraicGeometry/GlobalHomBaseChangeExchange.lean from the
quarantine source prescribed by coord/rework.tsv. The original public theorem
AlgebraicGeometry.schemeGlobalHom_baseChange_exchange, its complete signature, and
its public import are preserved. Added a proved private equality identifying the
compatibility schemeGlobalSectionsDirectImageIso with the adopted
mixedGlobalSectionsDirectImageIso, and use it in the final normalization. This fixes
the actual archived compile error after source adoption. No definition changes.

The proof still combines schemeInternalHom_baseChange_exchange with
schemeGlobalSections_baseChange_mate via the existing proved private adjunction
naturality argument. The node's final step and proof_origin now record the extra
normalization; all existing dependencies and the Lean attachment remain.

Validation: archived source reproduced the final simpa type mismatch. The repaired
module compiled without warnings (24.2 seconds with original imports; 36.7 seconds
with pruned imports). An artifact-producing compile of a separate check sandbox
compiled the repaired module in 39.5 seconds and a public consumer in 5.2 seconds.
The consumer repeats the exact archived exchange signature and proves it by applying
the repaired declaration. Signature comparison against the archive was byte-identical.
The private equality's axiom check showed only propext, Classical.choice, Quot.sound.
Line lengths are at most 100 characters.

Change record: coord/changes/M2-global-hom-exchange-Leray-compatibility.md.

## Proved and sorry left

Assigned repair completed for AlgebraicGeometry.schemeGlobalHom_baseChange_exchange
(node lem-sc-global-hom-base-change-exchange). The archived item already had zero
textual holes: 0 of 0 holes closed, 0 holes added, 0 split off, 0 left in this module.
The new private schemeGlobalSectionsDirectImageIso_eq_mixed is proved by rfl.
This is a compile repair, not a claim of new sorry reduction.

The existing imported dependency declarations
AlgebraicGeometry.schemeInternalHom_baseChange_exchange
(lem-sc-internal-hom-base-change-exchange) and
AlgebraicGeometry.schemeGlobalSections_baseChange_mate
(lem-sc-global-sections-base-change-mate) still have their original sorry proofs.
They are not changed or split off by this delivery. The repaired theorem continues
to use them as authorized stage-3 proof dependencies; its closure is not claimed to
be axiom-free until those existing items are proved.

## No longer needed

Removed redundant private imports, with successful recompilation:

- WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
- Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
- WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
- Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
- WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap

Their required declarations remain available from the unchanged public comparison
import. No dependency node, module, public declaration, or unit route is withdrawn.
Both planned exchange dependencies remain used and imported. The adopted mixed
exchange theorem was inspected as a potential shorter route; its tensor and
internal-comparison constructions differ, so the existing two-dependency proof is
retained and repaired directly.

## Where the brief, the DAG or earlier work was wrong

This is a quarantined zero-hole repair, not a fresh unproved exchange statement.
The archive's final normalization predates source adoption: the direct-image
comparison now uses mixedGlobalSectionsDirectImageIso while the retained pullback
comparison and global-sections mate use schemeGlobalSectionsDirectImageIso. Their
equality is definitional/proof-irrelevant, but the archived final simpa did not list
that rewrite. Globally expanding the large constructions in the final equation hit
the 60-second limit; extracting their small equality solved that problem without
changing definitions or the limit. No mathematical statement or blueprint step is
rejected, and the quarantine archive and the parent dependency are preserved.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
