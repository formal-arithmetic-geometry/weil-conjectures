## What changed

Restored `Sheaf.AlgebraicGeometry.DerivedDirectImagePastedCounitNormalization`
from its quarantine archive and removed only `derivedPullback` from its local
irreducibility command. The source definition is now an `irreducible_def`;
reapplying the attribute caused the recorded build failure. The repaired file
compiled cleanly through `lcompile.py` (35.3 seconds).

The original proof is preserved: the pinned Hom normalization gives the two
individual counit equations; naturality and the composite-adjunction counit paste
them; injectivity of the inverse Hom equivalence yields the stated forward form.
The node, its attachment and dependencies, and the unit route remain unchanged.
Both quarantined direct consumers were read, including the consumer using
`import all` to access the private normalization helper; all their used
declarations are preserved verbatim. No consumer adaptation is forced.

Change record: `coord/changes/derived-pasted-counit-redundant-irreducibility.md`.

## Proved and sorry left

This is a zero-hole repair. The archived item has 0 sorries and the repaired item
has 0 sorries. Holes closed: none. Holes added: none. No statements are split off.
The proof of `AlgebraicGeometry.derivedDirectImage_pasted_counit_normalization`
(node `lem-sc-derived-direct-image-pasted-counit-normalization`) and the private
proved helpers `counit_of_normalization`, `pasted_counit` and `forward_of_counit`
are retained unchanged. Imported obligations are unchanged.

## No longer needed

No imports, nodes, modules or proof dependencies are pruned. Only the redundant
local attribute entry for the already irreducible `derivedPullback` is removed.
The upstream twin states the same theorem but its recorded import-closure twins
prevent treating this quarantined item as withdrawn. Its Lean attachment and
mathematical dependency route are preserved.

## Where the brief, the DAG or earlier work was wrong

The quarantine diagnostic correctly identifies the obsolete local attribute.
The earlier command predates the source library's `irreducible_def` for
`derivedPullback`. There is no mathematical statement or proof-route correction.
LeanFinder found generic derived-counit factorization lemmas; Loogle and grep
found `Adjunction.comp_counit_app`, already used by the existing proof. The local
source twin already omits the same redundant attribute entry.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
