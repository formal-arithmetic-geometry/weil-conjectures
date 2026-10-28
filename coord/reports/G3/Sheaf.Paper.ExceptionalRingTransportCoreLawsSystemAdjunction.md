## What changed

Repaired `TransportCoreData` in `Sheaf.Paper.ExceptionalRingTransportCoreData`:
`realizeG` is now the explicit right-adjoint uniqueness comparison determined by
`adjunction`, `realizeF`, the two reconstruction equivalences and the given integral
operation adjunction. It is no longer an arbitrary record field. The data
constructor no longer copies `p.realizeG`. No compatibility hypothesis or unproved
existence witness was added.

In the assigned module, `normalizedRealizeG` abbreviates that definition and
`normalizeRealizeG` returns the already normalized datum. The existing uniqueness
proof proves the assigned adjunction law with its written signature unchanged.
The pointwise, twist and sign diagnostics now quantify over arbitrary comparison
isomorphisms with fixed data. Their former record updates would be invalid after
the definition repair; no external caller uses these lemmas.

Updated four existing nodes: data, system adjunction law, canonical comparison and
comparison obstruction, with explicit statement-change/citer audits. The data node
records ownership of the structure and derived `realizeG`. No new node was added.

Source read: Zheng, pp. 35-37, especially Lemma 5.22, Construction 5.25 and
Propositions 5.24 and 5.26; current blueprint compatibility unit. Mathlib
`rightAdjointUniq` and the source-library `ofNatIsoRight_eq_iff` give the shorter
route. LeanFinder, Loogle and grep were run through `msearch.py` and their
signatures checked in the local sources.

Change record: `coord/changes/exceptional-core-canonical-realizeG.md`.

## Proved and sorry left

Closed 1 of 1 holes in the assigned module, after the explicit definition repair:
`WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_core_system_adjunction_law`
(node `lem-sf-exceptional-ring-transport-core-system-adjunction-law`).
The original false arbitrary-comparison interpretation is not claimed proved.
The written theorem signature is unchanged, while its data type is repaired.

Item holes remaining: 0. New holes: 0. Split-off holes: 0.
The adapted data module also contains 0 holes. All existing uniqueness and
obstruction results remain completely proved, and both normalization definitions
have complete bodies. The proof uses provided adjunctions and the proved generic
uniqueness API, without any other transport law or its unfinished proof.

Validation: `lcompile.py --all` compiled all 14 files without errors or warnings,
one file at a time in import order. The changed data and item took 14.0 s and
16.0 s; all 12 unchanged consumers took 6.8–15.4 s. This included every direct
importer, the indirect support-maps user, and the final core assembly. All 12
temporary unchanged copies were then removed. The import closure still contains
inherited unfinished results; this delivery does not claim the entire
exceptional transport construction is axiom-free.

## No longer needed

The system adjunction law no longer depends on
`lem-sf-exceptional-system-adjunction-comparison-obstruction`; its new proof uses
only the canonical-comparison node and the repaired data definition. The proved
obstruction lemmas and node remain available as diagnostics for arbitrary
comparison families. No existing Lean module is withdrawn.

Removed the item's redundant direct public import of
`Mathlib.CategoryTheory.Adjunction.Unique`; it is now needed for the canonical
public definition in the data module, which publicly reexports it. The proof-only
import of `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique` remains needed.
No unit-level route is pruned and no new proof dependency chain is split off.

## Where the brief, the DAG or earlier work was wrong

The earlier split confused a constructed adjunction-compatible comparison with an
arbitrary natural isomorphism. The previously proved iff and twist obstructions
correctly exposed the error but left the original hole. This repair fixes its
source: the right comparison is computed canonically, rather than asserted to
satisfy a law for every independent choice.

This is a semantic definition change and is explicitly recorded, rather than a
proof of the old unrestricted assertion. Final `Transported` statements and all
five challenge targets are unchanged. The unit still reconstructs the system
adjunction through the specified equivalences and retains its unit/counit law.

Edge cases: the uniqueness construction works for empty schemes and zero
categories, with no nonidentity assumption. The diagnostics still require an
explicit nonidentity automorphism or sign component; identity twists and zero
categories do not satisfy that premise. No nonemptiness of schemes, odd-prime
restriction, extra geometric hypothesis or new axiom was added.

Other independent arbitrary data fields still have unfinished law statements,
including reductionG, evaluation and integral-left normalization. This delivery
repairs the adjunction comparison only and does not claim those statements follow
from the remaining arbitrary record fields.

## Related modules compiled before delivery

12 related module(s) compiled against this delivery by deliver3.py: 3 INFRA, 9 OK.

```json
{"capped": false, "direct": 10, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCoreData": "11434efccc00256fbcfaa273b1898d12aed8a3de", "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemAdjunction": "d7ba9a28a725864ad3dd9797fab91dce0223e92c"}, "results": {"Sheaf.Paper.ExceptionalRingTransportCore": {"hash": "87222536a47dc08a48ed436e6a8378b42f61ec3c", "status": "INFRA"}, "Sheaf.Paper.ExceptionalRingTransportCoreEvaluationCounit": {"hash": "520a81f5f514b2ce588afa443ef16ef9b5d656ab", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreEvaluationSupport": {"hash": "4a09a7a3107b7cc6cae51e582ea6cb47e92ce0bf", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreEvaluationUnit": {"hash": "64d50027cc635a70b1b31897ca0b9b52477fc3ff", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLaws": {"hash": "b259262fe74d3b4e12841ffc4857a6dfbe5aca00", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation": {"hash": "bca3f579773ede1a6113fa23dd19db6fa3adb7ed", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization": {"hash": "30d30a6c6df80b01386b1bf09686cc0f84e44866", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem": {"hash": "4165610bc155c7566a70f987503df48599e484ad", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemReduction": {"hash": "5ff474c8ac27f502c85c04dbb33f531c193d0546", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupport": {"hash": "6d2bef3e85c92b3628d5f2106f8e229088731001", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportMaps": {"hash": "1e84097ea867d45a330b30dcf4e113760353d83d", "status": "INFRA"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupportObjects": {"hash": "12b981994ee2cf7f655db03e81492237d318009f", "status": "INFRA"}}, "seconds": 144, "time": "2026-10-28T12:03:36+0800", "transitive": 2, "version": 1}
```

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
