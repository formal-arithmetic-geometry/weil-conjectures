## What changed

Repaired `Sheaf.Paper.ExceptionalRingTransportCoreData`: `reductionF` and
`reductionG` are now explicit canonical definitions from `realizeF`/`realizeG`,
reconstruction counits, and Mathlib isomorphism whiskering. They keep their public
names and types. Removed the two redundant record fields and their only
constructor assignments. All remaining data fields and their existence proof are
retained. No target statement is changed.

Proved `exists_exceptional_transport_core_system_reduction_laws` in the assigned
module by evaluating the two canonical comparisons at an object and simplifying
the terminal identity. Its statement text and public imports are unchanged.
Updated the data and reduction-law nodes to describe this construction and proof,
including the two canonical definition names in the data node's Lean attachment.
No new nodes, proof dependencies, or imports were introduced.

Change record: `coord/changes/G7-canonical-exceptional-reduction-comparisons.md`.

Validation: `lcompile.py --all` compiled the two changed modules, all ten direct
importers (including the item), and the final core assembly, one file at a time
in import order, with no errors or warnings. The twelve files took 6.8–13.4 seconds
each in the final run; the assigned theorem module took 7.4 seconds. All unchanged
consumer copies were removed from the delivery sandbox after these checks.

## Proved and sorry left

Closed the one assigned hole:
`WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_core_system_reduction_laws`
(node `lem-sf-exceptional-ring-transport-core-system-reduction-laws`), following
the explicit definition repair recorded above. The old theorem was not established
for independent, unnormalized choices of the reduction comparisons.

The item now contains zero `sorry`; `ExceptionalRingTransportCoreData` also
contains zero `sorry`. No holes added and no statements split off. The existing
post-functor-data and other transport-law obligations are not proved by this
change. In particular the independent adjunction, evaluation, support, and
integral normalization obligations remain with their assigned modules.

## No longer needed

No imports, modules, or nodes pruned. The normalized core construction no longer
uses `TransportCorePostData.reductionF` or `TransportCorePostData.reductionG`;
their source modules and other fields remain necessary and are retained.
No source-library declaration was changed or removed.

## Where the brief, the DAG or earlier work was wrong

The earlier split made the reduction comparison isomorphisms arbitrary data and
then requested their prescribed counit formulas for every such datum. The
reconstruction-counit calculation only computes the specified comparison; it
cannot identify an independent choice of isomorphism with that map. This was a
statement/interface defect, resolved by constructing both comparisons explicitly
instead of leaving another `sorry` for the same missing coherence. This is below
the unit route and retains every step of `sk-thm-sf-compatibility`.

Searches used `msearch.py` with LeanFinder (reconstruction-counit comparison),
Loogle (`CategoryTheory.isoWhiskerLeft`, unknown in that search service), and grep
(`isoWhisker(Left|Right)|def associator`). Local sources confirmed the current
Mathlib names `Functor.isoWhiskerLeft` and `Functor.isoWhiskerRight`, their component
formulas, and `Functor.rightUnitor`. Read Zheng Constructions 4.1 and 5.25,
Lemma 5.22, and Proposition 5.26 from the supplied PDF. These are specified maps;
there is no assertion of equality between freely chosen comparison isomorphisms.
The construction works for arbitrary functors and equivalences, including empty
and zero categories, with no extra hypothesis or nonzero-object assumption.

## Related modules compiled before delivery

10 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 9 OK.

```json
{"capped": false, "direct": 9, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCoreData": "6c18d0eb642a2b1cbaf900de572fc24e71335d35", "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemReduction": "43c85ef9a0f088e2905104f09399a3dbcb52337a"}, "results": {"Sheaf.Paper.ExceptionalRingTransportCore": {"hash": "87222536a47dc08a48ed436e6a8378b42f61ec3c", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreEvaluationCounit": {"hash": "520a81f5f514b2ce588afa443ef16ef9b5d656ab", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreEvaluationSupport": {"hash": "4a09a7a3107b7cc6cae51e582ea6cb47e92ce0bf", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreEvaluationUnit": {"hash": "64d50027cc635a70b1b31897ca0b9b52477fc3ff", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLaws": {"hash": "b259262fe74d3b4e12841ffc4857a6dfbe5aca00", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation": {"hash": "bca3f579773ede1a6113fa23dd19db6fa3adb7ed", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization": {"hash": "30d30a6c6df80b01386b1bf09686cc0f84e44866", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem": {"hash": "4165610bc155c7566a70f987503df48599e484ad", "status": "INFRA"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemAdjunction": {"hash": "770c08c984cbcd9718cfc33d3d30564b319efa15", "status": "OK"}, "Sheaf.Paper.ExceptionalRingTransportCoreLawsSystemSupport": {"hash": "9d306bdd90ed0d93d725f36f40984d20361f5644", "status": "OK"}}, "seconds": 137, "time": "2026-10-28T10:20:20+0800", "transitive": 1, "version": 1}
```

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
