## What changed

Completed `WeilConjectures.RationalOperations.scalarEvaluation_of_normalizedCounits`
in `Sheaf.SixFunctors.RationalHomScalarEvaluationCore`, preserving its statement.
Added proof-only imports of `Sheaf.Paper.RationalHomScalarTranspose` and
`Sheaf.Paper.RationalTensorSymmetry`. A proved private helper derives the inverse
transpose formula from parameter naturality. The main proof applies scalar
transpose compatibility to evaluation, then uses braiding naturality and scalar
braiding compatibility to obtain the normalized counit square.

Updated the item's DAG proof and dependency records to this argument. Removed
one unused public import of `RationalOperations` from the unclaimed
`Sheaf.Paper.RationalHomScalarTranspose` module, and its corresponding stale
statement-dependency edge, to break the import cycle through this item. The
transpose theorem retains its exact signature and body; no shared definition
changed. This import correction is recorded in
`coord/changes/A4-rational-hom-scalar-transpose-import-pruning.md`.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.RationalOperations.scalarEvaluation_of_normalizedCounits`
(`lem-sf-rational-hom-scalar-evaluation-core`). The item now has zero `sorry`.
No holes were added and no statements were split off. The proof uses the existing
stated dependencies `WeilConjectures.rationalHomScalar_transpose` and
`WeilConjectures.rationalTensorSymmetry_laws`; their proofs are outside this
packet. The changed transpose module retains its one pre-existing hole in
`WeilConjectures.rationalHomScalar_transpose`
(`lem-coef-rational-hom-scalar-transpose`); no new hole was introduced. The item and the trimmed transpose module compiled cleanly through
`lcompile.py --all`, in 6.9 and 9.6 seconds respectively. Both original direct
importers compiled unchanged against the pruned import:
`Sheaf.Paper.AdicCommonStageHomTranspose` (9.9 seconds) and
`Sheaf.SixFunctors.RationalRetractEvaluation` (15.5 seconds). Their temporary
sandbox copies were removed after comparison with the originals.

## No longer needed

Removed `public import Sheaf.SixFunctors.RationalOperations` from
`Sheaf.Paper.RationalHomScalarTranspose`: its statement does not use the
operations-identification theorem. Removed the matching stale statement
dependency `lem-coef-rational-operations` from the transpose node. This breaks
the import cycle; `RationalOperations` itself remains needed elsewhere and is
not withdrawn. No original import of the assigned item was removed and no
modules are withdrawn. The proof uses
the definition of `normalizedCounit`, but does not need to prove counit
normalization: both normalization equations are hypotheses of this theorem.
The old proof-dependency references `lem-sf-rational-hom-normalized-counit` and
`lem-sf-rational-hom-scalar-transpose` are replaced by the actual existing node
identifiers used in the proof. This correction does not withdraw their parent
arguments or claim that any other module is unused.

## Where the brief, the DAG or earlier work was wrong

The original proof plan cited node names that do not identify the available
normalization definition or scalar transpose theorem. The required transpose
result is `lem-coef-rational-hom-scalar-transpose`. Its tensor order is Hom-first,
whereas normalized counits are argument-first; the explicit bridge uses
`lem-coef-rational-tensor-symmetry-laws`. The resulting calculation closes the
whole obligation without another split or any statement change. Delivery's
source import-cycle check also exposed the redundant `RationalOperations`
import in the transpose module, which a single-file compile against published
artifacts did not detect. Removing that unused dependency makes this proof route
acyclic without changing any declaration.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.RationalHomScalarTranspose": "9155b053b92b7771813ea2a54b1f5514a130de09", "Sheaf.SixFunctors.RationalHomScalarEvaluationCore": "dc428c0f18d4faa0b490e5a418107686db1ff673"}, "results": {"Sheaf.Paper.AdicCommonStageHomTranspose": {"hash": "b1de91655e42ead8ad785ab4154adf04c70baa14", "status": "OK"}, "Sheaf.SixFunctors.RationalHomScalarEvaluation": {"hash": "4f92c3e988d7a0336ab55a6085a6acb1d9860dc2", "status": "OK"}, "Sheaf.SixFunctors.RationalRetractEvaluation": {"hash": "51c241d8ad79d710a587aab9d53b0e148eee03e4", "status": "OK"}}, "seconds": 57, "time": "2026-10-28T10:26:14+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
