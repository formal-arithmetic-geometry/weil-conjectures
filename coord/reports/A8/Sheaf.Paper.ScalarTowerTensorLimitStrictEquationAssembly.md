## What changed

Proved `WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare_of_representativeTransport`
in `Sheaf.Paper.ScalarTowerTensorLimitStrictEquationAssembly` without changing its statement.
Added a proved private categorical lemma `transport_all_bridges`: an equation for every
bridge on the image of an essentially surjective functor transports to every object.

The proof packages the scalar and tensor reduction maps as natural transformations
using the supplied realization maps and adjunction counits. Their composites with
the total-limit functor are natural. Essential surjectivity of the product good-complex
localization transports the assumed equality; specialize its bridge to the existing
completed scalar/tensor comparison. Only the two equal-universe scalar-extension
wrappers and component formulas are unfolded.

Added proof imports of `IntegralOperationsWellDefined` (with `all`, for its proved
private localization theorem) and Mathlib's product-localization API. Updated only
the assigned node's proof, proof dependencies, and proof origin. No existing public
signature, definition, instance, attribute, or public import changes.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare_of_representativeTransport`
(node `stage3-pur-scalar-tensor-limit-strict-equation-assembly`).

Zero holes remain in the item. Zero holes added, zero statements split off.
The private categorical helper is fully proved. The representative equality remains
an explicit theorem hypothesis; its separate producer is not assumed as a theorem
in this proof.

## No longer needed

Removed no existing import. No module is withdrawn or claimed to leave the targets'
import closure.

Removed these direct proof dependencies from the assigned node:

- `stage3-pur-scalar-tensor-limit-good-representatives`
  (`Sheaf.Paper.ScalarTowerTensorLimitRepresentativeTransport`): its conclusion is
  already supplied as `hRep`; importing its producer is unnecessary for transport.
- `stage3-pur-scalar-tensor-limit-strict-witness`
  (`Sheaf.Paper.ScalarTowerTensorLimitStrictWitness`): neither the witness structure
  nor its extraction theorem is used. The existing public import remains for the
  statement's infrastructure, and other consumers still use the witness module.
- `lem-pc-kflat-resolution`
  (`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`) and
  `lem-pur-kflat-change-of-rings-independent`
  (`Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`): no fresh
  resolution or scalar-preservation argument is needed; the existing proved
  good-complex localization supplies essential surjectivity.

The realization-model definitions and the existing completed comparison remain
needed. The original producer of the representative equality and every unit route
remain intact.

## Where the brief, the DAG or earlier work was wrong

The former proof plan repeated the representative-construction work even though the
Lean hypothesis already quantifies over every pair of good representatives and every
bridge map. Once the two composites are recognized as natural transformations, the
remaining assembly is a direct categorical transport argument. No fourth re-split is
needed.

The existing node's `stmt_deps` mentions the absent
`stage3-pur-scalar-tensor-limit-strict-equation-predicate`; the earlier G8 report says
that duplicate was removed. This delivery leaves statement metadata unchanged and
reports that inherited dangling reference for the maintainer.

Validation: `lcompile.py` compiled the assigned module successfully in 13.8 seconds,
with no compiler warnings or errors. The delivery command performs the declaration,
axiom, dependency, and preflight checks against the current server base.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ScalarTowerTensorLimitStrictEquationAssembly": "2dd554b942a48cf27af36dcee08d8a3db1807ba9"}, "results": {"Sheaf.Paper.ScalarTowerTensorLimitTransportAssembly": {"hash": "852ed0565aa9cc152bba17a7f1cbc31a07ff28bd", "status": "OK"}}, "seconds": 83, "time": "2026-10-28T10:18:16+0800", "transitive": 0, "version": 1}
```

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
