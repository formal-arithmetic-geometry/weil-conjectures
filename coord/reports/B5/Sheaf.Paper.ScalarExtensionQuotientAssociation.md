## What changed

Added `Sheaf.Paper.ScalarExtensionQuotientAssociationDegreeData`, which states the
strictly smaller degreewise normalized association problem. The item theorem now
assembles its component isomorphisms with `HomologicalComplex.Hom.isoOfComponents`
and transfers the displayed section formula.

## Proved and sorry left

The item theorem `WeilConjectures.ScalarExtensionTower.quotientAssociation_exists`
is proved from the degreewise assembly. One strictly smaller theorem remains sorry:
`WeilConjectures.ScalarExtensionTower.quotientAssociation_degreeData_exists`, in
`stage3-pur-scalar-quotient-association-degree-data`.

## No longer needed

None. The parent needs the degreewise association and the existing reduction and
realization interfaces. No imported node or module was pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan conflated the finite balanced association calculation with
its whole strict sequence-site assembly. The delivery separates these into a
componentwise theorem and a short, real complex assembly.

## New nodes

`stage3-pur-scalar-quotient-association-degree-data` records the finite degreewise
association and differential compatibility left for a subsequent worker.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ScalarExtensionQuotientAssociation": "f468fed4b4134179803b9837812a44cb5ed6ce06", "Sheaf.Paper.ScalarExtensionQuotientAssociationDegreeData": "7cd78266ebb132eee31da341e85468db9df178e0"}, "results": {}, "time": "2026-10-28T00:19:01+0800", "transitive": 0, "version": 1}
```

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
