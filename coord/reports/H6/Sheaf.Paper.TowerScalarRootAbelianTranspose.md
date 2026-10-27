## What changed

Replaced the `sorry` in `scalarRoot_abelianTranspose` by a genuine categorical
extensionality proof. The proof reduces equality of the two tower morphisms to
finite-level section equality and invokes the new component theorem. Added the
new module `Sheaf.Paper.TowerScalarRootAbelianTransposeComponent`, whose theorem
is the strictly smaller pointwise finite-level statement and is left for a
subsequent worker.

## Proved and sorry left

- Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.scalarRoot_abelianTranspose`.
- Added one strictly smaller named theorem, with its proof left as `sorry`:
  `AlgebraicGeometry.ProEtale.SpTowerClasses.scalarRoot_abelianTranspose_component`.

## No longer needed

None. The existing public imports and all DAG dependencies remain needed by the
component statement or the parent theorem.

## Where the brief, the DAG or earlier work was wrong

The brief and DAG proof route are mathematically consistent. The prior route
stated the whole tower equality directly; the Lean proof naturally factors it
through its finite-level pointwise component, so the missing work is recorded as
that new strictly smaller node.

## New nodes

- `lem-sp-tower-scalar-root-abelian-transpose-component`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TowerScalarRootAbelianTranspose": "30f00c53e994c9d4c38d5918f28f744215c6a8cf", "Sheaf.Paper.TowerScalarRootAbelianTransposeComponent": "8e9429394eda660f49cbdd388d871e12a12ac2db"}, "results": {}, "time": "2026-10-28T03:25:49+0800", "transitive": 0, "version": 1}
```

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
