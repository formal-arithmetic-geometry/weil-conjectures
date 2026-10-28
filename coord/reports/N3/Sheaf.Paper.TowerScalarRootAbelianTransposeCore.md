## What changed

Proved `scalarRoot_abelianTranspose_core` in
`Sheaf.Paper.TowerScalarRootAbelianTransposeCore`, preserving both public helper
definitions and the theorem statement. Four proved private lemmas identify the
Kummer roots transpose, evaluate the scalar unit, and identify each side with the
same finite Tate tensor under inverse `lineEvaluation`.

Added proof-only `import all` imports of
`TowerIntegralCoefficientPullbackExistence`, `TowerRestrictedScalarAdjunction`,
`TowerLineTransitionTensor`, `TowerLinePullbackLowerTensor`, and
`ScalarExtensionSectionNaturality` to use their existing private proved helpers.
Local transparency attributes keep the sheaf constructions from unfolding during
elaboration. Updated the item's proof steps and proof dependencies in its DAG node.
The module compiled without warnings in 18.5 seconds through `lcompile.py`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.scalarRoot_abelianTranspose_core`
(node `lem-sp-tower-scalar-root-abelian-transpose-component-core`).
No `sorry` remains in the item. Added zero holes and no split-off statements.
The private lemmas `rootTranspose`, `scalarUnitSection`, `sourceSection`, and
`rightSection` all have complete proofs.

## No longer needed

None. No original imports, nodes, modules, or declarations were removed. Every
added import supplies a helper used in the proof. The imported modules' larger
existence and transition theorems are not invoked: the calculation uses their
proved local normalization and section-transport helpers.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original planned calculation closes from the
existing helpers and normalization fields, without another decomposition.
The updated DAG expands the original single proof step into the actual root,
scalar-unit, geometric-source, and abelian-transpose calculations.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.TowerScalarRootAbelianTransposeCore": "1a26d2b46f638b68c8f1bbd8c0c691afbd1eb68c"}, "results": {"Sheaf.Paper.TowerScalarRootAbelianTransposeComponent": {"hash": "0332fa4934e6d0e2c2b5d90bddd1eee9f710ace3", "status": "OK"}}, "seconds": 95, "time": "2026-10-28T10:25:06+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
