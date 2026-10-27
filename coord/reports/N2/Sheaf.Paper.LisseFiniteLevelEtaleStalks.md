## What changed

The assigned theorem `AlgebraicGeometry.Scheme.lisse_finite_level_etale_stalks` is now
proved by composing two strict lower obligations.  The new module
`Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms` isolates construction of a pointed
étale neighbourhood carrying an actual derived local isomorphism.  The new module
`Sheaf.Paper.LisseFiniteLevelEtaleStalkFromLocal` isolates passage from that local
representative through sheafification and the point-fibre colimit.  The item module
imports these two proof modules and constructs the final stalk conclusion by applying
them.  Its public statement and the `LisseTowerEtaleDescentData` public import are
unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.lisse_finite_level_etale_stalks` (1 of 1).

Two strictly simpler lower statements remain as named theorem holes:

- `AlgebraicGeometry.Scheme.lisse_finite_level_etale_local_isomorphisms`, node
  `lem-weil-pbc-lisse-finite-level-etale-local-isomorphisms`;
- `AlgebraicGeometry.Scheme.lisse_finite_level_etale_stalk_from_local_section`, node
  `lem-weil-pbc-lisse-finite-level-etale-stalk-from-local-section`.

No definition contains a `sorry`.  The delivery adds 2 split-off holes.

## No longer needed

The item module no longer directly imports the proof-only modules
`Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`,
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`,
`Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse`,
`Sheaf.AlgebraicGeometry.DerivedIsomSheafComparisonFromHom`,
`Sheaf.Paper.ProEtaleLisseOrigin`, or
`Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection`.  Those modules remain imported
by the local-comparison helper, where the finite-lisse comparison argument uses them.
The item itself directly needs only `Sheaf.Paper.LisseTowerEtaleDescentData` for its
statement and the two new proof modules.

The original three proof-dependency nodes are therefore no longer direct dependencies
of the item node; they remain dependencies of
`lem-weil-pbc-lisse-finite-level-etale-local-isomorphisms`.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan combined two distinct constructions: an actual local
étale representative of the Isom presheaf and evaluation of that representative in a
geometric stalk.  The available comparison and equalizer declarations address the
first construction, while the point-fibre sheafification API addresses the second.
The DAG did not expose either interface in Lean.  The delivery records both as strict
parts of the argument and proves their composition in the assigned module; no target
statement or unit route was changed.

## New nodes

`lem-weil-pbc-lisse-finite-level-etale-local-isomorphisms` records the local comparison
and representative construction.  Its Lean declaration is in
`lean/Sheaf/Paper/LisseFiniteLevelEtaleLocalIsomorphisms.lean`.

`lem-weil-pbc-lisse-finite-level-etale-stalk-from-local-section` records evaluation of a
pointed local representative in the sheafified Isom stalk.  Its Lean declaration is in
`lean/Sheaf/Paper/LisseFiniteLevelEtaleStalkFromLocal.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms": "2df731f57bc8540a6a46354101d3f724ca895cd7", "Sheaf.Paper.LisseFiniteLevelEtaleStalkFromLocal": "4ef0048af014fededc0123d59a42f9b9f91aadee", "Sheaf.Paper.LisseFiniteLevelEtaleStalks": "864c2ea5791b6693cd7bcb06801b8d0439b50b12"}, "results": {"Sheaf.Paper.LisseFiniteLevelEtaleDescent": {"hash": "bdcdcb3186f0e12e37a1aae23babc13c1f097fcf", "status": "OK"}}, "seconds": 12, "time": "2026-10-28T06:32:14+0800", "transitive": 0, "version": 1}
```

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
