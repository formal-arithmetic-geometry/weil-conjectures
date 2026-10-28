## What changed

Replaced the target theorem's proof imports with two local intermediate modules.  The target
now obtains pointwise pro-etale derived Isom sections from the finite-level comparison data
and converts them to etale local representatives.  The two intermediate declarations are
`lisse_finite_level_proetale_local_iso_sections` and
`exists_etale_local_representative_of_proetale_local_iso_sections`; each is a strictly smaller
step and remains explicitly named for the next proving stage.  The original target statement
is unchanged and compiles.

## Proved and sorry left

The target declaration
`AlgebraicGeometry.Scheme.lisse_finite_level_etale_local_isomorphisms` is proved by a real
Lean composition of the two intermediate statements.  The delivery adds exactly two named
split-off sorries:

- `AlgebraicGeometry.Scheme.lisse_finite_level_proetale_local_iso_sections` in node
  `new-lem-weil-pbc-lisse-finite-level-proetale-local-iso-sections`;
- `AlgebraicGeometry.Scheme.exists_etale_local_representative_of_proetale_local_iso_sections`
  in node `new-lem-weil-pbc-lisse-finite-level-etale-local-representative`.

## No longer needed

The target module no longer imports the former proof-only modules
`Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse`,
`Sheaf.AlgebraicGeometry.DerivedIsomSheafComparisonFromHom`,
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`,
`Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`,
`Sheaf.Paper.ProEtaleLisseOrigin`, and
`Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection` directly.  The finite comparison
nodes remain the declared proof dependencies of the first split-off theorem, so no existing
DAG node is pruned by this decomposition.

## Where the brief, the DAG or earlier work was wrong

The original one-step DAG proof plan bundled finite comparison, pro-etale section construction,
sheafification, and pointed etale representative extraction into one theorem.  The target
module can compile cleanly only after these are exposed as the two strictly simpler statements
added here; the target's mathematical statement and its unit route are unchanged.

## New nodes

`new-lem-weil-pbc-lisse-finite-level-proetale-local-iso-sections` records the pointwise
pro-etale section construction and its finite comparison dependencies.

`new-lem-weil-pbc-lisse-finite-level-etale-local-representative` records the generic
sheafification and point-fibre representative step.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteLevelEtaleLocalIsomorphisms": "f8674c4dc52da453ee46e36207bde58015c17f03", "Sheaf.Paper.LisseFiniteLevelEtaleLocalRepresentative": "3fd3aaa968e79e682cc497a228b7711ee2a61135", "Sheaf.Paper.LisseFiniteLevelProEtaleLocalIsoSections": "4e858acb1957f11713b4a6ab8423d89f024e5a8a"}, "results": {"Sheaf.Paper.LisseFiniteLevelEtaleStalks": {"hash": "864c2ea5791b6693cd7bcb06801b8d0439b50b12", "status": "OK"}}, "seconds": 16, "time": "2026-10-28T08:04:04+0800", "transitive": 0, "version": 1}
```

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
