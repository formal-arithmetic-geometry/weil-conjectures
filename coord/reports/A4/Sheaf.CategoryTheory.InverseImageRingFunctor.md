## What changed

Proved `CategoryTheory.inverseImage_ring_functor` by the planned route through
`sheaves_algebraicStructures_objects` and `Adjunction.liftsGroupRingObjects`.
The ring functors and adjunction are transported through the strict sheaf/ring-object
identifications. Proved private lemmas handle equality transports for binary operations,
constants, and adjunction hom-equivalences. No statement or definition changed. Replaced redundant public project imports
with the three Mathlib statement imports and made the two proof-tool imports private.
Change record: `coord/changes/inverse-image-ring-functor-proof-imports.md`.
Updated the item node's proof and proof origin to describe the actual Lean argument.

Validation: `lcompile.py --all` compiled the item in 20.9 seconds and its sole direct
consumer, `Sheaf.CategoryTheory.GeometricRingInverseImage`, in 7.5 seconds, without
warnings and under the default heartbeat limit. The unchanged consumer copy was
removed from the packet after checking. A text comparison verifies that the four
original operation definitions and the theorem signature are byte-identical.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.inverseImage_ring_functor`
(`lem-route-inverse-image-ring-functor`). Added zero holes. No `sorry` remains in the
item, and there are no split-off statements.

## No longer needed

Both declared proof dependencies remain necessary. No node or module is withdrawn;
the unit route is retained.
Removed unused imports `Sheaf.CategoryTheory.SiteCoveringAxioms` and
`Sheaf.CategoryTheory.RingedSiteModules`; their definition nodes remain statement
references, and their modules are still needed elsewhere in the library.
`WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects` and
`Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects` remain necessary proof
imports, with public exposure removed. No entire library module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The two stated generic tools fit the argument.
Their strict inverse and forgetful identities require explicit equality transports;
these are proved in the item rather than left as an additional obligation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.InverseImageRingFunctor": "2f638cec9eb4c5839700e8dcb614e7789c3cfb32"}, "results": {"Sheaf.CategoryTheory.GeometricRingInverseImage": {"hash": "013e1e92d2b68770a032ab049171c2941150d63e", "status": "OK"}}, "seconds": 11, "time": "2026-10-28T09:28:04+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
