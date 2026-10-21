## What changed

Proved `DerivedCategory.Plus.isIso_app_truncLE_of_isIso_app_homology` with its
statement unchanged, by finite Postnikov induction in the induced t-structure on
`DerivedCategory.Plus A`.

Added the private proof import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`, whose proved
`nonempty_eTruncGE_eTruncLT_iso_singleFunctor` identifies the successive piece.
The proof establishes invertibility on all integer shifts directly from the
degree-one equation, transports along isomorphisms, and explicitly constructs the
morphism of distinguished triangles before applying Mathlib two-out-of-three.
The base case uses the zero truncation and covers `b = a - 1`.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
No statement, definition, public import or other module changed. The unit's
finite Postnikov route is preserved.

## Proved and sorry left

Closed one hole:
`DerivedCategory.Plus.isIso_app_truncLE_of_isIso_app_homology`
(node `lem-weil-pbc-finite-postnikov-isomorphism`).

Proved 1 of 1 original sorries; zero sorries remain; zero holes added or split off.
The earlier attempt compiled the complete module on the server in approximately
2.5 seconds. The resumed session rechecked the unchanged signature, finite
induction, shift argument, unit route, and DAG dependency union against current
sources; current server validation is retried below.

## No longer needed

Removed proof imports:

- `WeilConjectures.CategoryTheory.TruncationTriangle`: the induced t-structure
  supplies the distinguished triangle directly; concrete cochain representatives
  and their comparison maps are unnecessary.
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`: the concrete truncation
  cohomology API is unnecessary for this proof.
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`: constructing the
  triangle morphism explicitly and using Mathlib's component two-out-of-three
  avoids requiring a coherent `NatTrans.CommShift` instance for all integers.

Removed the following planned proof dependencies from this node:

- `lem-weil-pbc-truncation-triangle`, by the first replacement above.
- `lem-weil-pbc-truncation-cohomology`, replaced by the existing proved derived
  truncation-piece isomorphism and nested-truncation comparison.
- `lem-weil-pbc-derived-plus-iso-on-cohomology`, replaced by the t-structure's
  `isZero_truncLE_obj_of_isGE` for the base case.
- `lem-sf-triangle-two-out-of-three`, replaced by direct use of Mathlib's
  `Pretriangulated.isIso₂_of_isIso₁₃` on the explicit triangle morphism.

Removed the obsolete top-level `tool_uses` approval for
`lem-sf-triangle-two-out-of-three`.

These nodes and source modules are unnecessary for this item's proof; no claim
is made that other consumers cease to need them. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The planned concrete truncation
triangle and cohomology detection detour are unnecessary because the adopted
source library already proves the cohomology-piece identification inside D+.
The natural-transformation two-out-of-three API asks for compatibility with all
integer shifts; its underlying Mathlib theorem applies directly after checking
the triangle's single degree-one square. No new lemmas or change records.

Earlier tooling failure: after the successful proof compiles, the delivery probe and an
ordinary lcompile call both failed at the first Mathlib import with
`unknown module prefix 'Mathlib'`. Their search paths listed only the project
build and Lean core, omitting the package build paths. Subsequent required
wait-and-retry attempts received busy-server responses and pushed nothing.
The completed proof and DAG updates are preserved in this sandbox; no launcher
script was edited or bypassed.

Resumed validation: the required initial delivery attempt returned
`no answer from the compile server within 196 s (server busy or unreachable)`.
Nothing was pushed; the worker retained the packet and waited before retrying.
Refreshed inherited DAG metadata from current sources without changing it; the
only node changes are the proof, proof dependencies, proof origin and removal of
the obsolete tool-use approval described above.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
