## What changed

Proved `CategoryTheory.Functor.exists_unique_exactInputDerivedTransformation` in
`Sheaf.CategoryTheory.ExactInputDerivedTransformation`, retaining its statement and public
interface. Added proved private helpers for shift descent, the universal comparison, its
unit equation on complexes, and its two-resolution computation. No imports changed.
Validation: the complete proof compiled on the project server in 12.8 seconds.
The final delivery checks recompile the file and check its declarations and axioms.
The canonical shift structures are descended along the K-injective localization, using
the inverse restricted computation units as lifting isomorphisms. The comparison is obtained
from the existing universal bijection. Updated the node proof to record the actual route.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Functor.exists_unique_exactInputDerivedTransformation`
(`lem-sfb-exact-input-derived-transformation`). No holes added; no `sorry` remains in the
item module. Every private helper is proved. No statements were split off.

## No longer needed

No imports or modules were removed. The direct proof no longer needs the separate
`lem-weil-pbc-kinjective-hom-derived` and `lem-weil-pbc-kinjective-shift` steps for explicit
changes of resolutions and shifted resolutions. Their infrastructure remains available
through the K-injective replacement theorem; this is not a claim of global withdrawal.
Every pair of resolutions already computes the single universally characterized map.
Shift compatibility follows instead from cancellation of the restricted invertible unit
and essential surjectivity. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan's explicit changes of both resolutions and
its calculation with shifted resolutions are unnecessary. The unit equation and universal
bijection give independence, while restriction to K-injectives proves shift compatibility.
The associators must be retained explicitly: their underlying functors are definitionally
associated but their composite shift structures need not be definitionally identical.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
