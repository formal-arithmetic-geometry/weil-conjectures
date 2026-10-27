## What changed

Replaced the single proof hole in
`AlgebraicGeometry.ProEtaleWeilSheaf.weil_geometric_hom_constructibility`.
The argument compares cohomology using the composite faithful exact abelian functor,
uses the native module comparison and the sectionwise equivalence unit for
constructibility, and preserves and reflects every prescribed support interval.
The coefficient-heart equality gives finite Tor amplitude; the adic predicate comparison
and the existing source internal-Hom closure theorem give constructibility of geometric
relative derived Hom. The theorem signature and `nativeGeometricForget` are unchanged.
Added a private proof import of
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback` for isomorphism transport.
The added import was checked cycle-free with `tools/import_direction.py may`.

The node proof and proof dependencies now describe this assembly and point directly to
`lem-sfb-dc-hom-small-coefficients` for the algebraic-closure coefficient case.

Validation: `lcompile.py` compiled the final module cleanly in 16.9 seconds,
without warnings. The existing theorem signature was checked byte-for-byte unchanged,
and all Lean lines are at most 100 characters.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtaleWeilSheaf.weil_geometric_hom_constructibility`
(`lem-sf-weil-geometric-hom-constructibility`), one existing hole.
Added: none. Remaining holes in the item: none. Split off: none.
The proof uses existing declared results with their own proof obligations; it does not
claim to close their transitive holes.

## No longer needed

Removed the unused private import
`Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`. Its discrete-coefficient
site-model presentation is not used by this condensed-coefficient proof. The general
bounded-constructibility predicate remains available through its defining source module.

The proof does not invoke `native_closed_forgetful` or its closed monoidal comparison
and representative-normalization clauses. The module
`Sheaf.Paper.NativeWeilClosedForgetful` stays because it defines `nativeForget`, which
occurs in the unchanged public abbreviation. Thus that module is not withdrawn.

The absent wrapper `Sheaf.Paper.BoundedConstructibleHomFiniteness`, recorded under
`lem-sfb-dc-hom-preserves`, is not needed. The existing
`isMonoidalClosed_boundedConstructible`, recorded under
`lem-sfb-dc-hom-small-coefficients`, supplies exactly its algebraic-closure case. The
obsolete `lem-sfb-dc-hom-preserves` tool approval is removed from the node; remaining
approvals retain their order. No source declaration or module is withdrawn.

The construction, coefficient-heart, finite-type base-change, Noetherianity and adic
predicate-comparison dependencies remain needed. No new mathematical theory is added.

## Where the brief, the DAG or earlier work was wrong

The rework table names a quarantine path, but the assigned module is present in the
current library and that quarantine path is absent. The delivery starts from the live
module, preserving its attachment and statement.

The planned Hom-finiteness dependency records a wrapper that is absent from the current
library. Its own node note identifies the source class-indexed theorem as providing the
algebraic-closure case. The proof uses that existing theorem directly and updates the
DAG edge accordingly.

The stronger `native_closed_forgetful` theorem is marked statement-disputed because of
an unrelated representative normalization. This proof needs only the underlying
forgetful functor and the already proved generic exact-functor homology interface,
so it does not apply that disputed theorem.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
