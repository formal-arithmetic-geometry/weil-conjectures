## What changed

Proved the unchanged `exists_uniform_lowerTail_bound_of_isProper` from the declared heart
bound, bounded-heart dévissage, and the actual module-object Postnikov–Roos triangle.
The homology-property argument includes a small-support argument for existing coproducts
whose index universe is larger than the heart closure's specified coproduct universe.

Added `Sheaf.Paper.PadicAlgClConstructibleScalarRestriction` for the admissibility predicate's
finite-subextension-valued algebraic-closure case. Its theorem restricts constructible
modules to a finite coefficient field's weak Serre coproduct class. The proof uses finite
coefficient descent, a scalar-basis coproduct, and finite qcqs open-closed reconstruction.
Faithful exact restriction and its derived pushforward comparison then transfer the existing
finite-field heart bound. No existing signature, definition, or public import changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.exists_uniform_lowerTail_bound_of_isProper`.

Added no holes. The new theorem
`AlgebraicGeometry.ProEtale.constantModelConstructible_padicAlgCl_comap` and every private
helper are proved. There are zero retained `sorry`s in the delivery's Lean modules.
The existing heart-bound and lattice-tree declarations are used as supplied dependencies;
this delivery does not claim to close their holes.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit` and
the corresponding `lem-kun-grothendieck-derived-coproducts` dependency/tool approval: the proof
uses the source library homology-preservation instance for existing coproducts directly.
No existing module is withdrawn. The proof follows the heart-to-tail plan and retains its
mathematical dependencies. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

`IsLocalizingAdmissibleCoefficient` includes seven alternatives. The existing qcqs proper
Serre-heart bound lists six norm-topological alternatives and does not cover the separate
finite-subextension-valued `padicAlgClRingObj` alternative. The proof handles that case by
restriction to a finite coefficient field; it never identifies that ring with the ring of all
continuous algebraic-closure-valued functions.

The hull's coproduct universe is larger than the universe explicitly used to generate the
heart class. Closure for all existing coproducts follows by dropping zero summands: distinct
nonzero summands give distinct orthogonal idempotents of the coproduct vertex, so their
index subtype is small in the morphism universe. Reindexing this subtype makes the stated
small-coproduct closure applicable.

## New nodes

`lem-sfb-padic-alg-cl-constructible-scalar-restriction` records the proved scalar-restriction
lemma. It is independent of properness and only asserts membership in a generated heart
class. Its module contains the finite-field, lisse, and open-closed reconstruction helpers.
The item node's proof and dependency list record this coefficient case and the coproduct
universe argument. No definition or statement repair, change record, or forced adaptation
is needed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
