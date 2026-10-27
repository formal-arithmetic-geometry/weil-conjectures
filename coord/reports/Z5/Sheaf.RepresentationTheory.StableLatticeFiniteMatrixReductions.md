## What changed

Proved `Padic.exists_stable_lattice_finite_matrix_reductions` in
`Sheaf.RepresentationTheory.StableLatticeFiniteMatrixReductions`, preserving its signature.
The proof applies the existing stable-lattice theorem, extends the integral basis by
Mathlib's `Module.Basis.extendOfIsLattice`, and maps the restricted automorphisms through
`LinearMap.toMatrixAlgEquiv` and `Units.map`. The basis expansion gives the stated action
formula. The recorded uniformizer ideal generates the recorded maximal ideal, so the
stable-lattice theorem supplies both topology clauses directly.

A proved private helper `Padic.continuous_adic_coordinate` shows that any linear coordinate
modulo an ideal power is continuous from the adic module topology to the discrete quotient:
its kernel contains the open module power. Composing with continuous orbit maps makes all
reduced matrix entries continuous. A matrix fiber is a finite intersection of entry fibers;
a range-restricted fiber is the same original fiber. This proves both continuity claims,
including rank zero, and range restriction is surjective by Mathlib. Coefficient-ring
finiteness is the existing `Padic.finite_coefficientExtensionRing`; finite matrices and
units give finiteness of the image.

Added proof-only imports of `Mathlib.Algebra.Module.Lattice` and
`Mathlib.Topology.Algebra.OpenSubgroup`. Updated the existing node's proof, proof dependencies
and proof origin to match the Lean argument. No public interface, definition, source-library
module, target, unit statement or unit route changes.

Searches used the launcher LeanFinder, Loogle and Mathlib grep services and local `rg` in
Mathlib, `lean/Sheaf` and `lean/WeilConjectures`. LeanFinder found the exact basis-extension
API; Loogle found no match for `"IsFractionRing", "linearIndependent"`. The local source
already demonstrates related coordinate and adic-topology arguments in the private helpers
of `CommonIrreducibilityDetectingCover`; it has no public theorem replacing this item.
Validation: the complete module compiled cleanly through `lcompile.py` (8.1 seconds),
with no warnings or remaining holes. A source comparison confirms that the existing
theorem signature is byte-for-byte unchanged; all Lean lines are at most 100 characters.
Read Stanford seminar L19, Proposition 1.1.9, printed page 3, and the current blueprint's
six-functor stability/direct-image route.

## Proved and sorry left

Closed 1 hole: `Padic.exists_stable_lattice_finite_matrix_reductions`
(`lem-sfb-stable-lattice-finite-matrix-reductions`). Added 0 holes, split off 0 statements.
No `sorry` remains in the delivered module. The private coordinate-continuity helper is
also completely proved. This is a proof from existing declared dependencies; their internal
remaining holes are unchanged and are not counted as closed here.

## No longer needed

The separate topology-comparison steps using `lem-weil-l-adic-extension-complete` and
`lem-weil-pbc-finite-dimensional-linear-homeomorphism` are unnecessary here: the topology in
`Padic.exists_stable_lattice` is definitionally the same module topology as this theorem's.
Removed those two direct proof dependencies from this node. They can still be needed by
the stable-lattice theorem or other consumers.

The direct use of `lem-weil-valued-dvr-finite-quotients` is unnecessary:
`Padic.finite_coefficientExtensionRing`, recorded at
`def-weil-l-adic-coefficient-extension`, already proves the exact coefficient-ring
finiteness claim. Removed that direct proof dependency. No replacement finite-quotient
node or module is introduced.

Removed the unused proof import `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
All existing public imports are preserved. Retained the existing stable-lattice proof
import, which is essential. No existing library module is withdrawn or claimed globally
unreachable.

## Where the brief, the DAG or earlier work was wrong

The DAG's initial topology comparison is redundant for the existing Lean signatures.
Its common-denominator basis argument is already implemented by Mathlib's lattice basis
extension. Its finite-quotient step is already available in the coefficient extension API.
The open-fiber argument is implemented via open kernels of coordinate quotient maps,
which avoids choosing lifts of every matrix entry. These are shorter implementations
of the same argument; all hypotheses, conclusions and the rank-zero case are preserved.
No disputed statement, definition repair, forced adaptation, or tool workaround was needed.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
