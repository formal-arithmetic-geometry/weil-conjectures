## What changed

Proved `AlgebraicGeometry.Scheme.Hom.isClosed_singleton_asFiber_of_finiteDimensional`
in `Sheaf.TraceFormula.FiniteResiduePointClosedInFibre`, with its signature unchanged.
The canonical map `Spec κ(x) → Xₛ` has locally finite type composite to `Spec κ(s)`
because the given residue extension is finite-dimensional. Cancellation gives local
finite type of the canonical map. Since `Xₛ` is Jacobson, Mathlib makes this map finite;
its closed image is precisely the requested singleton.

Replaced the two Sheaf proof imports with the private proof import
`Mathlib.AlgebraicGeometry.Morphisms.Finite`. All existing public imports remain.
Updated the theorem docstring and its DAG node's proof, proof dependencies and origin
to describe this route. Removed the two obsolete top-level tool approvals.
The unit statement and steps are preserved; no declaration or definition changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Hom.isClosed_singleton_asFiber_of_finiteDimensional`
(node `lem-trf-finite-residue-point-closed-in-fibre`).

Added 0 holes; split off 0 statements; no `sorry` remains in the delivered module.
The proof uses only Mathlib, with no assumed project theorem.
The single-file remote compilation passed in 3.8 seconds without diagnostics.
The delivery preflight also checks declaration axioms.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.FibreStalkQuotient`;
- `Sheaf.AlgebraicGeometry.ClosedPointField`.

Removed dependencies of this node:
- `lem-weil-pbc-lft-affine-pairs`: no affine neighbourhood or coordinate algebra is needed;
- `lem-sbc-scheme-fibre-stalk-quotient`: use `asFiberHom` directly, avoiding any identification
  of the fibre stalk or residue field;
- `lem-kun-closed-point-field`: the finite-morphism criterion over a Jacobson scheme
  gives the closed image directly, without a quasi-compact affine restriction.

Removed top-level `tool_uses` entries `lem-kun-closed-point-field` and
`lem-sbc-scheme-fibre-stalk-quotient` for the same reasons. These nodes and their
modules are unnecessary for this proof; no claim is made that all other consumers
can dispense with them. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier search correctly found the Jacobson criterion but did not exploit
`asFiberHom`. There is no need to identify the fibre point's own residue field:
Mathlib already knows the canonical map's composite and its singleton image.
The original affine-local proof plan was valid but longer than necessary.
The final proof is a direct Mathlib argument; it does not bypass a blueprint unit.
Edge cases cause no extra hypotheses: non-quasi-compact X is allowed because the
Jacobson criterion only needs local finite type; empty X has no point x, so that
case is vacuous. No separability of the finite residue extension is used.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
