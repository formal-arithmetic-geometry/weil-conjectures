## What changed

Proved `Algebra.exists_smooth_localization_of_separable_fractionRing` in
`Sheaf.RingTheory.GenericSmoothDomain`, with its signature, universes and all four
public imports unchanged. The proof uses generic finite presentation and Mathlib's
formal smoothness and smooth-locus API instead of constructing the generic fibre.

The four proved private helpers supply generic finite presentation in different
universes, formal smoothness of an essentially finite type separable field extension,
formal smoothness of the target fraction field over the original domain, and descent
of a smooth principal neighbourhood through a principal localization. No public
interface or definition changed. `import all` accesses the existing proved private
affine helper of `Sheaf.AlgebraicGeometry.GenericLocallyOfFinitePresentation`, as that
module itself does for its generic-flatness input; no theorem is restated with a hole.

Updated `lem-exc-generic-smooth-domain`'s proof, dependencies, proof origin, and obsolete
tool approvals to match the Lean proof. The blueprint unit has no realization by this
node: this changes only the route below the unit.

Validation: the complete proof compiled through `lcompile.py` (about five seconds).
The final delivery gate checks the formatted file again. The original theorem
statement is identical, including the specific induced fraction-field algebra.

## Proved and sorry left

Closed one original hole:
`Algebra.exists_smooth_localization_of_separable_fractionRing`
(node `lem-exc-generic-smooth-domain`).

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining: 0.
Every private helper is proved. No new modules, nodes, definitions or assumptions.

## No longer needed

Removed these proof imports:

- `Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime`: Mathlib formal smoothness
  composes through the fraction field without a flat-fibre criterion.
- `Sheaf.RingTheory.SmoothAtGenericPointOverField`: formal smoothness follows directly
  from the separable transcendence basis and Mathlib's field theorem.
- `WeilConjectures.RingTheory.SingularIdeal`: the conclusion is constructed directly;
  the project-specific existential definition of smoothness at a prime is unnecessary.

Kept `Sheaf.AlgebraicGeometry.GenericLocallyOfFinitePresentation` as a proof dependency,
using its already proved affine finite-presentation helper. The new Mathlib imports
supply universe shrinking, finite-type smallness, field formal smoothness, the smooth
locus, finite generation of the top intermediate field, and iterated localization.

The following former proof dependencies are unnecessary for this proof:

- `def-weil-affine-spectrum`;
- `lem-weil-pbc-spec-domain-stalks-function-field`;
- `lem-weil-pbc-lft-pointwise-criterion`;
- `lem-weil-pbc-affine-scheme-qcqs`;
- `lem-weil-pbc-affine-open-section-vanishing-prime`;
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`;
- `lem-weil-pbc-finite-presentation-base-change-composition`;
- `lem-weil-pbc-generic-fibre-localization-domain-irreducible`;
- `lem-weil-pbc-smooth-at-generic-point-over-field`;
- `lem-weil-pbc-module-over-field-flat`;
- `lem-weil-pbc-flat-smooth-fibre-smooth-at-prime`;
- `def-weil-pbc-singular-ideal`.

The explicit spectrum, generic-fibre and flat-fibre constructions are replaced by the
proved affine finite-presentation helper and formal smoothness of the fraction field.
Definitions still used (finite type, finite presentation, separability, localization
at a prime, and smoothness) remain in the node's dependencies. Removed the two obsolete
top-level tool approvals for field-base generic-point smoothness and the flat smooth
fibre criterion; retained the generic finite-presentation approval. This is pruning
of this item's dependencies; other parents may still need these nodes and modules.

## Where the brief, the DAG or earlier work was wrong

The original statement is correct. The planned generic-fibre and flat-fibre route is
longer than necessary given Mathlib's formal smoothness API. Separability is applied
only after proving essential finite type of the fraction-field extension; it is not
silently treated as algebraic separability. The chosen finite-presentation element
is nonzero in the source, and injectivity gives a nonzero target element. A second
localization numerator is nonzero because its image is associated to the nonzero
smooth-neighbourhood element. Their product is nonzero even in the edge cases where
the source or target is already a field. Universe differences are handled by `Shrink`
and algebra equivalences, without changing the original universes.

The interrupted session's provisional auxiliary module and unmatched node were never
delivered and are absent from this delivery: the entire proof is completed in the
original module, with no split.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
