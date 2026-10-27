## What changed

Proved `AlgebraicGeometry.Scheme.sfCartesianOpenAdjunctionRestriction` in
`Sheaf.SixFunctors.CartesianOpenAdjunctionRestriction`, with all existing declaration
signatures and both definition bodies unchanged. The proof identifies the conjugate Hom
comparison with the mate of the specified derived pullback square, identifies geometric
restriction with that same mate, and applies Mathlib's unit and counit mate identities.

Added only fully proved private helpers for coefficient transport, right-adjoint coordinate
changes, exact localization, and these two identifications. Proof imports use existing
private proved APIs via `import all`; no dependency statement is assumed anew. Updated the
item node's proof, proof dependencies and origin to match this route. No unit realization
is bypassed (the containing unit has no realized statement or proof steps).

The final module compiles without warnings via `lcompile.py` (16.4 seconds). Every Lean
line is at most 100 characters. The theorem works for the existing arbitrary morphism,
open immersion and finite commutative coefficient ring, including empty opens, identity
maps and the zero ring: the proof uses categorical identities without nonemptiness,
properness, boundedness or nonzero assumptions.

Public-import pruning is documented in
`coord/changes/cartesian-open-adjunction-import-pruning.md`. The sole downstream module,
`Sheaf.Paper.IsomorphismFiniteMateNormalization`, explicitly imports the removed module
and needs no adaptation. No source-library module is changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.sfCartesianOpenAdjunctionRestriction`
(node `lem-sf-cartesian-open-adjunction-restriction`).

There are zero `sorry`s left in the item, zero added elsewhere, and zero split-off
statements. All seven new private helper theorems are proved. This is a proof, not a
hole decomposition. No definitions, axioms or arbitrary existence witnesses are added.

## No longer needed

Removed the direct imports:

- `Sheaf.SixFunctors.OpenTensorNormalization` (public): the published concrete open mate
  already has the required normalized mate identity; the generic tensor/existence theorem
  is not used. Its node `lem-sf-open-tensor-normalization` is removed from this proof's
  dependencies and obsolete `tool_uses`, while its statement dependency remains unchanged.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (private), node
  `def-weil-proetale-inverse-image`: reuse the proved ordinary base-change/mate calculation
  instead of redoing the inverse-image-colimit calculation.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral` (private), node
  `lem-pc-pre-derived-adjoint-functors-general`: reuse the proved derived-square/mate
  compatibility instead of redoing the representative-level derived adjunction argument.

The latter two nodes are also removed from this item's obsolete `tool_uses`. These are
pruned direct proof dependencies only: no claim is made that the modules have become
unused elsewhere or through other imported modules, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned sectionwise and K-injective calculations
already exist in the library, including their compatibility with the specified coefficient
coordinates and exact localizations. Reusing those proofs is shorter and preserves the
same normalization. The existing theorem docstring remains as the mathematical argument;
the updated DAG describes the formal proof's reuse of those calculations.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
