## What changed

The assigned theorem in `Sheaf.Paper.ExtendedCechCompleteUnitCriterion` is now proved by
combining two directional theorems. The complete-to-unit direction and the unit-to-complete
direction are stated in separate modules, each with its own DAG node and source-backed proof
plan. The assigned module imports those modules proof-only and applies both implications.

The directional proofs are intentionally split because the parent reflector module imports the
assigned criterion; importing that parent here would create an import cycle. The split modules
retain the local finite-generator, internal-Hom, localization, complete-elements, and model
interfaces needed by the eventual proofs.

## Proved and sorry left

Closed 1 original sorry:

- `CategoryTheory.ringedExtendedCech_complete_iff_unit_isIso`.

Added 2 strictly simpler directional obligations, both public named theorems with DAG nodes:

- `CategoryTheory.ringedExtendedCech_complete_implies_unit_isIso` in
  `Sheaf.Paper.ExtendedCechCompleteImpliesUnitIso`;
- `CategoryTheory.ringedExtendedCech_unit_isIso_implies_complete` in
  `Sheaf.Paper.ExtendedCechUnitIsoImpliesComplete`.

The two added sorries are the complete-to-unit and unit-to-complete halves of the original
criterion; neither restates the equivalence or repackages the original conclusion.

## No longer needed

No imports were removed from the assigned module. Its three public imports remain necessary for
the theorem signature. The original six proof dependencies are no longer direct dependencies of
the assigned theorem's proof: they are recorded on the two split directional nodes, where the
future proofs will use the corresponding local arguments.

## Where the brief, the DAG or earlier work was wrong

The original proof plan placed the entire finite-filtration and localization argument in one
large theorem, while its parent `ExtendedCechReflectorCore` already imports this criterion. A
proof route through that parent is therefore cyclic. Splitting the two implications gives a
non-cyclic reduction into strictly simpler obligations and leaves the statement unchanged.

## New nodes

- `lem-weil-pbc-extended-cech-complete-implies-unit-isIso`: the complete-object implication;
  node file `dag/nodes/sec-proper-base-change/lem-weil-pbc-extended-cech-complete-implies-unit-isIso.json`.
- `lem-weil-pbc-extended-cech-unit-isIso-implies-complete`: the invertible-unit implication;
  node file `dag/nodes/sec-proper-base-change/lem-weil-pbc-extended-cech-unit-isIso-implies-complete.json`.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
