## What changed

Proved `Module.finite_flat_restriction_projective` in
`Sheaf.Algebra.FiniteFlatRestrictionProjective` by the existing node's three-step route.
First use `Module.FinitePresentation.of_finite_of_finitePresentation` for the algebra,
then `Module.FinitePresentation.trans` for the module. Projectivity over the larger
ring supplies flatness by Mathlib's instance; `Module.Flat.trans` descends flatness,
and `Module.Flat.projective_of_finitePresentation` supplies projectivity over the
smaller ring.

Added three proof-only imports: `Mathlib.RingTheory.Finiteness.ModuleFinitePresentation`,
`Mathlib.RingTheory.Flat.Stability`, and `Mathlib.RingTheory.Flat.EquationalCriterion`.
Existing signatures, public imports, definitions, and the node's route are unchanged.
No new nodes or change records are needed.

The remote single-file compiler accepted the proof without warnings.
A separate compiler check of `#print axioms Module.finite_flat_restriction_projective`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
The diagnostic command was removed from the delivery.

## Proved and sorry left

Closed one hole: `Module.finite_flat_restriction_projective`
(node `lem-pc-finite-flat-restriction-projective`).
Proved 1 of 1 original sorries; added 0 holes; split off 0 statements.
No sorry remains in the delivered module.

## No longer needed

None. No imports were removed and no nodes or modules were pruned.
The proof uses all the mathematical lemmas named by the existing three-step plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. All the required dependencies are already proved
in Mathlib, so no intermediate Sheaf modules are needed. The module needed the
three proof-only imports listed above to expose the lemmas in its docstring.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
