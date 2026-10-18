## What changed

Proved `AlgebraicGeometry.Scheme.adicScalar_exists` in
`Sheaf.Paper.AdicGlobalDerivedHom`, with every existing signature and definition unchanged.
A proved private helper `adicFiniteConstant_compat` checks consecutive quotient compatibility:
sheafification naturality reduces it to postcomposition of a constant residue function.
`NatTrans.ofOpSequence` extends that compatibility to the entire inverse system.
Sheaf inclusion followed by section evaluation preserves the limit; its universal property
constructs the scalar ring homomorphism and proves uniqueness by all projections.
This is the argument already documented at the declaration, including empty objects and zero rings.

The module compiles through `lcompile.py` in approximately five seconds without warnings.
All existing imports are needed by the statements or definitions; no imports were added.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.adicScalar_exists`
(node `def-weil-pbc-adic-global-derived-hom`).
The private compatibility helper is also fully proved.
No holes remain in the item module. No holes were added, and none were split off.

## No longer needed

None. The proof follows the declaration's existing limit argument.
The node has no listed proof dependencies to prune, and all three public imports remain
necessary for the module's definitions. No constant/completed coefficient comparison,
finite coefficient comparison theorem, or extra module is imported or used in the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect was found. The definition node has an empty `proof`
field, but the theorem's existing docstring gives the complete argument; this delivery
implements it directly from Mathlib and the existing coefficient definitions.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
