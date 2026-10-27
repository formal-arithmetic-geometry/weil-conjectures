## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_frobenius_power_deck_point` in
`Sheaf.DeligneLaumon.FrobeniusPowerDeckPoints` by the stated deck-automorphism route.
Private proved helpers establish Frobenius naturality between algebraic field extensions,
construct the automorphism of the cartesian model, and identify residueCard with the
absolute residue-field cardinality. The original theorem signature, translate definition,
and public imports are unchanged. The node proof now describes the explicit Lean argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Hom.exists_frobenius_power_deck_point`
(node `lem-zl-frobenius-power-deck-points`). No holes remain in the item, and no holes
are added or split off. This is a proof, not a decomposition.

Validation: the complete item compiled through `lcompile.py` in 4.0 seconds,
with exit code 0 and no warnings or errors.

## No longer needed

None. Both original public imports support the statements and translate definition.
The proof follows the existing scheme-theoretic route and retains its two DAG dependencies.
No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The previously split obligation closes using the
existing pullback, finite-field Frobenius, geometric-fibre projection, and residue-field
APIs. No coefficient or stalk transport theory is required here. Edge cases j=0 and
k1=k0 are included by the power and pullback constructions; an empty scheme has no
finite-point input. No equality with a separately chosen lift of the translated point
is asserted.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
