## What changed

Proved `AlgebraicGeometry.geometricallyIrreducible_adjoin_transcendental` in
`Sheaf.FieldTheory.GeometricIrreducibilityAddTranscendental`, preserving its full signature.
The proof applies the forward finite-family theorem to the singleton in `ULift K`.
Canonical intermediate-field equivalences identify the generated fields. A proved private
helper transports geometric irreducibility across their commuting square using the existing
separable-elements characterization. Only proof imports were added:
`Mathlib.RingTheory.AlgebraicIndependent.Transcendental`, `Mathlib.Algebra.Field.ULift`,
and `Sheaf.FieldTheory.GeometricIrreducibilitySeparable`.

The item's node now records this universe transport and both actual proof dependencies.
No definition, public signature, other module, or target statement changes.
The unit record `sk-i-dl-general-real` has no realized node that this specialization bypasses.
Sources read: Stacks `algebra.tex`, Tags 0G31, 0G32 and 0G33.

Validation: the complete module compiles cleanly through `lcompile.py` in 2.9 seconds.
Both existing dependency declarations remain proof obligations of their own modules.
The singleton range equality is rewritten explicitly before applying the inclusion theorem;
this avoids rewriting only visible types while leaving dependent inclusion casts behind.

## Proved and sorry left

Closed the original sole hole:
`AlgebraicGeometry.geometricallyIrreducible_adjoin_transcendental`
(node `lem-zl-geometric-irreducibility-add-transcendental`).
Item: 1 of 1 sorries proved, zero remaining; zero new holes and zero splits.
The private transport helper is fully proved.
The proof uses the existing named theorems
`AlgebraicGeometry.geometricallyIrreducible_transcendental_extension`
(node `lem-zl-geometric-irreducibility-transcendental`) and
`AlgebraicGeometry.geometricallyIrreducible_iff_separableElements_mem`
(node `lem-zl-geometric-irreducibility-separable`), whose pre-existing sorries are unchanged.

## No longer needed

None. The sole original proof dependency and both original public imports remain necessary.
All added imports are used: singleton independence, the field structure on `ULift`,
and the separable-elements criterion for transport between scheme universes.
No node or module is pruned. No new module or scratch Lean file is delivered.

## Where the brief, the DAG or earlier work was wrong

The planned singleton specialization is mathematically correct, but the existing finite-family
theorem quantifies its ambient field in `Type (max u v)`, whereas this item permits
`K : Type v` independently of `u`. A direct application fails with the universe constraint
`max u ?w = v`. The proof therefore lifts the ambient field and transports the result back.
This is a representation issue; neither theorem's mathematical statement needs correction.
The separable-elements node is used as a generic isomorphism-invariance tool in the same unit,
not as a replacement for the source's transcendental-extension argument.

Edge cases: no cardinality, characteristic, separability or nontrivial-extension hypothesis
is added; `M = L` is included. Both the original and lifted fields are nonzero fields.
All equivalences are explicit constructions from `ULift.algEquiv` and `equivMap`;
no data is chosen from an unproved existence assertion.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
