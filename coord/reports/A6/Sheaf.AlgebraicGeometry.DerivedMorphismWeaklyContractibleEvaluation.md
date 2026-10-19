## What changed

Proved five compatibility clauses in the item module. Local extension follows from the
sheafification and comparison adjunction unit identities and naturality. Restriction cancels
the bijective pro-etale sheafification units in their naturality squares. Identity specializes
local extension at the terminal etale object. Naturality in both arguments follows from
naturality of the localized comparison isomorphism, followed by sheafification and comparison
adjunction transposition and cancellation of the evaluation units. All private helpers are proved.

No imports, public signatures, definitions or node routes changed.

Resumed against the current shared sources and retained all current dependency imports.
The complete delivered module passed `lcompile.py` against the current server library
(exit code 0, 11.2 seconds, 2026-10-19).

## Proved and sorry left

Closed five of the original nine holes:

- `AlgebraicGeometry.Scheme.derivedMorphism_evaluation_extends_local`
- `AlgebraicGeometry.Scheme.derivedMorphism_evaluation_restriction`
- `AlgebraicGeometry.Scheme.derivedMorphism_evaluation_identity`
- `AlgebraicGeometry.Scheme.derivedMorphism_evaluation_natural`
- `AlgebraicGeometry.Scheme.derivedMorphism_isoEvaluation_natural`

Four original holes remain, all at node
`lem-weil-pbc-derived-isomorphism-sheaf-wcontractible-evaluation`:

- `AlgebraicGeometry.Scheme.derivedMorphism_weaklyContractible_evaluation`
- `AlgebraicGeometry.Scheme.derivedMorphism_evaluation_composition`
- `AlgebraicGeometry.Scheme.derivedMorphism_isoEvaluation_composition`
- `AlgebraicGeometry.Scheme.derivedMorphism_evaluation_scalarExtension`

No holes added and no split-offs. Main bijectivity requires the finite-diagonal derived
internal-Hom comparison. Composition requires compatibility with the sheafified product
composition. Scalar extension requires the coherent tensor adjunctions and their mates.

## No longer needed

None. The four retained open clauses still use the planned imports and proof dependencies.
The compatibility proofs follow the recorded canonical-comparison route.

## Where the brief, the DAG or earlier work was wrong

An attempted reduction of Isom composition to Hom composition requires explicit compatibility
of evaluation with the Isom-to-Hom map; it does not follow by definitional unfolding.
The attempted reduction was withdrawn. No mathematical statement was changed.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
