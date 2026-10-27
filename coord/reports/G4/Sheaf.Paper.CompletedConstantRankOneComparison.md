## What changed

Proved `AlgebraicGeometry.Scheme.completedConstantComparisonMap_rankOne_isIso` in
`Sheaf.Paper.CompletedConstantRankOneComparison`, with its signature unchanged.

The proof constructs the evaluation isomorphisms from the completion's finite module
quotients to the ordinary ring quotients, sheafifies them, and checks their transition
compatibility. It reuses the proved `CompletedConstantReduction.constantChange_unit`
isomorphism for the source. Its inverse sends a section to its tensor with 1; the fixed
finite-projection formula then identifies the comparison cone with the ring limit cone.
Transport and reflection of limits prove that the actual comparison map is invertible.
All auxiliary constructions and proofs are private and fully proved in the item module.

Added proof imports of `Sheaf.Paper.CompletedConstantSheafReduction` (with `import all`
to reuse its private unit isomorphism) and
`Mathlib.RingTheory.AdicCompletion.Completeness`. Updated the item's node proof to
record the implemented cone argument. No existing definitions or statements changed.

Validation: the complete item module passed the server `lcompile.py` check without
warnings in 23.3 seconds, below the 60-second limit.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.completedConstantComparisonMap_rankOne_isIso`
(node `lem-weil-pbc-completed-constant-rank-one-comparison`).

Zero holes remain in the delivered module. Zero holes were added or split off.
The quotient evaluation proof uses the existing completion kernel and surjectivity
lemmas. It imposes no extra nonzero-ring or proper-ideal assumption, so includes the
zero ring, the zero ideal, and the unit ideal.

## No longer needed

None. No original import was removed. All four planned dependency nodes are used:
`lem-weil-pbc-completed-constant-sheaf-reduction`,
`lem-weil-pbc-adic-completion-mod-power`,
`def-weil-pbc-completed-constant-projection-maps`, and
`def-weil-pbc-completed-constant-residue-data`.
No module or DAG node is withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement repair was needed. The existing private
`CompletedConstantReduction.constantChange_unit` already supplies the source
isomorphism required by the plan, including a constructive inverse; using it avoids
repeating or splitting off that obligation. The finite quotient identifications and
all compatibility checks are proved directly here from the existing declarations.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
