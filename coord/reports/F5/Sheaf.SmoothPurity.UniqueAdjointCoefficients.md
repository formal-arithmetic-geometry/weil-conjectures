## What changed

Filled both theorem proofs in `Sheaf.SmoothPurity.UniqueAdjointCoefficients`, preserving
all existing declarations, signatures, definitions, visibility and imports.
Two fully proved private helpers implement the existing node's conjugation calculation
and the naturality of the objectwise mate. The first uses injectivity of the target
adjunction's inverse Hom equivalence, the two counit compatibility equations, and
naturality of `b.inv`. The second uses the naturality of the Hom equivalence, `b.inv`,
and the source counit. The main theorem combines these calculations and transports
`IsIso` along the displayed composite.

The chain theorem substitutes the conjugation formulas, cancels the two middle
isomorphism components after applying `TX12`, uses naturality of the last right-adjoint
isomorphism, applies the assumed chain equation, and finishes by naturality of `aX`.
Remote single-file compilation against the current server state passed cleanly
with no warnings (4.0 seconds).
The file has no lines exceeding 100 columns.
This follows the existing seven-step proof of `det-sp-unique-adjoint-coefficients`;
no change to the proof route or its dependencies is needed. The source statement,
proof file and unit record were read. The unit's route is retained.

## Proved and sorry left

Original holes: 2. Holes closed: 2, at
`CategoryTheory.det_sp_unique_adjoint_coefficients` and
`CategoryTheory.det_sp_unique_adjoint_coefficients_chain`
(both attached to `det-sp-unique-adjoint-coefficients`).
Holes added: 0. Split-offs: 0. No `sorry` remains in the delivered module.
The two private calculation helpers are fully proved.

## No longer needed

None. No import, node or module is pruned. The proof uses the existing Mathlib
adjunction Hom-equivalence and unique-right-adjoint interfaces specified by the DAG.
The naturality calculation verifies directly that the defined components form the
mate transformation. No additional library imports are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement defect found. The coefficient stages and geometric
hypotheses remain exactly as stated. Both required equations are categorical, so
none of those hypotheses needs an extra restriction. The isomorphism implication
uses the proved conjugation formula, not an assertion that every invertible square
has invertible mate. No coherence identity for the comparisons `b01`, `b12`, `b02`
is introduced: the chain calculation uses precisely the given identity for `c_f`.


The retained sandbox was checked against the current source: only the two proved
private helpers and the two theorem proof bodies differ. No existing signature,
definition, docstring, visibility or import changed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
