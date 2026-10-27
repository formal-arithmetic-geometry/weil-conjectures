## What changed

Filled proofs in `lean/Sheaf/Paper/CoefficientTwistsDetailed.lean` without changing
any theorem signature, existing instance body, or public import. Added the
proof imports `Sheaf.Algebra.Homology.SignedLinePowerFlat` and
`import all Sheaf.Paper.IntegralConstructibleLinear`.

Rank-one local trivializations supply the hypotheses of the existing general-site
signed-power flatness theorem. Its positive powers and negative internal duals are
definitionally the coefficient twists. Finite colimit preservation gives additivity.
The integral coefficient action is checked before sheafification and carried through
complexes and derived localization. The full-subcategory functor inherits linearity
and additivity. The rational morphism formula is scalar base change. The integral
comparison restricts to the full subcategory, and its rational comparison follows
by tensor induction. The coefficient object comparison uses compatibility with the
single-complex functor. Common-stage object and representative-map formulas follow
from the recorded coefficientPairFunctor_exists specifications.

Disabled asynchronous elaboration in this file to avoid concurrent checks of its
large completed-coefficient expressions. Updated the existing exactness node's
proof, dependencies and origin to match this route. No new theorem, consumer
adaptation or node is added.

A clean proof compile passed in 56.9 seconds; the first delivery compile took
74.4 seconds and was refused before pushing. To reduce expansion in the final
record, added four transparent family-type definitions and used them in the
CoefficientTateTwistData fields. The field types remain definitionally equal to
the originals. The existing coefficientTateTwists construction is verbatim.
The downstream use check finds no external consumer of either declaration.
The change is recorded in `coord/changes/coefficient-twist-family-checking.md`.
The revised module compiled cleanly in 58.0 seconds.

## Proved and sorry left

Closed 11 of the item's original 20 holes; added 0 holes and split off 0 statements.
These are proofs from existing declarations, some of which still have their own
recorded holes; this report does not claim axiom-free completion of the targets.

Closed (all in namespace `WeilConjectures`):

- `coefficientTwistLine_exact`.
- `integralComplexTwist_linear_statement`.
- `integralConstructibleComplexTwistFunctor_linear_statement`.
- `integralConstructibleComplexTwistFunctor_additive_statement`.
- `rationalComplexTwistFunctor_obj`.
- `rationalComplexTwistFunctor_map`.
- `twistIntegralScalarComparison_existsUnique`.
- `twistRationalOrdinaryComparison_existsUnique`.
- `rationalCoefficientTwist_scalarExtension`.
- `algebraicClosureComplexTwistFunctor_obj`.
- `algebraicClosureComplexTwistFunctor_map_exists`.

The following 9 original named theorem holes remain unchanged. Their existing
source and proof docstrings cite `def-coefficient-twists-detailed`; no anonymous
or definition hole is introduced:

- `integralCoefficientTwist_constructible`.
- `integralComplexTwist_constructible`.
- `twistScalarMaps_existsUnique`.
- `twistLineScalarIso_existsUnique`.
- `twistSheafScalarComparison_existsUnique`.
- `twistScalarMaps_identity`.
- `twistScalarMaps_composition`.
- `rationalTwistScalarComparison_unit`.
- `coefficientTwistStageComparison_coherent`.

`coefficientTwistLine_exact` is attached to
`lem-route-coefficient-twist-line-exact`. The other declarations retain their
existing blueprint tags; this delivery introduces no new hole needing an attachment.

## No longer needed

No public import or library module is withdrawn. The exactness node no longer
needs `lem-weil-signed-line-tensor-equivalence`,
`lem-pc-sheaf-modules-tensor-closed`, or
`lem-galois-equivalence-preserves-limits`: direct signed-power flatness already
supplies finite limit and colimit preservation, and Mathlib supplies additivity.
Removed the obsolete `tool_uses` entries for the first two nodes. These nodes may
still be needed by other consumers; this is only a dependency reduction for this
exactness proof. No claim is made that their modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned signedLineTensor_equivalence route imports this item module itself,
so using it here would form an import cycle. The existing general-site signed-line
flatness theorem avoids that cycle and applies directly to the same constructed
powers after explicit universe specialization. Its definition agrees with
coefficientTwistLine by integer cases. The unit's own statement and proof steps
are preserved.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
