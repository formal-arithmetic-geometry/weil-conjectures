## What changed

Implemented the eleven `WordLaws` clauses in `CounitRealizationSubstitution`: actual
counit invertibility, normalization under words, arbitrary morphism naturality,
cut and parenthesization, whole-counit substitution, unique conjugate comparisons,
composition, inverse, and both whiskering laws. Implemented the scalar-law deduction
by naturality, the adjunction triangle, and cancellation of the published chi maps.
Existing declarations and public imports are unchanged.

Two new ambient scalar normalization squares isolate the strict quotient calculation
in parent proof steps 8--10 and 11. Both are independent of constructibility and
completion invertibility. They are genuine separate arguments, not copies of either
the whole theorem or ScalarLaws: their inputs are arbitrary ambient complexes and
individual normalized scalar models, and the parent transports their equations
through its original system counit and cancels completion isomorphisms.

## Proved and sorry left

Closed the single body hole of
`WeilConjectures.CounitRealization.counitRealizationSubstitution` by a complete
combination proof. Added two named holes:

- `WeilConjectures.scalarModelAssociativity`, node
  `lem-trf-scalar-model-associativity`.
- `WeilConjectures.scalarModelUnit`, node `lem-trf-scalar-model-unit`.

This is a decomposition, not a net hole reduction: one original hole closed, two
new holes added; no sorry remains in the item module. The named private word-law
helpers are proved. The new squares have full statements, sources, complete
natural-language proofs, and matching DAG records. Edge cases checked in the
argument include zero complexes, empty sites, identity coefficient extensions,
and arbitrary unbounded inputs; no finite quotient flatness is assumed.

Validation: `lcompile.py` compiled the item module without errors or warnings
in 21.6 seconds. Both new scalar modules also compiled individually in the
sandbox dependency build; their two named theorem holes are intentional.

## No longer needed

Removed private proof imports of `Sheaf.Paper.NormalizedDVREffectivity`,
`Sheaf.Paper.IntegralDerivedOperationsOnSlices`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
`Sheaf.Paper.QuotientScalarComparisonDescent`,
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`, and
`Sheaf.TraceFormula.IntegralConeCounitRealization` from the item.

The original direct proof dependencies on normalized DVR effectivity and the
K-flat, quotient-descent and cone-counit scalar calculation are replaced in this
node by reconstruction and the two separate scalar-square nodes. The scalar
calculation dependencies remain needed in the new nodes; no such module is claimed
pruned from the target closure. The source-library tree is unchanged. All original
public statement imports remain necessary for the unchanged interface.

Removed the parent's obsolete `tool_uses` approvals for
`lem-coef-derived-system-evaluation-calculus`,
`lem-coef-normalized-dvr-effectivity`, `lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`, `lem-pur-quotient-scalar-comparison-descent`,
and `lem-pur-kflat-change-of-rings`. The new parent proof does not directly use
these tools; the scalar calculations retain their dependencies in their own nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed definition was found. The original scalar plan
requires an explicit normalization bridge from the whole-system scalar model to
the prescribed ordinary derived associator and reduction adjunction unit. None
of its existing declared dependencies directly states either square. The new
nodes isolate these precise calculations. The module and blueprint searches found
no duplicate; existing scalarExtensionTowerCoherence concerns scalar/tensor and
scalar/pullback squares, not these two realization equations.

The existing generic `purNormalizedReconstruction` theorem supplies exactly the
actual-counit invertibility needed in step 1, avoiding a second effectivity proof.
Its node is `lem-pur-normalized-reconstruction-adjunction-calculus`; it is a generic
coefficient reconstruction tool, not a replacement of the trace-transport unit
route. This new off-route generic-tool use requires the maintainer's independent
review; no tool approval was added by the worker.

## New nodes

`lem-trf-scalar-model-associativity` states the ambient pre-completion associativity
square, with the actual middle whole-system counit. Its proof uses simultaneous
K-flat quotient representatives, zero shifted Roos coordinates, the whole-counit
identity, and balanced multiplication before localization.

`lem-trf-scalar-model-unit` states the ambient identity square with the actual
reconstruction unit. Its proof compares the strict quotient augmentation with the
adjunction unit under ordinary multiplication before localization. No definition
or signature change record is needed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
