## What changed

Proved `AlgebraicGeometry.ProEtale.pbcRectangleDerivedLimit` in
`Sheaf.Paper.PbcRectangleDerivedLimit`, preserving its exact signature and the
unchanged `pbcRoosProjection` definition. Functoriality transports the rectangle;
postcomposing naturality of p with a product projection gives both outer component
equalities. Evaluating the original rectangle gives the middle equality.
No new declaration, definition, instance or assumption is introduced.

The original proof compiled in 4.1 seconds. After import pruning, the module compiled
in 3.6 seconds, and its sole direct importer, the original
`Sheaf.Paper.CompletedMapReduction`, compiled against it in 4.6 seconds. Temporary
axiom probes and the unchanged consumer copy were removed after those checks.
Updated the existing DAG node's proof, proof dependencies and origin to match Lean.
The current blueprint assertion and the unit's realized steps are preserved.

Public import pruning is recorded in
`coord/changes/E1-pbc-rectangle-derived-limit-imports.md`, including all transitive
users and the direct consumer check.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.pbcRectangleDerivedLimit`
(node `lem-weil-pbc-rectangle-derived-limit`).
Added 0 holes; split off 0 statements. The delivered module contains zero `sorry`.

`#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` and an inherited
`sorryAx` for both the unchanged `pbcRoosProjection` and the proved theorem. The
existing evaluated-tower/product setup still depends on lower unproved statements;
this delivery does not claim those dependencies closed. No axiom is introduced.

## No longer needed

Removed imports:

- `Sheaf.Paper.SequentialDerivedInverseLimitFunctor` (public), replaced by
  `Mathlib.CategoryTheory.Triangulated.Functor`, needed by the existing statement.
- `Sheaf.Paper.CompletedRlimFunctor` (proof-only).
- `Sheaf.Paper.CompletedTowerCompatibility` (proof-only).

The proof does not invoke the declarations of `prop-weil-pbc-rlim-functoriality` or
`lem-weil-pbc-tower-compatibility`: F and the rectangle are already supplied as
hypotheses. Neither `sequentialDerivedInverseLimit_functorial`,
`completedRlim_computation`, `completedRlim_properties`, `completedRlim_roos`, nor
`AdicCoefficientDatum.fourTowers_compatibility` is needed to prove this conditional
statement. Their construction roles remain with the callers.

The existence theorem `pbcRoosTriangle` of `prop-weil-pbc-roos-triangle` is likewise
not applied: p and its naturality are inputs. Its module remains publicly imported
because it defines the product functor used by the theorem and projection. The
Roos distinguishedness and triangulated hypotheses are preserved exactly, although
the elementary calculation needs only functoriality and naturality.

Accordingly the existing node has no non-elementary proof dependencies. Statement
dependencies remain intact. No unit statement or realized unit step is bypassed,
and no globally unreachable module is asserted without a closure audit.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The declared proof dependencies describe the
construction of inputs that the theorem already assumes; importing those construction
theorems is unnecessary for the conditional rectangle calculation. The previous
node's two-step argument was otherwise correct and is now implemented in Lean.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
