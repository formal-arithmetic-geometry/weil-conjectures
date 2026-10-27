## What changed

In `Sheaf.AlgebraicGeometry.PrincipalLogIdealTautologicalPolarization`, proved
`AlgebraicGeometry.principalLogIdeal_polarization_identity` and
`AlgebraicGeometry.principalLogIdeal_polarization_composition`.

Both proofs transpose morphisms under the section-normalized tensor-pullback
adjunction. A proved private helper detects equality on local log-generator frames:
free generation reduces arbitrary sections to scalar multiples, and sheaf separation
glues equality. The identity proof uses the identity relative étale test map and the
unit equation for left-adjoint uniqueness. The composition proof uses the actual
`CompEq` equation on restricted opens, the unit equation for the composition
comparison, and naturality of pullback sections. These proofs do not require the
three remaining existence theorems.

All existing declaration signatures, definitions, attributes and public imports are
unchanged. The new helpers are private and proved. The item's node step 9 and
`proof_origin` now record the implemented argument and distinguish the remaining
plan. No other existing module or node was changed.

Validation: the final file compiled without errors or warnings through lcompile in
6.8 seconds after import cleanup. Delivery runs the required preflight and axiom checks.

## Proved and sorry left

Closed 2 of the original 5 holes, without adding any holes:

- `AlgebraicGeometry.principalLogIdeal_polarization_identity`.
- `AlgebraicGeometry.principalLogIdeal_polarization_composition`.

The following 3 named theorems retain their original whole-proof `sorry`, source,
and proof docstrings, all attached to
`lem-trf-principal-log-ideal-tautological-polarization`:

- `AlgebraicGeometry.principalLogIdeal_tautological_polarization`.
- `AlgebraicGeometry.principalLogIdeal_polarization_logIso`.
- `AlgebraicGeometry.principalLogIdeal_polarization_strict_comparison`.

Zero split-off statements and zero new holes. This is a partial proof delivery with
two holes closed, rather than a decomposition into new statements.

## No longer needed

Removed these unused proof-only imports from the item:

- `WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle`.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`.
- `WeilConjectures.Topology.GlueSheavesOfModules`.
- `Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover`.
- `Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.

The proved compatibility clauses use `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`
directly for sheaf separation, together with the existing public frame and normalized
adjunction APIs. No public import is removed. No whole DAG dependency or module is
claimed pruned: the unchanged existence and transport holes still have the original
construction plan, including cocycle gluing, invertible pullback, and relative ampleness.
Their node dependencies and existing tool approvals are retained.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. Step 9 does not need to rebuild or glue an isomorphism
to prove identity and composition once the comparison maps and local generator cover
are supplied. Adjunction injectivity and sheaf separation prove their equality directly.
The empty-scheme case is included: the point-indexed cover and all local tests are
empty, and sheaf separation still determines the unique map. No fine, strict, finite
or affine hypotheses have been added to either compatibility theorem.

Searches used the prescribed msearch leanfinder, loogle, and grep interfaces, plus
local searches in both library roots and Mathlib. The results did not supply the log
compatibilities as a theorem. Existing proofs in `LineProjChartPullback` and
`GradedImmersionAmpleCriterion` show the relevant normalized-unit calculations;
the generic arguments are proved locally here without importing those larger modules.
The source ILO VIII 3.3.8, printed pages 107--108, and the unit blueprint were read.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
