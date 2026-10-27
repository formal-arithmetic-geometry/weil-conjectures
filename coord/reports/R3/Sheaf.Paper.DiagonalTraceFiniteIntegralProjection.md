## What changed

The original signature of `diagonalTrace_finiteIntegralProjection` is preserved.
Its proof now combines the finite pretrace component formula with the actual
inverse-splitting trace. Private helpers prove that the trace kills the twisted
unit, sends the Chern adjunct to one, and identify a derived-limit projection of
the coefficient cone with the literal ordinary coefficient projection. The final
calculation is abstracted over its input map and the underlying category, so
concrete completed-sheaf definitions are instantiated only at the end. The trace
calculation uses the existing proved twisted-splitting component equations, rather
than assuming an integration identity.

Using components makes the transport calculation shorter: it only transports the
unit and Chern maps; the inverse splitting and second projection are handled by
the actual model trace in Lean.

The new module `Sheaf.Paper.DiagonalTraceFinitePretraceComponents` states the
remaining comparison before any trace is applied. It takes a `Presentation`,
without a `Result`, splitting inverse, trace, or trace-normalization hypotheses.
Its conclusion is a decomposition with an arbitrary base term and coefficient-one
relative Chern term. The existing item then applies the trace to this sum and
performs the cancellation in Lean. This is a decomposition, not a net hole closure.

The proved general integration calculation and coefficient-cone normalization
now have separate modules, `Sheaf.Paper.DiagonalTraceModelTraceComponents` and
`Sheaf.Paper.DiagonalTraceCoefficientProjection`. This keeps coefficient
normalization independent of the imports used to prove the twisted splitting.
The item imports the general integration API. That module privately imports
the coefficient-projection API and the twisted-splitting proof. The general
calculation needs the presentation interface and does not import the supported-
source or diagonal-limit witness interfaces.

Only the item module and node, the three new modules and their nodes, and this
report change. No existing statement, definition, public import, or consumer changes.

Validation: `lcompile.py` accepted all four production modules. The final
integration helper and the item compiled together. The DAG signatures match
Lean, and the original item signature is unchanged.

## Proved and sorry left

Closed the original proof body of
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteIntegralProjection`
(node `lem-sfb-diagonal-trace-finite-integral-projection`): 1 of 1 original holes.

Added one hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finitePretrace_components`
(node `lem-sfb-diagonal-trace-finite-pretrace-components`). This is a pretrace
component comparison, not the integration statement under another name. It has no
trace in its hypotheses or conclusion and identifies the base summand while
fixing the Chern coefficient of the pushforward class before trace. The proof
after applying the trace, including projection normalization, is complete Lean. Net textual hole reduction: zero.
No holes occur in private helpers or definitions. Two new public helper theorems
have complete proofs and introduce no holes:
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_integral_of_components`
and
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_exactConeComparison_projection`.

## No longer needed

No original import was removed. The full finite integral theorem `det-sp-p1-trace`
(`Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace`) is no longer a direct proof
dependency: its pretrace component formula
`lem-sp-p1-diagonal-comparison-components` suffices, followed by the explicit
inverse-splitting trace calculation. The component formula remains within the
same projective-line adjunction unit route. No module is withdrawn, and no claim
is made that the finite trace module is unreachable from all other targets.

The item imports the proved general component-integration module. The twisted-
splitting proof and coefficient-projection API imports are owned by that module;
the derived single-functor proof import is owned by the coefficient-projection
module. These dependencies remain needed; moving their imports is not pruning.

The original coefficient/source/limit comparison dependencies remain necessary
for the new finite pretrace comparison; they are not pruned globally.

## Where the brief, the DAG or earlier work was wrong

The original four-step plan elided a substantial compatibility calculation
between the normalized completed source/class cones and the finite component
formula. The source signatures provide the required data, but not this derived
comparison equation. The new node isolates precisely that calculation before
trace. The later cancellation and conversion to the specified ordinary
coefficient projection are proved here, rather than left inside another integral
projection assertion. No mathematical statement or unit route was changed.

The new statement was checked at the empty base and at n=0: the former is the
zero-category identity and the latter uses exponent 1. Both projections are
retained. A change of projective-line model can contribute a base line only; the
arbitrary beta term retains that contribution rather than assuming it is zero.

## New nodes

`lem-sfb-diagonal-trace-finite-pretrace-components`, module
`Sheaf.Paper.DiagonalTraceFinitePretraceComponents`, isolates the evaluated
supported Cartier component formula. Its docstring describes the source, root,
limit/direct-image, evaluation, and finite Chern normalizations needed to
transport the existing finite geometric component formula. It is strictly a
pretrace step: it can be used with any normalized presentation and does not
require a splitting or a trace. No change record is needed because existing
interfaces are unchanged.

`lem-sfb-diagonal-trace-exact-cone-projection`, module
`Sheaf.Paper.DiagonalTraceCoefficientProjection`, is proved. It gives the generic
ordinary coefficient cone projection under the normalized derived-limit and
single-object comparisons. Its private proof uses the derived-limit normalization
on a single complex, naturality, and the ordinary cone lift equation.

`lem-sfb-diagonal-trace-model-trace-components`, module
`Sheaf.Paper.DiagonalTraceModelTraceComponents`, is proved. Its public theorem
combines the existing twisted-splitting component theorem, cancellation of the inverse splitting, and the coefficient
projection normalization. It integrates any base-plus-Chern pretrace formula
for arbitrary schemes X and S. The supported diagonal theorem supplies that
formula separately. Its private helpers introduce no holes.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
