## What changed

Replaced the sole hole in `Sheaf.Paper.DiagonalTraceFinitePretraceComponents` by a
proof through the Chern adjunct of the actual diagonal divisor line. Its statement
and public import are unchanged. The new proof imports
`DiagonalTraceFiniteDivisorAdjoint` and `DiagonalTraceDivisorChernAdjoint` privately.

Added five modules, including two proved additive APIs extracted for compilation
time. `DiagonalTraceDiagonalPic` isolates a scheme-theoretic Picard factorization for either projection and any projective-line model.
`DiagonalTraceDivisorChernAdjoint` proves the resulting tower Chern component
formula, including additivity of the concrete firstChern construction and its
adjunction calculation, using the existing tower_firstChern_pullback theorem.
`DiagonalTraceFiniteDivisorAdjoint` isolates only the normalized finite comparison
from the supported completed arrow to that divisor Chern adjunct; it needs no
choice of projection, decomposition of the line, base component or trace.

The item proof pulls invertibility along the structural map and f, evaluates the
proved tower formula, and composes it with the coefficient projection. There are
no definition changes and no changes to any other existing module.

Validation: each of the six modules passed lcompile's per-file check. The item
compiles without warnings. All development profiling options are removed. The
delivery command rechecks the complete cleaned packet.

## Proved and sorry left

Closed the item's one syntactic hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finitePretrace_components`.
Also proved
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_divisorChernAdjoint_components`
and its private additivity lemmas for firstChernR and firstChern. Also proved
`AlgebraicGeometry.ProEtale.SpTowerClasses.tower_lineBundleEtaleClass_mul` and
`AlgebraicGeometry.ProEtale.SpTowerClasses.tower_lineBundleClass_mul` in separate
new modules. The large construction definitions are irreducible
only locally in this proof module. Generic private additive transport lemmas
avoid expanding concrete sheaf comparisons repeatedly. The proof uses the source
modules' sheafification-instance setup and restores the existing instance at the
end. No shared reducibility attribute or instance priority is changed.

Two new holes remain, both named public theorems in separate new modules:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_diagonalPic_factorization`
  (lem-sfb-diagonal-trace-diagonal-pic).
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteDivisorAdjoint`
  (lem-sfb-diagonal-trace-finite-divisor-adjoint).

This is a decomposition: one old hole closed, two added, zero in the item itself.
It is not a net proof. The Picard lemma has no coefficients, completed categories,
limits or supported arrow. The finite comparison gives the actual divisor Chern
adjunct, without asserting any component formula. The intervening Chern and
adjunction calculation is fully proved rather than a renamed obligation.

Edge cases checked mathematically: the Picard degree is one on every component,
including for a disconnected or nonreduced base; on the empty base the unit line
works. The finite projection uses exponent n+1, so n=0 is included. Swapping
projections changes a local diagonal equation by a unit and leaves its divisor
class unchanged. The Chern additivity and adjunction proof is valid for arbitrary
base lines, including the trivial line.

## No longer needed

No original import was removed: the item originally imported only
`Sheaf.Paper.DiagonalTraceSources`, needed by its statement.

The item no longer directly uses
`lem-sp-p1-diagonal-comparison-components`
(`Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents`). Its standard-chart
component equation and transport to the arbitrary projective model are replaced
by the divisor Picard factorization and the proved tower Chern calculation.
This is pruning from this argument only; no declaration or module is withdrawn.

The prior direct dependencies
`lem-pur-coefficient-system-derived-comparison` and
`lem-weil-ringed-tower-pushforward-limit-comparison` remain needed in the new
finite-divisor comparison node. The coefficient, presentation, source and limit
notions remain needed as well; none is claimed pruned. No unit statement or step
is bypassed. The exact-cone projection is reused as a proved comparison tool.

## Where the brief, the DAG or earlier work was wrong

The original plan required transporting a standard-chart component formula to an
arbitrary projective-line model by absorbing a base line into beta. It did not
give a separate declaration for that Picard factorization. The new route
states this geometric obligation explicitly and proves the Chern additivity and
adjunction steps above it. The finite normalization and model-change obligations
are now separate; neither new hole repeats the item's conclusion.

The generic projective-bundle Picard classification is used only in the proof
plan of the scheme-theoretic Picard lemma, with its arbitrary-base formulation.
Its classification theorem is not claimed proved here. The original unit's
finite reduction and trace route is retained.

## New nodes

`lem-sfb-diagonal-trace-diagonal-pic`: factor the actual diagonal divisor line as
f-pullback of a base line times the relative hyperplane line. Source: the four
product-chart equations, EGA II Remark 4.2.7 and the existing arbitrary-base
projective-bundle Picard classification. New module has one hole.

`lem-sfb-diagonal-trace-divisor-chern-adjoint`: the two components of that line's
tower Chern adjunct. Source: Picard additivity, existing tower Chern pullback and
adjunction naturality. New module has no holes.

`lem-sfb-diagonal-trace-finite-divisor-adjoint`: identify the finite projected
supported diagonal with the projected coefficient unit followed by the evaluated
restricted divisor Chern adjunct. Source: diagonal limit normalization, exact
restriction/direct-image comparisons and Cartier forget support. New module has
one hole. The normalized supported source supplies Delta followed by f = id,
so no hypothesis selecting a projection is needed here.

All new nodes belong to sk-prop-diagonal-tower and record three kinds of Mathlib
search, exact Lean signatures, sources and full proof plans. No change record is
needed: no existing definition or statement changed.

`lem-sfb-tower-line-bundle-etale-class-additive`: the Picard-to-H1 tensor law
after exact change of site. Fully proved in TowerLineBundleEtaleClassAdditive.

`lem-sfb-tower-line-bundle-class-additive`: the same law after making the constant
tower. Fully proved in TowerLineBundleClassAdditive. These two APIs were separated
only after local irreducibility and generic transport lemmas left the combined
file over 60 seconds. Profiling found roughly 14 and 26 seconds of type checking
in these declarations, in addition to the linting cost. They introduce no holes.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
