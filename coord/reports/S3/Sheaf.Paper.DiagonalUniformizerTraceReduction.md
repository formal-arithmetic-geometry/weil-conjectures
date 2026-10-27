## What changed

The signature of `diagonalUniformizer_traceReduction` is unchanged. Its body now
uses a proved generic reconstruction theorem and the degree-one equation for the
Chern summand. Its original public imports are preserved. Two private proof
imports name the new modules `DiagonalFiniteTraceChernCriterion` and
`DiagonalUniformizerTraceChernDegree`.

`DiagonalFiniteTraceChernCriterion` constructs the actual isomorphism underlying
`FiniteRealization.shiftedLine`, composes it with the supplied full-unit derived
square and canonical-model transport, and uses the inverse of this composite to
express `d.traceq` in the canonical finite model. No data are chosen. The new irreducible predicate
`FiniteTraceChernDegree` names
only the Chern-component equation at generic coefficients, so its concrete
instances share their coefficient and derived-category instances. The comparison
definitions are also irreducible and their hom equations are proved explicitly.
Its theorem
`finitePresentedTraceEquation_of_chern` proves the other component is zero by the
canonical t-structure: the positive finite Tate line shifted by two is in degrees
at most -2, and the coefficient unit is in degrees at least zero. Biproduct
extensionality then reconstructs the whole trace from its Chern degree, and the
proof cancels the specified comparison to recover the original equation.

`DiagonalUniformizerTraceChernDegree` states the remaining geometric comparison
as the identity of the finite coefficient unit after precomposition with the
canonical Chern adjunct. This is one summand calculation, stated using only the
projective-line completed trace and its two coefficient changes: it has no
completed diagonal arrow, no Family or Reference, and no Noetherian or
localization conditions on the diagonal surface. It requires no comparison
of entire splittings, no assertion concerning the other summand, and no equality
detection for arbitrary derived arrows from their finite projections. Its
source-based proof in words starts from `tq.torsion_chern n` and
identifies the two factors after coefficient extension using the supplied root,
coefficient and full universal-unit normalizations.

No other existing module or node is changed. No target, definition or existing
statement is changed, and no module is withdrawn. The unit's projective-line
splitting/trace route is preserved.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_traceReduction`
(`lem-diagonal-uniformizer-trace-reduction`), using a new lower obligation.

The generic theorem
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.finitePresentedTraceEquation_of_chern`
(`lem-diagonal-finite-trace-chern-criterion`) and its private t-structure vanishing
helper are completely proved. The three comparison definitions are explicit
composites of existing maps and
isomorphisms; the fourth definition is their Chern-component equality. None
contains a hole.

Added exactly one hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_traceChernDegree`
(`lem-diagonal-uniformizer-trace-chern-degree`), with whole body `:= by sorry`.
The item itself has zero remaining holes; the delivery has one. This is a
reduction/decomposition of one hole to one strictly smaller summand calculation,
not a complete proof of the geometric normalization or a net hole reduction.
The vanishing component and the reconstruction argument are proved, rather than
included among the hypotheses of the remaining obligation.

Validation: all three delivery modules compiled successfully through lcompile.py
against the private overlay. The final item and remaining Chern-degree statement
compiled together with exit code zero. All profiling options were removed before
that check. The original theorem signature is preserved verbatim; the node
signatures, dependency references, proof-dependency unions and Lean line lengths
were also checked.

Edge cases checked: n=0 still uses exponent l, and hA makes the finite ring a
Z/l^(n+1)-algebra even for ramified uniformizers. No nonemptiness assumption on
the base or coefficient ring is used; the empty scheme and zero coefficient ring
have the same zero maps and identities. No quotient flatness is assumed.

## No longer needed

No existing import is removed and no existing module is withdrawn. No claim is
made that a whole module has left the targets' import closure.

The original route's comparison of the unit components of the entire completed
and finite splittings is unnecessary here: the unit component of every candidate
trace is zero by t-structure orthogonality. Only the positive Chern component
requires coefficient transport. The new obligation consequently does not ask for
a commuting diagram of entire splittings, preservation of their inverses, or a
separate unit-summand reduction theorem.

`lem-diagonal-completed-push-square` / `Sheaf.Paper.DiagonalCompletedPushSquare`
is no longer an explicit proof dependency of this item: the finite normalized
square is already supplied by `presentation`, so no square is constructed here.
The geometric Chern comparison still uses uniqueness of the full universal unit
recorded in the supplied square; this does not use the existence theorem.
The other original geometric dependencies remain needed by the Chern-degree
obligation and are recorded there, rather than advertised as pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan reduces both components of the whole splitting and then
inverts it. That is sufficient but stronger than needed. T-structure orthogonality
proves one component for every possible finite trace. After this step the only
geometric comparison required is degree one on the canonical Chern adjunct.
Existing `Result.torsion_chern` supplies the system-level identity, but none of
the read declarations identifies its image under all the supplied coefficient
realizations with this finite Chern composite. That remaining comparison is
exposed explicitly. No statement was disputed or weakened.

## New nodes

`lem-diagonal-finite-trace-chern-criterion` records the fully proved generic
reconstruction, its explicit comparison definitions and the single-component
predicate. Its proof uses the
finite-line and unit single comparisons, Mathlib t-structure orthogonality,
biproduct extensionality and cancellation of isomorphisms. It has no completed
coefficient, family or reference hypotheses.

`lem-diagonal-uniformizer-trace-chern-degree` records only the scalar-reduced
Chern-adjoint/trace composite. Its proof in words details how the finite
`torsion_chern n` identity is transported, and lists the existing root, Kummer,
coefficient and universal-unit interfaces it needs. It inherits the item's
chapter and unit. Blueprint searches for Chern, trace and Chern degree found
no duplicate of these supplied-model statements; the generic source splitting
and trace definitions were read instead of restated.

No change record is required: no existing interface or other module is changed.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
