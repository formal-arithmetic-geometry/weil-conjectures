## What changed

Replaced the proof of WeilConjectures.sfCompletedMateDomain, preserving its signature
and both definitions. The proof assembles the existing finite reduction equation,
strict-limit equation, proper complete base change, actual-coefficient constructible
preservation, and adic smooth base change. Geometry comes from the already proved
sf_baseChange_geometry_hypotheses. Private proved helpers establish prime membership,
prime-power quotient order units, and bounded constructible etale sources of canonical
reductions. The latter uses import all of PbcUniformReductionCriterion to reuse its
proved uniformProfile_localEffectivity and functionRealizationComparison; it introduces
no new object by an arbitrary existence choice.

Added Sheaf.Paper.SfCompletedExchangeTransport with the fixed canonical equality between
the smooth completed mate and the ordered proper completed exchange. This isolates
only the normalization comparison; it asserts no invertibility or constructible landing.
The parent proof uses it to transfer proper invertibility and independently assembles
all other conclusions. Its endpoint transports are the published counit-normalized
cbcDatumCompletedTransport and coefficient equality eqToIso, not existential choices.
The complete proof in words is in its docstring and node.

Updated the parent proof/dependency record to the proof actually written. No target,
existing signature, public import, definition body, consumer, or source-library module
changes. No forced adaptations. The two submitted modules compile through lcompile.py;
the parent completed cleanly in 19.1 seconds. Both definition bodies and the theorem
signature were compared verbatim with the shared source. Local instance priority and
irreducibility attributes prevent an unrelated IntegralHom universe from being inferred
for the fixed pro-etale ring-module derived category.

## Proved and sorry left

Original holes: one, WeilConjectures.sfCompletedMateDomain
(lem-sf-bc-completed-mate-domain). Its assembly has no sorry.
Added holes: one, WeilConjectures.sfCompletedExchange_transport
(lem-sf-completed-exchange-transport), in its own module, with proof exactly by sorry.
This is a decomposition: one upper hole closed, one strictly smaller normalization
hole added; net zero holes. No holes in definitions or private helpers.

The new comparison has arbitrary schemes and complete input, and only asserts one
map equality. Empty schemes and zero inputs use the same reflector cancellation.
No assertion that equal finite reductions imply equal arrows is used.

## No longer needed

The ordinary proof import of PbcUniformReductionCriterion is replaced by import all
so that its proved private construction can be reused.

Removed private proof imports Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound,
Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect,
Sheaf.Paper.ConstructibleCompleteBaseChange, and
Sheaf.Paper.FiniteRingConstructibleDerivedOrigin.

The parent proof no longer directly uses lem-cbc-compactification-geometry-fibre-bound
or lem-weil-pbc-proper-base-change: lem-sf-bc-geometry-hypotheses supplies the exact
package geometry and properness. It no longer needs a separate use of
lem-weil-pbc-standard-quotients-perfect: the datum already contains quotient perfectness.
It uses lem-weil-pbc-actual-coefficient-constructible-preservation directly instead of
cor-weil-pbc-constructible-complete, whose current Lean specializes to the unlifted datum
and a different coefficient universe. It uses the normalized local-effectivity argument
of the published uniform criterion instead of the differently-universed
lem-weil-pbc-finite-ring-constructible-derived-origin. Definitions of exchange,
completed base change, and scheme conventions remain in the statements or underlying
constructions; they were removed only as separate proof steps. These modules and nodes
are not withdrawn and can remain needed by other parents or transitive dependencies.

## Where the brief, the DAG or earlier work was wrong

The old plan treats its cited completed-operation comparison as also supplying the
explicit cbcDatumCompletedTransport conjugation with d.completedExchange. Its current
Lean proves finite reduction and the ordinary strict-tower realization, and does not
state that second-presentation equality. The new node isolates precisely that step.
PbcActualCompletedExchangeTransport was inspected: it compares another actual mate
with existential source/target comparisons, insufficient to identify these fixed ones.

The old plan also applies finiteRing_constructibleDerived_origin to quotients in
Type (u+1), while that theorem accepts B : Type u and inserts its own ULift. The proof
instead uses the already proved local-effectivity construction in the right universe.
Likewise constructibleComplete_properBaseChange uses E : Type (u+1) and the unlifted
pbcPadicCoefficientDatum, whereas the item uses E : Type u and pbcIntegralDatum. The
original-datum constructible-preservation theorem fits without any statement change.

The unit route is unchanged: proper base change and smooth base change remain the
sources of invertibility; their canonical comparisons and full-subcategory restriction
are retained. Mathlib semantic, pattern and source searches found generic adjunction
and mate APIs, not this completed-coefficient normalization.

## New nodes

lem-sf-completed-exchange-transport records the equality of the two specified completed
exchange presentations. Its three proof steps identify ordinary mates using resolving
counits, compare the two completed arrows after the completion unit, and cancel that
unit by the reflector Hom bijection into the complete target. This is strictly the
normalization part of the parent, independent of all its geometric invertibility,
finite origin, and constructible landing conclusions. No change record is needed:
existing statements and definitions stay unchanged.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
