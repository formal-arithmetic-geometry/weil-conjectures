## What changed

Replaced the hole in `AlgebraicGeometry.Etale.sfP1IntegralTransport` by explicit
construction of its witnesses and a factorization through two strictly smaller
comparison equations. Its signature and original public imports are unchanged.
The two new comparison modules are proof imports.

`SfP1IntegralTransportData` constructs the self-product map of the specified
isomorphism and proves its Cartesian projection and diagonal squares. It constructs
the constant-object comparison, the inverse push-pull comparison along the
isomorphism, and the normalized line comparison. The diagonal class is the actual
pullback of the given supported Ext representative through inverse diagonal
exchange and proper forget-supports. The trace is the given ordinary trace
transported by direct-image composition and the isomorphism over the base.
The supported Ext realization is named `supportedMap` with fixed ordinary
functor endpoints. A proved private defining equation identifies the existing
ordinary supported map with its projected form, and a generic categorical lemma
uses those defining equations without normalizing the whole derived diagram.
The two arrows are packaged as an explicit `datum`, with proved equations for
its two fields. Every definition has a concrete body; no map is selected from a
mere existence statement. Proper exchange is inverted using the existing proper-base-change
theorem, which uniquely determines its inverse.

The source equation is reduced to `sectionComparison`, which concerns only the
canonical diagonal section unit. In particular it has no N, twist, Ext class,
splitting family, or trace. Naturality of the explicitly defined projection
comparison and cancellation of the coefficient isomorphism then prove the equation
for an arbitrary supported Ext representative in Lean. The second equation,
`traceComparison`, concerns only the explicitly constructed trace and the two
ordinary chart traces. It contains no Ext representative or integral identity.
The main proof composes these equations by functoriality, for both projections.
The middle comparison uses the generic irreducible `middleComposite`; the
naturality lemma unfolds it only with abstract functors. This keeps the concrete
normalized coefficient isomorphism from expanding during the final kernel check.

## Proved and sorry left

Original direct holes: 1. Closed by reduction:
`AlgebraicGeometry.Etale.sfP1IntegralTransport`
(node `lem-sf-p1-integral-transport`). No direct sorry remains in the assigned
module. The geometry, witness constructions, naturality in the arbitrary supported
class, and composition of the source and trace comparisons are proved Lean code.

Added direct holes: 2, each the whole proof of a public named theorem with its
source and complete proof in words:

- `AlgebraicGeometry.Etale.SfP1Transport.sectionComparison`, node
  `lem-sf-p1-integral-section-comparison`, in
  `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison`.
- `AlgebraicGeometry.Etale.SfP1Transport.traceComparison`, node
  `lem-sf-p1-integral-trace-comparison`, in
  `Sheaf.AlgebraicGeometry.SfP1IntegralTraceComparison`.

This delivery is a decomposition, not a net hole reduction: 1 closed minus 2 added
is -1. The data module has zero holes. The remaining equations concern separate
parts of the argument and neither one restates the original existence-and-two-
composites theorem or repackages it as a hypothesis.

## No longer needed

No original import is removed, and no existing module is withdrawn. The attempted
proof import of `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` was
removed: its import closure returns to this item through smooth duality. The
push-pull comparison is constructed directly from the exact-functor comparisons
and `upperStarInvIsoLowerStarHom`, without importing any Kunneth theorem. No module is
claimed to leave the targets' import closure. The new data module imports the
component-arrow, splitting-target and invertibility modules directly; it does not
import `FiniteP1ArbitraryBaseIntegrals`. Only the trace comparison needs that
family and its base-change predicate. The source-unit comparison thus does not
carry the arbitrary-base integral theorem as an import dependency.

The assigned node no longer directly uses the four former proof dependencies as
an unspecified all-at-once comparison. Their roles are retained below the explicit
data construction and the two new comparison nodes: proper base change is used in
the data; ringed-derived coherence and normalized twist coherence remain in the
plans for the two outstanding comparison equations. No planned dependency is
claimed obsolete while those equations remain unproved. The arbitrary-base
integral module remains necessary for the splitting family, its base-change
predicate and its chart trace. Its integral-evaluation theorem is not applied here.
The source-unit lemma needs none of the twist, Kummer, splitting or trace
arguments of the old combined obligation. The trace lemma needs no supported
class or diagonal integration computation.

The blueprint unit's statement and realized steps are unchanged; this is a
factorization below that route. Every adopted source-library declaration remains
untouched.

## Where the brief, the DAG or earlier work was wrong

The delivery cycle check exposed a cycle in using the existing Kunneth helper for
push-pull along an isomorphism. The data constructor instead uses its elementary
exact-functor comparison directly, retaining the adopted source module unchanged.

The existing node's two prose steps contain canonical-comparison assertions that
its declared dependency signatures do not directly expose for these specialized
ordinary and compact-support arrows. General monoidal ringed-topos comparison
existence alone does not provide this specialized equation without additional
identification work. The prior split left the datum, class, trace, constant
comparison and naturality implicit. This packet constructs them and proves the
naturality and composition steps, leaving only their source-unit and trace
coherences separately stated.

The source and trace equations have been checked mathematically for the empty
scheme, the zero coefficient ring, the zero Ext class, and arbitrary N whenever
the original hypotheses can hold. They add no positivity, Noetherian, boundedness,
nonempty-base or nonzero-ring assumption. The source equation is independent of N.
The Ext class is arbitrary throughout the proved combination; no Kummer
normalization or identity value of its integral is assumed.

## New nodes

`def-sf-p1-integral-transport-data` records the concrete constructions and their
Cartesian geometry. Its primary attachment is `SfP1Transport.diagonalLift` and it
also lists the other definitions and proved geometric helpers of the data module.
It has zero sorry statements and makes no arbitrary data choice.

`lem-sf-p1-integral-section-comparison` isolates compatibility of the canonical
section unit with proper forget-supports and the pasted exchange squares, before
inserting any Ext representative. This replaces the source part of the old
comparison by a statement without any line, class or trace parameters.

`lem-sf-p1-integral-trace-comparison` isolates the trace clause of base-change
compatibility after chart and coordinate comparisons. Its trace is fixed by the
explicit constructor, independently of the supported class. Both remaining nodes
retain their source, proof steps and actual Mathlib search results. The parent
node now follows the Lean construction and its two comparison dependencies.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
