## What changed

Withdraw the assigned fixed-datum module and the unclaimed
Sheaf.SixFunctors.FiniteTorOrdinaryPullCompleteOfComplete. The latter was the only
mathematical parent of the former; the only consumer of the latter is
Sheaf.SixFunctors.FiniteTorOrdinaryPullComplete. Replace that parent's proof without
changing its signature or public imports. All three node records follow the new route;
the two withdrawn nodes remain in the DAG with null Lean attachments.

The parent now actually uses the finite-Tor hypothesis: its existing affine-chart
lemma, applied to K and K and projected to one input, gives explicit source models.
A new geometric model-transport theorem pulls those charts back. The existing
boundedProjectiveComplex_complete proves every model complete. Naturality of the
specified completion unit and cancellation of the model isomorphism transport this
completeness. The existing affineTreeCompleteDetection descends it to X.

The new theorem concerns transport of supplied bounded finite-free-retract charts,
with explicit models and splitting maps. Neither its hypothesis nor its conclusion
is a completeness predicate. This is the geometric step before completeness and
descent, not another rephrasing of the assigned statement. The coefficient-unit
alternative has the rank-one regular-module construction in its proof plan.

Change record: coord/changes/H8-ordinary-pullback-projective-route.md.
No retained declaration signature, target, definition, instance or public import changes.

Validation: lcompile accepted the new chart module and replacement parent, then
both unchanged direct importers, PrimitiveCompletionEffectivity and
RationalSmoothPurityCanonical. The latter first exceeded the time limit; profiling
was used, all diagnostic options were removed, and its final clean check passed.
Separate published/overlay probes found identical registrations for the six relevant
site/derived-category instances and the same structural hash of the retained theorem's
type (767152257). The unchanged consumer copies and diagnostic probe are not delivered.
No forced consumer adaptation was needed.

## Proved and sorry left

Assigned module: one original hole, zero holes proved and zero holes left there,
because its unsupported statement is withdrawn. This is a repair and pruning, not
a proof of the old over-general statement.

Withdrawn original hole:
WeilConjectures.GeneratorReduction.finiteTorOrdinaryPullComplete_fixed_datum
(node lem-sf-finite-tor-ordinary-pull-complete-fixed-datum).
The withdrawn finiteTorOrdinaryPullComplete_of_complete was already proved from that
hole; it is not counted as another closed hole.

The retained WeilConjectures.GeneratorReduction.finiteTorOrdinaryPullComplete has a
complete Lean proof from the named dependencies, with its original statement intact.
It contains no sorry. This is a decomposition of the original route, not a net
closed hole: one original unsupported hole is removed and one genuine model-transport
hole is added.

The only new sorry is
WeilConjectures.GeneratorReduction.finiteTorPullbackAffineProjectiveCharts
(node lem-sf-finite-tor-pullback-affine-projective-charts), in
Sheaf.SixFunctors.FiniteTorPullbackAffineProjectiveCharts. Its proof is exactly
`by sorry`, with a full construction plan and edge cases in the docstring and node.
Existing imported theorem holes are not duplicated or changed.

## No longer needed

Withdrawn modules and nullified Lean attachments:
Sheaf.SixFunctors.FiniteTorOrdinaryPullCompleteFixedDatum
(lem-sf-finite-tor-ordinary-pull-complete-fixed-datum) and
Sheaf.SixFunctors.FiniteTorOrdinaryPullCompleteOfComplete
(lem-sf-finite-tor-ordinary-pull-complete-of-complete).
Their only parent dependencies were checked in stmt_deps, proof_deps and proof-step
uses and are removed together; withdrawal does not rely on zero Lean importers.

Removed private imports from the retained parent:
Sheaf.SixFunctors.FiniteTorOrdinaryPullCompleteOfComplete,
Sheaf.SixFunctors.FiniteTorOrdinaryPullCompleteTensorUnit, and
Sheaf.Paper.SfDerivedCompleteLegacyComparison.
The separate tensor-unit completeness node is no longer used by this proof, since
rank-one models are treated by the same bounded-projective argument after transport.
Its source module is not removed, nor are any declarations in WeilConjectures.
No unit statement or realized unit step is bypassed (the unit's realized lists are empty).

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the assigned node and its unrestricted parent generalize from
finite-projective constructible models to arbitrary complete complexes while assuming
that exact inverse image and scalar extension transport infinite products and Roos
triangles. This is not implied by exactness or by the cited sources. A model on a
bounded finite-projective complex is not supplied by arbitrary source completeness.

Read Bhatt--Scholze Section 6.5, especially Remark 6.5.10: ordinary pullback agrees
with completed pullback for the specified compositions of qcqs weakly etale maps and
constructible closed immersions. Stacks Tag 099N(5), proetale.tex,
lemma-pushforward-Noetherian-case, explicitly describes COMPLETED pullback, not
ordinary pullback. We do not claim a formal counterexample in this encoding; the
unsupported universal route is removed, and the required parent is preserved using
its genuine finite-Tor projective-model hypotheses.

The node's only stated dependencies were definitions, so they could not supply the
asserted product preservation. The replacement uses the already available chart,
bounded-projective completeness, and affine-tree detection statements instead.

## New nodes

lem-sf-finite-tor-pullback-affine-projective-charts: a geometric transport lemma for
supplied explicit source projective charts. The source is the finite-projective
argument of Bhatt--Scholze Lemmas 6.5.5--6.5.8 and Stacks 0G7E/09C3. Its source and
target chart descriptions include bounded complexes, actual retractions into finite
free sheaves, all leaf-cover maps, and the ordinary derived model isomorphisms. It
imposes no completeness predicate. Rank zero, empty schemes and empty leaves are
included, and the tensor unit uses the degree-zero rank-one model. Actual LeanSearch,
LeanFinder, Loogle and grep queries, and blueprint phrase searches, found no existing
chart-transport theorem. Existing nodes only construct source charts or handle
K-flat module pullback. The new node does not depend on either withdrawn statement.

Change record: coord/changes/H8-ordinary-pullback-projective-route.md.

The new node uses the existing ringed K-flat pullback theorem and native K-flat
unit comparison as foundational tools from other units. They supply only model
transport and the identity of the coefficient unit; no unit-level route is bypassed.
Any cross-unit tool approval remains the maintainer's field; this packet adds no
entries to tool_uses.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
