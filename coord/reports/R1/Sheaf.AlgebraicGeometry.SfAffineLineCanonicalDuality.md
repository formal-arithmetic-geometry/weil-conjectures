## What changed

Proved `AlgebraicGeometry.Etale.sfAffineLineCanonicalDuality` from the stated projective trace
adjunction and the normalized etale restriction identity. The private categorical helper `tensorMap_of_trace`, instantiated by
`tensorMap_of_trace_adjunction`, identifies the actual tensor composite with the
counit-preserving right-adjoint comparison, by projection naturality and injectivity of the
adjunction Hom equivalence. The private helper `tensorMap_etale_restriction` cancels the
three invertible comparison factors in `sfExceptionalTensorEtaleRestriction`. The final
orientation pulls back the projective root line using the existing normalized exponent-one
Tate comparison, degree-zero comparison and shift comparison. All complexes remain unbounded. The formal calculation is checked over abstract categories,
and the three large comparison definitions are locally irreducible during this proof;
only the defining tensor-map formula is explicitly unfolded. This avoids repeated
unfolding without changing any public definition or attribute.
The affine-line theorem and its compactification retain their exact signatures and definitions.

Added three private proof imports: `SfAffineBaseP1TraceAdjunction`,
`SfExceptionalTensorTransitivity`, and `EtaleFiniteTwistPullback`.

Repaired the unclaimed `SfAffineBaseP1TraceAdjunction` interface to express the same
projective-line result over arbitrary affine S, in standard-chart coordinates, using the
identity/proper compactification and an explicit version of its documented unit equation.
The new abbreviation `sfProjectiveLineCompactification` uses `Compactification.ofIsProper`;
`sfTensorPullbackUnitIso` is constructed from the existing right unitor and pullback-unit
isomorphism. No data is chosen from a mere-existence hole. The geometric projective-adjunction
hole remains exactly one named public theorem. Its node records the equivalent presentation
and audits its sole DAG citer. The statement-change record uses the stage-2 schema
required by brief-stage3 section 4; this is a stage-3 delivery. No adopted source-library module is changed.

Change records: `coord/changes/R1-affine-line-projective-trace-interface.md` and
`coord/changes/R1-finite-tate-pullback-import-cycle.md`.

Replaced one overly broad private import of
`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction` from the unclaimed
`EtaleFiniteTwistPullbackBase`. Its two actually needed lemma providers, RootsOfUnityPullback
and ProjectionFormula.Unit, are now imported directly. Its entire existing complete proof,
signature and public API are unchanged. This breaks the circular path from Tate pullback
through smooth duality back to this item. No source-library module or upstream declaration is removed. The overlaid
complete source graph has zero import cycles.

## Proved and sorry left

Closed 1 of the assigned module's 1 original holes:
`AlgebraicGeometry.Etale.sfAffineLineCanonicalDuality`
(node `lem-sf-affine-line-canonical-duality`). All three private helpers are proved in full.
The assigned module has zero remaining holes. Added zero holes and split off zero theorems.

The adapted dependency retains its original hole:
`AlgebraicGeometry.Etale.sfAffineBaseP1TraceAdjunction`
(node `lem-sf-affine-base-p1-trace-adjunction`). Its projective geometric argument remains
explicit in the source docstring and node; this delivery does not count that hole as closed.
Its interface repair is mathematically equivalent, including the unit equation already
asserted by the node. The delivered three-module packet has one total remaining hole.
`AlgebraicGeometry.Scheme.etaleFiniteTwistPullback_base` is retained proved, with zero holes.

## No longer needed

Replaced the overly broad private RegularImmersionReduction import from
EtaleFiniteTwistPullbackBase, as described above. No module or planned geometric dependency
node is withdrawn. The assigned theorem itself removes no imports. The proof retains the
unit's projective-line adjunction followed by affine-open restriction. The etale unit theorem
is used through the normalized restriction comparison, and uniqueness of right adjoints is
used for the actual counit comparison. Choosing the projective adjoint to be the trace
adjoint itself avoids an unnecessary second choice without dropping any geometric input.
The initial leanfinder, loogle and Mathlib grep searches found no shorter geometric result.

## Where the brief, the DAG or earlier work was wrong

The trace dependency's old Lean presentation could not be applied directly to the stated
arbitrary-affine-base, standard-chart item: it used Spec R and ULift (Fin 2), and hid the
coefficient-unit normalization needed by the counit comparison. The repair changes the
presentation, not the geometric content. An affine scheme is canonically Spec of its global
sections; the two index sets both have two elements; invertibility is local on stalks; and
the identity/proper compactification represents the proper pushforward with its canonical
projection map. The existing trace node already asserted its unit specialization. Its one
DAG citer, `lem-sf-affine-line-canonical-duality`, continues to hold unchanged.

`tools/downstream.py` reported zero existing importers of the trace module and only its
own declaration as a use. No group held that module or node in the current claim records.
The old base-package proof import introduced a circular dependency when the stated trace
and Tate-pullback modules were imported here. The broad private import has been replaced by its two actual lemma providers,
with no change to its already complete proof. There are no forced adaptations or new nodes.
The empty scheme, zero coefficient ring and N=1 are covered by the same functorial formulas; no nontriviality assumption is used.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
