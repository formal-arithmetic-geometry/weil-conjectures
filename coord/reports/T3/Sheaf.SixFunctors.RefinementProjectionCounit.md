## What changed

`refinementProjectionCounit` is reduced to the local normalized proper/open tensor
equation and the proper projection/compositor equation. The combination is a proved
categorical pasting argument, using first-variable naturality of proper projection.
The new factor-interface module records the actual finite and simultaneous-system
maps, including identity and equality transports. It records the native projection
components with their proved component equations, so the main proof uses those equations
without repeatedly rewriting through the derived-functor constructions.
The original binders and mathematical statements are preserved. The finite comparison
uses the proved canonical index transport. The theorem's two native finite projection
maps are expressed through `finiteProjection`, the identical native construction
elaborated generically before specializing the coefficient ring. This shares its
categorical instance data and avoids the costly ring-instance diamond. Both presentation
changes and the consumer check are documented in
`coord/changes/refinement-projection-index-transport.md`. The finite
combining proof now applies directly.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.AmbientProperOpen.refinementProjectionCounit`
(node `lem-sf-refinement-projection-counit`) is replaced by a combining proof from the two explicit factor equations.
One strictly smaller hole is added:

- `AlgebraicGeometry.ProEtale.AmbientProperOpen.RefinementProjection.refinementProjectionLocalTensor`
  (`lem-sf-refinement-projection-local-tensor`).

`refinementProjectionProperComposition` is proved from the general adjunction projection
composition and conjugation formulas, using the existing ambient tensor-composition
coherence. All generic categorical helpers and the pasting lemma are proved without holes.

This is a decomposition: one original hole replaced, one added. It is not a net
reduction of the number of holes. The remaining local
equation retains both coefficient settings and arbitrary unbounded inputs. It has no
outer pushforward and does not restate the final result.

## No longer needed

Removed the original direct private imports of `ProperOpenProjectionMate` and
`RingedProjectionTensorComposition` from the main module: the combining proof uses the new local and composition statements.
Their proofs still need the original proper/open mate, ambient pasting and ringed projection identities;
no original mathematical dependency is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original plan suppressed nontrivial identity and equality transports. Its system
unit laws are supplied for the canonical presentation, whereas the statement quantifies
over arbitrary realized compositors; the remaining local proof must normalize those
using the recorded section and localization certificates. No evaluation faithfulness
is available or used. Several development compiles exceeded 60 seconds while unfolding
identity tensor comparisons; those experiments are outside the delivered Lean modules.
Server storage and published-build failures occurred during development. Several imports initially failed because published upstream object files were
missing; later checks reached the proofs. The required delivery compiler log is the
validation of the complete packet. Development also isolated a costly whole-functor
equality cast in `Compositors.square`; a future proof of the retained local lemma
should use a component API or repair that transport while preserving its map.

## New nodes

`def-sf-refinement-projection-words` records the explicit factors and the two local
equation predicates. It retains the actual first-variable tensor action in each
coefficient setting and its proved composition law.

`lem-sf-refinement-projection-local-tensor` is the identity-side proper/open tensor
calculation with compactification pullback transport. This is the remaining hole.

`lem-sf-refinement-projection-proper-composition` is the proper projection/compositor
identity, proved using the general adjunction projection formulas and ambient tensor
composition. The refinement equality is transported at the abstract categorical level.

All serve the composition/refinement sentence of `fix-prop-projection-formula`.
No target or source-library declaration is changed. Original result types are
definitionally equal; the native finite projection maps are displayed through the
transparent construction `finiteProjection`. The mathematical statement and its
statement dependencies are unchanged; the new words interface is a proof dependency.
The finite comparison transport is extensionally unchanged by
`eqToIso_congrArg_indexIso`; see the change record.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
