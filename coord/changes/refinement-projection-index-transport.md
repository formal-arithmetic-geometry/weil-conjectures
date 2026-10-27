# Refinement projection: canonical transport and shared native instance data

## Reason

The assigned module `Sheaf.SixFunctors.RefinementProjectionCounit` (T3), realizing
`lem-sf-refinement-projection-counit`, must combine the local mate equation with proper
projection composition. Whole-functor equality transport and concrete coefficient-ring
instance comparisons made this proof exceed the compile limit. The changes below
preserve the maps and the mathematical statement. No target or source-library declaration
is changed.

## Old

`RefinementProjection.finiteComparison` ended with
`eqToIso (congrArg (ProperOpenPush A) r.hom_g)`. The theorem wrote its two finite projection
maps directly as `projectionMapOfCompactification (ModuleCat (ULift ...)) c`.
The kernel compared native `ULift.ring` against the ring parent of `ULift.commRing`
through the complete derived-functor constructions and timed out.

## New

The final comparison transport is `indexIso (ProperOpenPush A) r.hom_g`. This is equality
elimination on the original morphism index, with identity as its reflexive case. The
proved theorem `eqToIso_congrArg_indexIso` identifies it with the original equality
isomorphism. Thus it changes no map.

The public theorem displays its two native finite projection maps through the real
construction `RefinementProjection.finiteProjection`, defined exactly as
`projectionMapOfCompactification (ModuleCat A) c` at generic coefficients. It introduces
no hypothesis, alternate map, choice or hole. Its generic elaboration shares all the
categorical instance data before specializing to the lifted coefficient quotient.
The original binders, universes, visibility and attributes are preserved. The result
types are definitionally equal. The independent reader can unfold `finiteProjection`
to compare the native formulas. The combining theorem then checks by direct application;
the complete development module compiled in 25.1 seconds.

The new factor-interface node `def-sf-refinement-projection-words` is a proof dependency.
The original node's mathematical statement and statement dependencies stay as on the base.
The Lean record and proof dependencies follow the implementation.

## Users

`Sheaf.SixFunctors.RefinementProjectionCounit` (held by T3) is adapted here. Current
`rg` searches of `lean/Sheaf` and `lean/WeilConjectures` find no other importer of this
module and no external use of `finiteComparison` or `refinementProjectionCounit`.
No downstream Lean module requires adaptation. Abstract DAG parents remain attached;
no mathematical dependency or source-library declaration is withdrawn.

## Status

landed 20261026T071105-L-3824606 2026-10-26 (merge of deliver/T3/Sheaf.SixFunctors.RefinementProjectionCounit)
consumer check, explicit factor equations and combining proof.
