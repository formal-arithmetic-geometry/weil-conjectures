# finiteFieldPresentation

## Reason

Make the specified heart functor explicit, prove that its scalar-extension factor is an
equivalence, and reduce the presentation theorem to two separate heart assertions. This
records new public declarations under Sheaf; no existing declaration signature, public
import, definition body, or target statement changes.

## Old

The proof of
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteFieldPresentation`
was `by sorry`. No `finiteHeartRealization` declaration existed.

## New

`finiteHeartRealization X A` is the concrete composite
`Mod.extendScalars (finiteScalarMap X A) ⋙ integralModelIntrinsicRealization X A`.
`finiteScalarMap_isIso` and `finiteScalarExtension_isEquivalence` are proved.
The unchanged presentation theorem is proved from
`finiteHeartMonoidalPresentation` and `finiteHeartConstructibility`, both new
public named theorem obligations with source, proof in words, and DAG nodes.
The derived compatibility is proved by actual natural-isomorphism composition;
the constructibility transport uses full faithfulness and the existing intrinsic
constant-scalar constructibility theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EmbeddedFiniteFieldPresentation | G9 | Uses the three new modules through proof imports; existing signature unchanged. |
| Sheaf.Paper.EmbeddedFiniteFieldCohomologyCriterion | unmodified consumer | Its only use is the unchanged existential signature; no adaptation. |

The new public definition has no existing users. Its only users in this packet are the
two new heart statements and the proof of the item. The existing direct consumer was
located by searching both Lean roots for the module import and declaration name.

## Status

landed 20261025T162527-L-470718 2026-10-25 (merge of deliver/G9/Sheaf.Paper.EmbeddedFiniteFieldPresentation)
