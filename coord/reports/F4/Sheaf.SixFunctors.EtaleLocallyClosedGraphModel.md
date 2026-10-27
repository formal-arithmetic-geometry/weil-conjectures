## What changed

Proved `AlgebraicGeometry.Etale.etaleLocallyClosedGraphModel` without changing any signature,
definition, or existing comparison. The projection equations identify the composites of the
first two graph maps with the identity and with `a`. Their projection targets are separated
by proper base change, so Mathlib's `IsProper.of_comp` proves both graphs proper. The same
lemma proves the intersection graph proper, since its first projection is an open immersion
and its composite is the first graph. The record uses the existing explicit
`locallyClosedGraphIso` and reflexivity for its specified normalization.

Updated the node's proof, proof dependencies and proof origin to this argument. Removed four
unused public imports. There are no current direct Lean importers of this module; its DAG
parent `lem-sf-etale-compact-projection-coherence` continues to use exactly the same statement
and specified comparisons. No unit statement or unit proof step changes.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.etaleLocallyClosedGraphModel`
(node `lem-sf-etale-locally-closed-graph-model`). Zero holes left in the item; zero holes added;
zero statements split off. This is a proof, not a decomposition. The explicit isomorphism
uses existing upstream comparison APIs; their transitive dependencies are unchanged.

## No longer needed

Removed the following direct imports:

- `Sheaf.AlgebraicGeometry.EtaleProperOpenTensorSquare`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`

The theorem assembles already constructed comparisons, rather than using these generic
assertions again. Removed the corresponding proof-dependency edges to
`lem-sf-etale-proper-open-tensor-square`, `lem-cbc-extension-zero-composition`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, and
`lem-sfb-ringed-derived-monoidal-comparisons`. Also removed proof-dependency edges to
`lem-weil-pbc-extension-by-zero-exact` and `def-weil-pbc-extension-by-zero`: their published
upstream APIs are already incorporated in the existing explicit definitions. Withdrew the
five generic `tool_uses` entries for these unused assertions. Statement dependencies stay:
they describe the normalization of the comparisons, and this delivery changes no statement.
None of these nodes or modules is withdrawn or claimed globally unnecessary; the adopted
upstream APIs and other parents may still need them. No declarations are removed.

## Where the brief, the DAG or earlier work was wrong

The longer Cartesian-square/base-change proof for the intersection graph is unnecessary:
properness of its composite with the separated open projection suffices. The four generic
Sheaf imports were unnecessary for both the explicit constructions and the theorem proof.
The stated theorem and its edge cases are unchanged; the argument permits empty schemes,
identity opens, arbitrary opens, and arbitrary schemes, without additional hypotheses.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
