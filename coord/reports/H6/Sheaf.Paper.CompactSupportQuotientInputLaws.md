## What changed

Proved `WeilConjectures.compactSupportQuotient_input_laws` in the assigned module,
with its statement unchanged. The proof first checks the prescribed restriction
comparisons on underlying sections, then uses exact derived localization and the
adjunction Hom bijections. All additional declarations are private and proved.

Added proof-only imports of `MapDerivedCategoryCocycle`,
`ExactRestrictionComposition`, and `ExactRestrictionDerivedIdentityUnit`, plus
a proof-only `import all` of `ProEtaleOpenScalarRestrictionCoherence` to reuse its
already-proved private section formulas `coefficient_id_apply` and
`restriction_comp_apply`.
Updated the item's DAG proof, proof dependencies and proof origin to this route.
No other existing Lean module or node is changed, and no public interface is changed.

Search: LeanFinder for composition of transposed adjunction units returned general
adjunction restriction and presheaf-unit lemmas, with no specialized quotient law.
Loogle located `Adjunction.homEquiv_naturality_right`, which the proof uses.
The launcher grep search for the exact-derived APIs returned no indexed hits;
local `rg` found the adopted source's `mapDerivedCategoryCompNatIso_cocycle`,
`mapDerivedCategoryNatIso_isoWhiskerRight`, and exact-derived unit laws. Local
search also found the parallel `IntegralReductionTransitionCocycles` proof,
but its public theorem concerns another coefficient presentation and its
restriction-coherence theorem is still a hole. This delivery proves the needed
coherence directly rather than importing that obligation.

## Proved and sorry left

Closed the one existing hole in
`WeilConjectures.compactSupportQuotient_input_laws`
(node `lem-coef-compact-support-quotient-input-laws`).
Holes closed: 1. Holes added: 0. Sorries left in the delivered module: 0.
No statements are split off.

## No longer needed

No original imports are removed: both public imports expose the original statement
and its prescribed coefficient comparisons. The following planned proof dependencies
are unnecessary for this item's proof and are removed from its `proof_deps`:

- `lem-pc-kflat-resolution`
  (`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`): the argument
  uses the defining adjuncts directly on arbitrary derived objects.
- `lem-coef-compact-support-quotient-model-maps`
  (`Sheaf.Paper.CompactSupportQuotientCocycleRepresentativesData`): no quotient or
  balancing chain maps are chosen.
- `lem-coef-compact-support-quotient-computation-squares`
  (`Sheaf.Paper.CompactSupportQuotientComputationSquares`): no representative
  computation squares are needed.
- `def-pc-sheaf-restrict-scalars` and `def-pur-sheaf-tensor-product`
  (`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` and
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`): these notions
  remain part of the existing definitions but their planned tensor-level proof
  is not used or separately imported here.

These nodes and modules may still be needed by other items. This delivery withdraws
none of them and makes no claim that they leave the entire targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The original plan was stronger than necessary: the quotient arrows were already
defined as inverse transposes of units. Their identity and composition follow
formally once the specified restriction comparisons are coherent. The remaining
coherence is proved from the existing sectionwise normalizations and exact
localization API. Direct substitution in a coefficient-cast section formula
triggered expensive kernel conversion. A private, proved equality-induction
helper keeps that motive fixed. The identity comparison is written explicitly:
a private wrapper around its large realization isomorphism also caused expensive
kernel unfolding. A generic section-composition lemma combines the cast formula
with the existing `coefficient_id_apply` formula. The other private coherence
helpers use abstract ring sheaves before specializing them. No shared definition
is changed. No statement defect or unit-route change was found.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportQuotientInputLaws": "7ba14777fa5d04f56d45bc32f9978f1805bfad51"}, "results": {"Sheaf.Paper.CompactSupportQuotientCocycle": {"hash": "d968efa467527c3363d5eea4cc1e0a1110430787", "status": "OK"}}, "seconds": 39, "time": "2026-10-28T01:22:02+0800", "transitive": 0, "version": 1}
```

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
