## What changed

Proved `WeilConjectures.IntegralSystemRealization.integralOpenReductionIso` in
`Sheaf.SixFunctors.IntegralOpenReductionIso`, preserving its signature and public import.
Added proof imports of `Sheaf.SixFunctors.OpenReductionMateLocalization` and
`import all Sheaf.Paper.IntegralOperationsWellDefined`. The latter exposes the existing
proved private good-complex localization helper; no existing module is changed.

The proof chooses a good K-flat representative by essential surjectivity, proves the
ordinary complex mate invertible degreewise, and cancels the comparison isomorphisms
in `openReduction_mate_localization`. Naturality transports the result to the input.
The DAG proof and proof dependencies now record these exact ingredients.

Validation: server `lcompile.py` compiled the delivered module cleanly in 5.2 seconds
(exit code 0), within the 60-second per-file limit.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralSystemRealization.integralOpenReductionIso`
(node `lem-sf-integral-open-reduction-iso`).

Holes added: zero. Sorries left in the delivered Lean module: zero.
No new lemmas or split-off obligations.

## No longer needed

No existing imports were removed and no modules are withdrawn.
`lem-sf-integral-open-reduction-comparison`
(`Sheaf.SixFunctors.IntegralOpenReductionComparison`) is unnecessary as a proof
input here: the ordinary invertibility theorem and the whole-system localization
formula give the result directly. Its existing statement dependency is preserved.
No global pruning of that module or its dependencies is claimed.

The larger module `Sheaf.SixFunctors.OpenReconstructionEffectivity` is not imported:
its already proved private `fixedOpenReduction_isIso` supplies an existing Lean
assembly of exactly this argument, which is reused here with only the lower imports
that its proof requires. Completeness and constructibility theory from the larger
module is not needed for this result.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof named `openReduction_mate_localization` but its dependency
list did not cite the node containing that theorem. It instead cited the broader
integral open-reduction comparison. The corrected proof dependencies name the
localization formula, ordinary mate invertibility, and the good-representative
localization. All of these ingredients are already proved; another split is unnecessary.

The statement holds for arbitrary derived objects and arbitrary open immersions,
including the empty and identity opens. The proof adds no completeness,
constructibility, quasi-compactness, or characteristic assumptions and preserves
the unit route.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
