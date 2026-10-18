## What changed

Proved `AlgebraicGeometry.ProEtale.proEtaleClassical_zariskiLocal` with its original
signature. The forward implication applies the existing stronger set-sheaf descent
theorem `Scheme.proEtale_locallyClassical_etaleCover`, using
`Scheme.proEtaleClassicalSheavesImage` to switch between continuity-map classicality
and the essential-image formulation. The module predicate already uses the underlying
set sheaf, so no linear descent construction is needed.

The cover is reindexed by `Set.range U`, lifted into the site's object universe;
this preserves the arbitrary universe `w` in the original theorem. Over every site
object T, its inverse-image opens cover T, and the existing open-immersion covering
criterion verifies `CoversTop`. Repeated and empty opens, empty schemes and empty
covers cause no exception. Coefficients need no finiteness or nonzero-ring assumption.

The private, proved helper `setClassical_restrict` composes an affine presentation
over an open with its inclusion in X. The site objects, section diagram and canonical
continuity map agree definitionally. Connected-limit preservation and reflection of
the over-category forgetful functors supply the limit assertion. No comparison
pullback coherence or new statement is required for this implication.

Updated the node's proof, proof dependencies and proof origin to this shorter route,
and withdrew its five obsolete tool-use approvals. The unit statement and route are
unchanged: this item still supplies exactly Zariski locality for constructible
comparison. The unit record has no realized substeps forcing the former linear gluing
argument. The imported set-sheaf descent theorem has its own existing node and proof.

The public dependency is narrowed to the module that defines classicality. The change
record is `coord/changes/E5-classical-zariski-local-import-pruning.md`. The downstream
script reports zero users; no consumer adaptation is necessary.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.proEtaleClassical_zariskiLocal`
(node `det-pe-constructible-comparison-local`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The final single-file remote compile passed without warnings in 4.6 seconds.
The private helper `setClassical_restrict` is also proved. This is a proof from existing
declarations, not a claim that all imported dependencies are axiom-free:
`Scheme.proEtaleClassicalSheavesImage` remains an existing dependency with `sorry`.

## No longer needed

Removed the public import `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`,
replacing it with `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`, which is the actual
statement dependency. The proof does not use `det-pe-classical-sheaves-modules`.

Removed these proof imports and their corresponding planned proof dependencies:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
  (`lem-weil-pbc-etale-site-localization-open`): no slice equivalence is needed.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
  (`lem-weil-proetale-weakly-etale-localization`): sectionwise restriction is used
  directly, without coefficient-ring or module-category transport.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
  (`def-weil-pbc-site-comparison-morphism`): no direct use in the proof; needed
  comparison constructions are supplied by the essential-image dependency.
- `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`
  (`lem-weil-pbc-sheafification-plus-theorem`): no double-plus calculation is used.
- `Sheaf.CategoryTheory.SiteModuleSheafGluing`
  (`lem-weil-pbc-site-module-sheaf-gluing`): stronger existing set descent replaces
  local module-model gluing.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`
  (`lem-pur-sheaf-hom-cover-gluing`): no linear comparison maps or inverses are glued.

The five obsolete top-level tool-use entries are removed from the node. These are
local dependency removals; other target branches may still need those modules.

## Where the brief, the DAG or earlier work was wrong

The planned four-step module-gluing proof is mathematically valid but unnecessary
for the actual signature, which defines module classicality using its underlying set
sheaf. Bhatt--Scholze Lemma 5.1.4 is already stated, with a completed proof from its
existing dependencies, as `proEtale_locallyClassical_etaleCover`. Its use avoids
reconstructing the linear descent theory. Lemmas 5.1.2 and 5.1.4 were checked in the
local Bhatt--Scholze PDF, and the blueprint statement and proof were read.

`AffinePresentation.isLimit` is a limit in `Over X`, rather than a limit asserted
literally in Scheme. The restriction proof accounts for this using preservation and
reflection by `Over.forget`; merely reusing `P.isLimit` is not type-correct.

Short-route searches: leanfinder query "classical pro etale sheaf restriction to open
subscheme and descent along open covering" returned eight unrelated scheme/open/gluing
hits; Loogle query `"sheafPullback", "comp"` returned zero hits; msearch grep query
`classicalRestrictionIso|IsProEtaleLocallyClassical|openImmersionRestriction` returned
zero Mathlib hits. Repository `rg` searches found the reusable local-classicality
module. No new theorem or node was needed.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
