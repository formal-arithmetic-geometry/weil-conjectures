## What changed

Proved ten existing theorems in `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`.
The representable scheme construction now has its actual diagonal and identity-atlas
proof. Scheme-object and composite chartwise etaleness follow directly from composition.
Base-change stability pulls an atlas back and applies the already proved source-cover
detection theorem; its pullback cancellation argument is reused from the proved
`chart_base` argument in `ChartwiseEtalePermanence`, avoiding a cyclic import.
The overlap is obtained directly from the atlas scheme test, then reflected into the
enlarged site. The atlas equalizer uses the singleton-cover sheaf condition, with field
lifts constructed using the residue field of a point of the surjective scheme test.
Its displayed function is exactly restriction followed by the given normalization.
Extension existence uses the restriction equivalence counit; normalized uniqueness
uses its full faithfulness. The small geometric morphism composes the enlarged
adjunction with the two comparison adjunctions. Postcomposition continuity follows
from the already stated localization equivalence and its covering-sieve comparison,
then continuity of the slice forgetful functor.

All existing signatures, non-theorem bodies and public imports are unchanged.
Only this existing Lean module is changed. Five proof imports replace ten redundant proof
imports. The aggregate node's proof records the implementation reductions, retaining
its original four comparison assembly steps and the unit route.

## Proved and sorry left

Closed 10 of the original 21 holes, with zero holes added and zero split-off statements.
In namespace `AlgebraicGeometry.AlgebraicSpace`, the closed declarations are:

- `schemeSheaf_isAlgebraicSpace`
- `schemeObject_chartwise`
- `enlargedExtension_unique`
- `enlargedExtension_equalizer`
- `enlargedFibreProduct_chartwise`
- `enlargedEtale_comp`
- `enlargedPostcompose_continuous`
- `enlargedChartOverlap_exists`
- `enlargedSmallDirectImage_geometric`
- `enlargedExtension_exists`

The 11 unchanged holes, all attached by their existing docstrings and the aggregate
node `lem-trf-space-enlarged-etale-ringed-site-model`, are:

- `enlargedEtale_site`
- `enlargedSchemeInclusion_continuous`
- `enlargedRestriction_equivalence`
- `enlargedModuleRestriction_equivalence`
- `enlargedBaseChange_continuous`
- `enlargedDirectImage_geometric`
- `enlargedStructuralMap_existsUnique`
- `enlargedBaseChange_composition`
- `enlargedBaseChange_identity`
- `enlargedLocalization_equivalence`
- `enlargedEtale_localization`

These are proofs from the existing library declarations, as required by stage 3;
closing an implementation hole does not claim that all imported theorem dependencies
are free of `sorry`. In particular the extension results use the remaining restriction
equivalence and geometric transport uses the remaining enlarged geometric-morphism theorem.
No statement is weakened or replaced. The final `lcompile.py` check passed without
errors or warnings in 17.3 seconds. `deliver3.py` performs the delivery compile and
axiom/preflight checks.

## No longer needed

Removed these redundant proof-only imports. The algebraic-space, ringed-module and
covering-axiom foundations are already supplied by the retained public imports; the other
removed imports supplied planned arguments not used by the actual proofs:

- `Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation`
- `Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence`
- `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `Sheaf.CategoryTheory.RingedToposMorphism`
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`

No public imports or declarations are removed. No module or DAG node is withdrawn.
The four original comparison packets remain needed for the outstanding claims and are
retained in the aggregate route. For the proved implementation clauses there is no need
to import `EnlargedSiteSchemeDensity`, `EnlargedAtlasAlgebraicExtension`,
`EnlargedChartRingedMorphism`, `EnlargedRingedCompositionLocalization`, or
`ChartwiseEtalePermanence`; they already import this construction module, directly or
transitively. The overlap proof does not use `etale_fibreProduct_isScheme`: the scheme-test
witness already supplies the desired scheme and its projections. The equalizer proof
does not use the site-axiom or restriction-equivalence holes: generated-cover membership
and the given sheaf suffice.

## Where the brief, the DAG or earlier work was wrong

The exact-module DAG lookup finds the definition-ownership nodes, but the theorem
ownership is in the declarations list of the aggregate node whose headline `lean.module`
now points to `Sheaf.AlgebraicGeometry.SchemeEtaleCotangentRingMap`. Its published
attachment is preserved; its proof is updated at
`dag/nodes/sec-trace-formula/lem-trf-space-enlarged-etale-ringed-site-model.json`.
The suggested comparison packets cannot be imported into this item because they
import it. Their existing proof ingredients nevertheless give the independent atlas
argument used here. No process workaround or source-tree change was needed.

Edge cases were checked against the definitions: the identity atlas works for the
empty scheme; the singleton-cover field lifting argument is vacuous with no target
field-valued sections; residue fields stay in the test universe; and no nonempty,
representability or separatedness hypothesis was added. The overlap construction does
not require the chart's surjectivity, although that existing hypothesis is retained.
The unit statement and its fixed route are untouched. No new nodes or change records.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
