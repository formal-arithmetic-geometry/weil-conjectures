## What changed

Filled `AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective` in
`WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic` without changing any
existing signature, attribute, public import or visibility, or definition body. Added the
proved private helper `affine_etale_sections_vanishing` and two private proof imports:
`Sheaf.AlgebraicGeometry.AffineComparisonInjectiveDerivedVanishing` and
`WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar`. Both imports are used.

The helper applies the existing affine vanishing theorem to the etale restriction of I.
Etale restriction preserves injectives. The canonical comparison pullback square and
pro-etale localization identify its positive derived sections with derived evaluation
at the affine etale object. The main proof computes comparison direct images using an
injective resolution, tests its exactness on the affine etale basis, proves presheaf
exactness by evaluation, and sheafifies. Faithful exact basis restriction reflects the
result. This follows Stacks `proetale.tex`, Tags 099U and 099V,
`lemma-affine-vanishing` and the first paragraph of `lemma-relative-comparison`.
No quasi-compactness, affineness of X, or coefficient-ring hypothesis was added.

Updated the proof records of the three nodes attached to this same theorem:
`lem-weil-pbc-comparison-grothendieck-injective-acyclicity`,
`lem-cbc-abelian-comparison-injective-acyclicity`, and
`lem-pe-comparison-injective-left-modules-acyclic`. The first two already planned
this affine-basis proof. The third now records the same generic coefficient proof,
specialized to arbitrary left modules, rather than going through abelian cohomology.
Their statements and Lean attachments are preserved. No unit statement or step changes.

Validation: on the current resumed attempt the entire item compiled remotely with
lcompile.py, exit 0, in 7.0 seconds, with no compiler errors or warnings. The required
deliver3.py invocation passed remote preflight and pushed commit 47b29763b6b; this report
update records the successful validation. The empty scheme is covered by the same affine
vanishing theorem; arbitrary objects and q = 0 (derived degree 1) use identical arguments.
The method never assumes that sections of a higher direct image equal derived sections.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`.
The private helper `AlgebraicGeometry.ProEtale.affine_etale_sections_vanishing` is proved.
There are zero textual sorries left in the item and zero holes added elsewhere; zero
statements are split off. This is a proof from already declared dependencies, including
`AlgebraicGeometry.ProEtale.isZero_rightDerived_globalSections_comparisonUpperStar_of_isAffine`
(node `stage3-affine-comparison-injective-derived-vanishing`). It does not claim to close
all transitive obligations of that existing theorem.

## No longer needed

No existing imports or library declarations were removed. No module is withdrawn or
claimed to be globally unreachable. All source-library public imports remain verbatim.

For `lem-pe-comparison-injective-left-modules-acyclic`, the new proof does not use the
following formerly declared dependencies:

- `lem-weil-pbc-ring-sheaves-grothendieck` /
  `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`: the theorem is proved
  directly for the supplied Grothendieck abelian coefficient category, so no ringed-site
  model or comparison of encodings is needed.
- `def-weil-sheaf-of-modules-category` /
  `Sheaf.CategoryTheory.RingedSiteModules`: no ringed-site module conversion is used.
- `lem-weil-pbc-derived-functor-injective-vanishing`: no separate passage to etale
  cohomology is used; affine comparison vanishing is applied directly to the injective.
- `lem-pe-ringed-site-derived-evaluation-slice` /
  `Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice`: localization and derived
  composition are used directly in the original generic coefficient category.
- `lem-pe-comparison-etale-slice-abelian-pullback` /
  `Sheaf.AlgebraicGeometry.ComparisonEtaleSliceAbelianPullback`: the generic source-library
  commutation isomorphism supplies the needed square, with no abelian specialization.
- `lem-cbc-abelian-etale-proetale-cohomology-comparison` /
  `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`: unnecessary and would
  be circular at the Lean level, since its proof imports this item.
- `lem-pe-left-module-comparison-vanishing-criterion` /
  `Sheaf.AlgebraicGeometry.LeftModuleComparisonVanishingCriterion`: the item implements
  an affine-basis criterion directly for general A; the old criterion instead requires
  vanishing at every etale object after forgetting scalars.

Removed obsolete top-level tool-use approvals from that node for
`lem-weil-pbc-ring-sheaves-grothendieck`, `lem-weil-pbc-comparison-pullback`,
`lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`,
`lem-weil-pbc-cohomology-over-object-localization`,
`lem-weil-pbc-etale-site-localization-open`,
`lem-cbc-abelian-etale-proetale-cohomology-comparison`, and
`lem-weil-pbc-derived-functor-injective-vanishing`.
From `lem-cbc-abelian-comparison-injective-acyclicity`, removed obsolete approvals for
`lem-sbc-etale-abelian-restriction-injectives`,
`lem-weil-pbc-cohomology-over-object-localization`,
`lem-weil-pbc-sets-etale-inverse-image-composition-units`,
`lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`, and
`lem-weil-proetale-weakly-etale-localization`. The proof uses the existing generic
localization API, the resolution isomorphisms, and exact sheafification directly.
The other declarations in this module, and their own dependencies, are retained.

## Where the brief, the DAG or earlier work was wrong

The generic and abelian node proof plans fit the current theorem. The arbitrary-left-module
node's plan unnecessarily passed through abelian cohomology comparison, whose actual
Lean module imports this item. Using that module here would create an import cycle.
The affine generic argument already provided by the other two records proves the same
source theorem and its arbitrary-ring specialization, so that detour is omitted.

Earlier delivery attempts were blocked by a checker conflict: unchanged upstream public
import line 14 has 102 characters, but the source-library boundary requires preserving it
verbatim. On this continuation the required deliver3.py invocation passed preflight with
that same import unchanged. No checker, launcher script, or upstream contract was altered
or bypassed by this worker.

The recovered proof at
coord/preferred-upstream/WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic.lean
was checked against the current source. It uses localization helpers declared later in
the file; the retained proved private helper implements that calculation before the
theorem without moving existing declarations. To preserve the restored proof in future
upstream syncs, the maintainer needs a row in coord/upstream-statement-exceptions.tsv
recording its private helper and the Sheaf.AlgebraicGeometry.AffineComparisonInjectiveDerivedVanishing
proof import. The worker has not changed that maintainer-owned table.

Current-source comparison confirms byte-identical public imports, one existing hole
closed, zero remaining sorry tokens, and no other overlength line. The retained DAG copies
change only proof, proof_deps, proof_origin, and obsolete tool_uses removals. The current B9
return is empty and there is no rework row. No new nodes, interface changes, forced
adaptations, or change records are needed. The recovered proof and current affine-vanishing
declaration were checked again. The first delivery of this continuation passed preflight;
this report update replaces the retained attempt's stale blocker diagnosis.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
