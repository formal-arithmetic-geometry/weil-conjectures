## What changed

Reviewed and repaired `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`.
The original second-reading candidate only restated sheaf vanishing sectionwise. Replaced that
candidate with an explicit resolution proof: restrict the derived direct-image complex to the
faithful exact affine étale basis, prove section-complex exactness using localization and affine
cohomology vanishing, sheafify, and reflect exactness. Moved three existing declarations before
the target so the proof can use them; their signatures, docstrings and bodies are unchanged.

Replaced the undelivered `ProEtaleComparisonInjectiveSectionsVanishing` module/node with
`Sheaf.AlgebraicGeometry.AffineComparisonInjectiveDerivedVanishing` and its node. The new
obligation concerns only affine schemes and derived global sections, not the target's derived
comparison direct-image sheaf. The existing abelian-group affine theorem does not cover arbitrary
Grothendieck abelian coefficient categories; its finite Čech proof is the source of the
categorical affine statement. The new docstring spells out both limits and the finite-product
argument. Updated both existing DAG nodes attached to the changed theorem to the actual route.

Converted proof-only public imports to ordinary imports. See
`coord/changes/lower-star-acyclic-proof-import.md`.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`.

Added one hole:
`AlgebraicGeometry.ProEtale.isZero_rightDerived_globalSections_comparisonUpperStar_of_isAffine`
(node `stage3-affine-comparison-injective-derived-vanishing`).

This is a decomposition: one upper hole closed, one strictly smaller affine cohomology hole
added, net zero direct holes. It is not a claim that comparison acyclicity is sorry-free.
There is no remaining `sorry` in the item; the new theorem's body is exactly `by sorry`.
The rejected undelivered sectionwise theorem/node is absent and adds no hole. No definitions
or data witnesses were added. Other imported theorems may still depend on `sorryAx`.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
- `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`
- `WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`

The following old proof-dependency edges of the two target attachments are no longer used by
the direct-image reduction (some remain transitively necessary for the affine theorem's plan):

- `def-sp-left-exact-additive`
- `def-weil-pbc-etale-site`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-sheaf-of-modules-category`
- `lem-cbc-abelian-affine-comparison-vanishing`
- `lem-cbc-comparison-pullback-sections`
- `lem-pc-fppf-affine-open-cover`
- `lem-sbc-etale-abelian-restriction-injectives`
- `lem-weil-pbc-cohomology-over-object-localization`
- `lem-weil-pbc-comparison-injective-acyclicity`
- `lem-weil-pbc-comparison-pullback`
- `lem-weil-pbc-open-immersion-etale`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-weil-pbc-sets-etale-inverse-image-composition-units`
- `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`
- `lem-weil-proetale-weakly-etale-localization`

No claim is made here that these modules are unreachable from every other target: global
closure pruning and the pinned-baseline ledger are the maintainer's measurements.

## Where the brief, the DAG or earlier work was wrong

The first candidate's sectionwise higher-direct-image assertion was equivalent to its target.
Its sketch conflated sections of a cohomology sheaf with cohomology of a section complex; the
latter must first be sheafified. Removed that assertion rather than counting it as progress.
The earlier report also omitted four removed imports and all target-node updates. The target
node's old module-valued plan and its abelian-valued attachment both need the same generic
coefficient source theorem, but the imported affine Lean theorem only covers AddCommGrpCat.
This coefficient gap is now explicit in the affine obligation.

## New nodes

`stage3-affine-comparison-injective-derived-vanishing`:
`dag/nodes/sec-proper-base-change/stage3-affine-comparison-injective-derived-vanishing.json`.
It states the affine derived-global-section case for the exact coefficient universes of the
target. Source: [Stacks 099U](https://stacks.math.columbia.edu/tag/099U), with its finite Čech
proof interpreted categorically using exact filtered colimits. This coefficient extension is
our inference from the proof, not a claim that Stacks states arbitrary A verbatim.

Searches repeated by the second reader: LeanFinder (unrelated étale algebra results), Loogle
(generic injective right-derived vanishing, insufficient since comparison pullback is not known
injective), and Mathlib grep (no comparison vanishing hit). LeanSearch returned Internal Server
Error. Searches are recorded in `searches.jsonl`. Local `rg` found the abelian specialization
in `AffineComparisonInjectiveVanishing`, plus downstream comparison results that depend on this
target and cannot be used without a cycle.

Change record: `coord/changes/lower-star-acyclic-proof-import.md`.

## Second reading by V2

1. Compared all delivered existing declarations against the shared repository with `diff` and
   `stage3_delivery.diff_module`: no statement/signature changed, no existing declaration added
   or removed, and only the target proof body changed. Reordering three prior declarations and
   deliberate proof-import visibility changes are recorded above. No target or data definition
   was changed. Verdict: pass after repair.
2. Compiled both delivered modules using only `lcompile.py`; the item is sorry-free, and the
   affine module has just its named documented theorem hole. Checked for forbidden declarations,
   hollow definitions and witness selection: none. Axiom probes allow only propext,
   Classical.choice, Quot.sound and the existing/open sorryAx. Verdict: pass, with the one
   explicitly reported affine obligation.
3. Rejected the old sectionwise restatement. The replacement has the extra affineness hypothesis
   and asks only for cohomology of terminal evaluation; the upper proof supplies localization,
   derived-section transport, basis detection and sheafification. Checked the zero injective,
   empty affine scheme, q=0 (degree 1), all higher q and non-affine X in the upper proof. Finite
   products suffice; exact infinite products and injectivity on arbitrary scheme pullbacks are
   never assumed. The Ab-only existing theorem cannot solve the generic coefficient case.
   Verdict: genuine strictly smaller affine obligation, mathematically justified and not yet
   formalized.
4. Read the actual top-down proof and removed unused imports. The route uses the affine vanishing
   calculation before direct-image sheafification, as planned. Read both relevant unit records:
   `sk-thm-properbasechange` keeps all three realized steps; `sk-prop-sf-comparison` has no
   nonempty realized fields. No unit statement or step was bypassed or changed. Verdict: pass.
5. Replaced the new node and updated both existing target attachments' proof, proof_deps and
   proof_origin. Checked dependency union, verbatim new Lean signature, source, searches,
   blueprint ancestry, chapter/unit, creation and Lean metadata. Verdict: pass after repair.

Second reading changed the restatement into an affine cohomology reduction, corrected import
visibility/pruning, documented the coefficient gap and decomposition, and repaired DAG/report
metadata. Final dry run and delivery use deliver3.py.
