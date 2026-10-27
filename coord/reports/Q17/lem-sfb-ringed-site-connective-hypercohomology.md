# Worker report: lem-sfb-ringed-site-connective-hypercohomology

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-connective-hypercohomology.json`: statement node, split, no new nodes; Mathlib searches found no exact match.
- `citations.json`: verbatim statement quotes for every cited node at every proof step.
- `report.md`: this report.

Attachments:

- None. I searched `lean/WeilConjectures/` for the item id and for connective hypercohomology, and found no exact sorry-free project declaration.

WANTED:

- None. The proof follows the Stacks documents already present in the repository.

What I checked and corrected:

- The imported statement is unchanged. Its hypotheses include smallness, commutative ring sheaves, the unbounded module-derived category, vanishing of all negative cohomology sheaves, localized sites, and the derived ringed-topos morphism. No upper bound or scheme hypothesis was added.
- I searched the DAG for the item, its Stacks tags, connective/nonnegative hypercohomology, and kernel/global-section formulations. The closest existing split is `lem-trf-connective-hypercohomology-sheaf`; it treats a ringed space and the presheaf calculation, so I cite its underlying inputs rather than duplicate it. No node states the full ringed-site item.
- The proof is seven steps: bounded-below injective replacement and unbounded derived-functor existence; the sectionwise kernel and negative vanishing calculation; identification with the canonical truncation map; naturality and choice independence via K-injective homotopy representatives; localization and restriction compatibility; the explicit kernel formula for a nonnegative complex; and the pullback/unit compatibility via the derived adjunction and normalized Leray comparison.
- The only generic cross-unit inputs are declared in `split_report.tool_uses`: Grothendieck module categories and K-injective existence, K-injective morphism realization, localized K-injective restriction, the ringed derived adjunction, its ordinary module adjunction, and derived direct-image composition. They are used as black-box infrastructure and do not replace the constructible-stability route.

## Review by Q17

I read the item source in `literature/stacks-project/sites-cohomology.tex` (Tags 071J and 07A5) and the connective degree-zero consequence in `literature/stacks-project/quot.tex` (Tag 08JX). I also read `derived.tex` Tags 013K, 070J, 070I, and the standard truncation definition (Tag 05RR), plus the localization/restriction argument in `sites-cohomology.tex` Tag 08FI and the derived direct-image composition at Tag 0D6E. The latest blueprint route was read in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`; the item serves the direct-image proof's connective hypercohomology input in the affine Hom reduction.

Step 1 cites the existing Grothendieck-module, enough-injectives, bounded-below derived-subcategory, bounded-below injective representative, K-injective existence, and total right-derived-functor statements. I checked that these statements give exactly a nonnegative injective K-injective representative and that the unbounded derived functor is computed on it; no upper bound is used.

Step 2 uses the cohomology-sheaf definition, sectionwise kernels of module sheaves, the derived-category cohomology formula, and the zeroth-hypercohomology definition. These statements say precisely that the degree-zero cycles are the global section kernel and that all negative terms give zero negative cohomology. The empty site/open and the zero complex satisfy the same formula.

Step 3 uses the standard truncation statement and the derived-functor unit. I checked that the canonical map from the zeroth cohomology sheaf in degree zero is represented by the inclusion of the cycle kernel, so the displayed isomorphism is the canonical one required by the item rather than an arbitrary representative isomorphism.

Step 4 uses the K-injective Hom realization, the right-derived-functor unit, and the explicit homotopy formula. The cited statements give a chain-map representative unique up to homotopy; because both complexes are zero in degree -1, the homotopy difference vanishes on degree-zero cycles. This proves naturality and independence of all model choices.

Step 5 uses exact derived restriction, localized-site K-injective preservation, localized section evaluation, and the derived-functor unit. I checked the hypotheses for every object and arrow in the site, including iterated localization. The section map is literally restriction of a cycle, so the two restriction squares agree.

Step 6 is the stated nonnegative-complex specialization. The cohomology-sheaf and module-sheaf definitions directly give the kernel of `Gamma(P^0) -> Gamma(P^1)`; it does not claim ordinary sections compute higher hypercohomology.

Step 7 uses the canonical ringed derived adjunction, ordinary module adjunction, and normalized derived direct-image composition. The right adjoint preserves kernels, so the zeroth cohomology of the derived direct image is the direct image of the zeroth cohomology. Applying the already checked degree-zero calculation to the derived unit gives exactly the section map in the item; the composition comparison identifies global sections on the source with sections after direct image. K-flat resolutions are used only in defining `Lf^*`, as required.

I ran the required Mathlib searches with `msearch.py` for the item: LeanFinder (connective degree-zero hypercohomology), LeanFinder (kernel formula), LeanSearch (right-derived degree zero), Loogle (`"rightDerived", "homologyFunctor"`), and grep (`homology.*rightDerived|rightDerived.*homology|hypercohomology`). The services returned only general derived-functor, sheaf-cohomology, and homological-complex declarations; none states this ringed-site connective theorem, so the item remains a split statement node.

The original `blueprint.from.node` is null: `tools/blueprint_refs.py ancestor lem-sfb-ringed-site-connective-hypercohomology` returns `None`, because the inherited creation chain terminates at `Sheaf.SixFunctors.CtfStabilityDirectImages` rather than a DAG id. I preserved the existing provenance record and its specified place/via chain and described the latest blueprint location in the split report. There are no new nodes requiring ancestor provenance.

I checked B1–B9: there are no new statement-only nodes or Mathlib leaves to audit. All cited statements were opened, and `citations.json` copies their text verbatim. I checked C1/C4 for each step as above, equality of `proof_deps` with the union of uses, and absence of a dependency path from the added tools back to the item. D1/D2 are avoided by doing the kernel, restriction, and naturality arguments in the item with no new restatement nodes. The longest step is 1534 characters, below the long-step threshold. The final pullback hypothesis is retained: nonflat change of rings can create negative cohomology, so the assertion is applied only when both E and its derived pullback are connective. I checked the identity ringed morphism, a sheaf in degree zero with connective pullback, the zero ring, zero complex, a complex concentrated in positive degree, nonnegative complexes with nontrivial first differential, and unbounded positive tails. All agree with the kernel formula; no assertion of exactness of arbitrary module pullback or injectivity of underlying abelian sheaves is used.

## Not duplicates

No new nodes were created. The existing ringed-space result `lem-trf-connective-hypercohomology-sheaf` does not include arbitrary small ringed sites or the derived pullback/unit clause. The constant-coefficient slice-model node `lem-pe-injective-complex-slice-section-model` has a different coefficient hypothesis and conclusion. I reused the general resolution and localization inputs underlying these nodes.

Before writing the report, the server `review_split` check passed with 0 new nodes. No Lean was written or compiled and no repository or launcher file was edited.
