# Stage-1 report: lem-weil-pbc-top-base-change-presheaf

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-top-base-change-presheaf.json`: statement unchanged; five-step split of the specified normalized module base-change map.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-derived-adjunction-top-edge.json`: one new statement-only lemma, unsplit; no Mathlib match. This compares adjoints on top cohomology in a single derived adjunction, independently of base-change squares and coefficient units.
- `citations.json`: a verbatim statement quotation for every step/node citation. The full statements are quoted so the reader can check hypotheses as well as the used formula.

## Attachments

None. Searches in `lean/WeilConjectures/` by the item tag, base-change/cohomology/presheaf terminology, and top-adjoint terminology found no declaration with every clause and these hypotheses. I read the affine dictionary and module Leray comparison: the first assumes flat base change, qcqs and quasi-coherence, and the latter uses affine charts and a chart dictionary. The etale edge comparisons have constant etale coefficients. None states this variable-structure-sheaf lemma for arbitrary scheme morphisms and arbitrary modules. The new top-adjunct lemma also has no project attachment.

## WANTED

None: the sources used are present locally.

## Corrections and limitations

There was no previous sandbox split, report, citations file or search log to retain. The repository item was unsplit; its statement is retained verbatim. The cocycle equality is not a formal consequence of the existence of the top-cohomology isomorphism alone: the adjunction normalization matters. I isolate that exact generic comparison as the new node rather than cite an unnormalized adjunction or assume the derived mate is invertible.

The source for the item explicitly marks the derived-mate identification as agent work. I read the actual Stacks cocycle constructions rather than treating the source label as a theorem asserting the whole item. The new node's source likewise distinguishes Stacks' local-class construction from the extra agent adjoint assertion.

The five steps are complete conditional on the one new statement-only lemma. I leave no Lean code or compiler result. No repository or launcher file was written, and no git command was run in the read clone.

## Sources and searches

For the item I read `cohomology.tex`, Tag 01E4 (`lemma-describe-higher-direct-images`), Tag 01F8 (`lemma-functoriality`), Tag 01FB (`remark-explain-arrow`), and Tag 08HY (`remark-base-change`), including the proofs and resolution diagrams. For the new node I read Tag 0BKJ (`lemma-sheafification-cohomology`), the local Leray construction in `lemma-before-Leray`, the adjunction construction `lemma-adjoint`, and the standard truncation triangles in `derived.tex`, Remark `remark-truncation-distinguished-triangle`. I also read `derived.tex`'s pre-derived adjunction proof and derived-adjunction statement to check normalization. The new node cites 0BKJ for its edge construction and explicitly marks the top-adjoint refinement as agent work; its single-module normalization is supplied by the existing canonical-single-adjunction-transpose node.

I read the current main-20261015 ancestor `thm-weil-pbc-direct-image-finiteness-proper.md`: it states FIN with no proof. The inherited blueprint place records the classical coherent edge comparison below that finiteness input. This split makes that local identification explicit; it does not replace a step of the proper-base-change unit. I read the chapter record, the unit's three steps and the three-level rule in SETUP. All off-unit proof uses are generic resolution, adjunction, or local-section tools, declared in split_report.tool_uses.

Whole-DAG searches covered cohomology-presheaf/derived-section identifications, top cohomology, adjunction normalizations, edges, and the source tags. Whole-blueprint searches were run with `blueprint_refs.py` for base change presheaf, cohomology edge, adjunction cohomology, hypercohomology, top cohomology, top adjoint, cohomology adjoint and 0BKJ. No blueprint statement supplies the new adjunct equality. In particular I reused the general ringed-space sheafification theorem, the unbounded direct-image section-presheaf theorem, and the normalized derived composition theorem instead of creating duplicate nodes for their specializations.

All Mathlib searches were run through msearch.py, and their actual results are in searches.jsonl. Both the item and the new node have semantic searches with distinct phrasings, Loogle patterns and source grep queries. LeanSearch and LeanFinder returned ordinary sheaf adjunctions, sheafification/pullback commutation, generic derived adjunction construction, triangulated adjunctions, or unrelated cohomology. I read `Adjunction.derived` and its unit/counit factorization, `Sheaf.cohomologyPresheafFunctor`, and the module pullback/sheafification source. The first constructs an adjunction without asserting its cohomology edge normalization, the second concerns Ext-defined abelian cohomology, and the third is underived. None is a one-line specialization proving the new lemma. No service failure was recorded as absence.

## Review by NP

In step 1 I checked the statements of def-pc-derived-module-base-change-map and def-pc-derived-base-change-map against the actual composite used: the former normalizes c_v as the transpose of the ordinary coefficient unit; the latter gives the base-change adjunct by the derived unit and direct-image composition. The derived and ordinary adjunction nodes provide exactly the hom equivalences used. The composition node gives the isomorphisms between the derived direct images of the equal composites. Naturality in the target identifies the adjunct after c_v, so this step identifies the specified delta, not an arbitrary arrow with the same source and target. The module-map definition already permits arbitrary modules; no quasi-coherence from the more restrictive statement of the general base-change definition is used as an additional hypothesis.

In step 2 I checked that the ringed-space sheafification statement gives canonical local classes, their sheafification and their naturality. The unbounded direct-image section-presheaf statement gives the local Leray isomorphism, natural in the derived object and compatible with opens; it is not just an abstract isomorphism of groups. The module-sheafification definition gives the factorization through a sheaf. On complexes all maps preserve the action of O_S(V), which checks the module structure despite the section-presheaf theorem being phrased for underlying abelian groups. The derived-image definition computes D on a K-injective representative; the bounded-below resolution theorem supplies a bounded-below K-injective complex for G[0], so D satisfies the new lemma's lower bound. The upper bound on C is exactly the item's hypothesis. The new lemma uses the same kappa, not a freely chosen isomorphism.

For the new lemma I checked the source's local cocycle/sheafification formula and its unique factorization. Its remaining assertion is a genuine general adjunction lemma. A proof can first map K to tau_{>=q}K. Since Lg*C lies in D^{<=q}, morphisms to that truncation are controlled by H^q; since Rg_* is left t-exact, its bottom cohomology is g_*H^qK. Truncate C at its top degree as well. Naturality reduces the adjunct comparison to shifted modules, where the canonical-single-adjunction-transpose statement gives exactly the normalized ordinary transpose. The edge agrees with this truncation description by the natural local-class formula. This is more than a two-line consequence and therefore remains the one unsplit node. It contains no square, no higher direct-image of a module along f, and no identification of a coefficient-unit cohomology map, so it does not restate a clause of the item.

In step 3 I opened the module cohomology-fmap definition and its independence theorem: their roof is precisely H(Gamma ell) inverse after H(Gamma beta). The open-restriction theorem explicitly says the restricted augmented resolutions remain injective resolutions. The pushforward-injectives sections theorem proves Gamma(U,ell) is a quasi-isomorphism, with its nonnegative-complex hypothesis satisfied by the choices in the cohomology-map definition. Bounded-below injective complexes are K-injective by the cited theorem, which allows the normalized composition theorem to be applied to J. That composition theorem's statement explicitly says f_*ell is a quasi-isomorphism and gives its normalization, not merely existence of some composition isomorphism. Thus the displayed roof for A and its evaluation are justified. I retained the pullback composition identification for the restricted coefficient. This calculation is the substantive coefficient-unit part of the item, not a new node equivalent to the original conclusion.

In step 4 I checked both class maps on the same resolutions I and J. The higher-direct-image-presheaf statement explicitly specifies the image of a cocycle, so it identifies the particular theta maps, rather than merely proving that two sheaves are isomorphic. The naturality sentence in the ringed-space sheafification theorem supplies the square for the actual derived morphism A. The local derived-sections statement supplies the canonical identifications of their domains. No assertion that a sectionwise theta is bijective occurs. Step 5 only substitutes these established equalities and cancels the invertible local derived-sections comparison.

I checked B--E of delivery-errors point by point: the new node introduces all objects and has empty proof/proof_deps; its notions are inline or in stmt_deps; every actual non-elementary input is a cited statement; the citation quotes are copied verbatim; source tags and labels were read; searches were executed; there is no created node for an elementary sheafification factorization or a clause of the original item. I checked the directions and types of every lambda, e, theta and adjunct. Every proof step is shorter than 2000 characters; step 3 writes the roof explicitly instead of saying only that the maps transport. Statement, blueprint metadata and imported flags of the item are preserved.

The small cases checked were: q=0 (the formula is the ordinary pullback unit on sections); f or g the identity (the roof reduces to the ordinary coefficient map or the identity); empty opens or empty schemes (zero section complexes and their unique maps); zero coefficients (all maps zero); and a nonflat ring quotient A to A/(t) (derived pullback can have lower Tor, but the new lemma only compares the top degree using kappa). The boundedness condition is used only in the top-adjoint lemma; in particular no injectivity of pullback, no flatness, no affine acyclicity and no invertibility of delta is smuggled into the resolution argument.

## Not duplicates

lem-weil-pbc-derived-adjunction-top-edge vs lem-trf-derived-basis-local-ext-sheaf: the existing node concerns sheaf conditions for local derived Hom under negative-Ext vanishing; the new node identifies ordinary and derived adjoints in degree q.

lem-weil-pbc-derived-adjunction-top-edge vs lem-trf-unbounded-direct-image-section-presheaf: the existing node gives local Leray and sheafification identifications, which the new node uses; it has no pullback adjunction or top-adjoint equality.

lem-weil-pbc-derived-adjunction-top-edge vs lem-pc-ringed-space-derived-limit-stalk-injective: the existing node gives injectivity on stalks of a derived inverse limit under stabilization assumptions; the new node concerns a single morphism and its adjoint.

lem-weil-pbc-derived-adjunction-top-edge vs new-qcoh-acyclic-sheafification-component: the existing node identifies sheafified section cohomology for qcqs cohomologically acyclic morphisms and quasi-coherent inputs; the new node compares adjoints without those assumptions.

lem-weil-pbc-derived-adjunction-top-edge vs lem-pc-cohomology-presheaf-derived-sections-evaluation: the existing node compares evaluation of a chosen presheaf functor with derived sections; it has no equation for adjuncts on cohomology.

lem-weil-pbc-derived-adjunction-top-edge vs lem-pc-ringed-space-sheafification-cohomology: the existing node gives natural local class sheafification, which is reused to define the edge; it does not identify derived transposes with ordinary transposes.

lem-weil-pbc-derived-adjunction-top-edge vs lem-pc-canonical-single-adjunction-transpose: the existing node is the normalized transpose for modules in a single degree. The new node permits an arbitrary C bounded above at q and a bounded-below K, and compares the q-th cohomology adjunct through the local derived-image edge. Its additional truncation comparison is not a one-line specialization.

## Unfinished work

No item-level work remains. The new statement-only lemma is intentionally not split in this one-level delivery. The final dry run and push results are recorded by the delivery tool.
