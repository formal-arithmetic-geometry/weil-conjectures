# Worker report: lem-pur-relative-extension-cohomology-normalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-relative-extension-cohomology-normalization.json`: item, statement; split into ten proof steps, no Mathlib match for the full item. The statement is unchanged. Added the constant-sheaf, direct-image and inverse-image definition dependencies implicit in its notation.
- `citations.json`: one verbatim statement quotation for each of the 32 step/node citations. The whole statement is retained when its several clauses fix the normalization being used.
- `report.md`: this report and signed review.
- `searches.jsonl`: actual search-command records. Existing searches in the live item were retained, and searches made in this dispatch were appended to the item with their actual query strings and results.

New nodes: 0. New Mathlib leaves: 0. Every needed general lemma already has a DAG node. No Lean was written and no compiler or build tool was run.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, the item id, relative torsors, framed torsors and torsor extensions found no project declaration stating the item. Existing declarations under `lean/Sheaf/` implement some of its helper interfaces; they do not justify attaching the whole item.

## WANTED

None. The source texts used are present locally.

## Findings and proof route

The original item was statement-only, with prior Mathlib searches. Its statement is consistent with the intended relative construction, but ordinary torsor normalization alone would not determine the class with its chosen complementary section. I supplied the missing supported cocycle computation rather than arguing from equality after forgetting support.

Write the supported extension as B and choose h from its middle sheaf to the degree-zero injective, extending the augmentation of G. Its differential factors through Q, giving a closed map k:Q→I¹. The morphism from B to the first resolution row, together with the existing first-row sign theorem, shows that extMk(k)=−β. Under the prescribed kernel inclusion the cocycle k is exactly (k(p(1)),0). The ordinary extension pulled back along p has fibre P, and h sends its specified section to zero. The existing signed torsor-cocycle theorem consequently identifies its raw class with that same cocycle, and c is its negative. This proves the full relative equality, including the section and sign. Pushout, exact etale inverse image and a second quotient restriction give the three functorialities; the explicit fibre calculation gives the final positive ordinary class.

The ancestor is `lem-pur-divisor-class`, via `lem-pur-divisor-normalized-realization`. I read the current main-20261015 divisor proof, especially its first sentence and final paragraph, together with the live corrected divisor and realization nodes. This item supplies only their relative-torsor/ordinary-class normalization tool. It changes no chapter or unit route and uses no SGA source. The key-node unit realization fields are not this item's responsibility and were left alone.

## Mathlib and duplicate searches

I read the inherited Mathlib search results in the item. Fresh searches used leanfinder, loogle, grep and leansearch through the prescribed msearch command. The two semantic formulations asked both for extension-to-resolution cocycles and for the supported framed-torsor comparison. Hits included `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_extMk`, `extMk`, `extMk_hom`, `mk₀_comp_extMk`, `CategoryTheory.Sheaf.H`, and `CategoryTheory.ShortComplex.ShortExact.extClass_naturality`. I read the actual Mathlib Injective/Ext and ExtClass source, including extClass_naturality at line 131. These are generic tools, not the assertion for the closed integer sheaf, a framed torsor and the signed support comparison. Naturality already has the exact Mathlib-leaf node `lem-sc-p1-ext-class-naturality`, which is cited instead of recreated. The specialized grep in CategoryTheory/Sites returned no relative-torsor/Ext match. No service-unavailable response was called a negative result.

I searched the whole DAG for relative torsors, extension cocycles, the first resolution row, support-Hom normalization, 03AJ and 06XR/06XV, and used blueprint_refs searches for “relative torsor”, “extension cocycle”, “first resolution”, “framed”, “extension class”, “03F1”, “supported Hom” and “torsor extension”. I opened the candidate statements. This found all the helpers used here and ruled out creating the tempting duplicate extension-cocycle lemma. No imported blueprint node states this whole relative normalization in another form; the item's same_as stays empty.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs to distinguish.

## Review by NK

I read Stacks `sites-cohomology.tex`, Tag 03AJ (`lemma-torsors-h1`), including the free-abelian pushout extension, boundary of one, and inverse injective-lifting construction. I also read Tag 03F1 (`lemma-h1-extensions`) immediately following it. I read `etale-cohomology.tex`, Tag 0A45 (`lemma-cohomology-with-support-triangle`), which obtains the support triangle from a degreewise exact injective restriction sequence. In `derived.tex` I read Tags 06XR (`lemma-compute-ext-resolutions`) and 06XV (`lemma-ext-1`) for the relation between injective cocycles, derived Ext and extensions. The framed refinement and the precise Mathlib sign are agent arguments, not assertions quoted verbatim from Stacks: proof_origin is therefore agent. I read the source and statements of the existing first-resolution sign theorem and the relative signed-cocycle helpers to fix that sign.

Step 1 uses the actual open-closed short exact sequence and the explicit open adjunction. Their statements give the maps and the counit, not just an existence assertion about an unspecified sequence. The constant-sheaf definition supplies its sheafification universal property, so evaluation at 1 and the identification Hom(j! Z_W,F)=F(W) follow directly. The relative extension lemma requires precisely this sequence, this natural equivalence, and the supplied section. I checked these hypotheses rather than assuming that a general closed support extension automatically has a torsor interpretation.

Step 2 uses injectivity in exactly its stated monomorphism-extension form and the exact-epi cokernel lemma in exactly its stated factorization form. The augmentation differential vanishes, v is epic, and the resolution is nonnegative and exact in positive degrees. These imply the two factorizations and the first-row short exactness. The resulting map of short exact sequences has end maps identity on G and bar k on Q; there is no unproved identification of a section with a morphism.

Step 3 uses the general extClass_naturality leaf, whose statement allows any abelian category and this morphism of short exact sequences. The first-resolution theorem explicitly says extMk(iCycles)=−S.extClass. The roof-normalized RHom theorem states the cocycle formula with inverse shifted augmentation; precomposing its complex map is literally precomposition of that formula. These statements give extMk(k)=−β, including the minus sign, without using any helper's proof as a premise.

Step 4 uses that same roof formula to interpret k in derived Hom. The integral instance of the item's prescribed supported-Hom normalization, together with the stated kernel inclusion and quasi-isomorphism in the divisor-relative-cone node, sends it to (k(p(1)),0). I checked a|W=0 and da=0 before taking its class. The amb-closed-support-Hom statement gives the derived isomorphism for a commutative coefficient ring, so A=Z is valid; the finite-coefficient-only supported-hom-cocycle-normalization node is deliberately not used here. The calculation does not infer a global relative class from agreement of local restrictions.

Step 5 is the elementary local computation from the free-extension presentation. I opened that definition's quotient universal property and the ordinary torsor theorem's explicit free-abelian presentation. The formula [t]↦(f(t),1) respects [g+t]=[t]+g. After choosing a local section t0 the displayed formula on G⊕Z has inverse obtained by subtracting n f(t0) and taking the unique kernel element g. Thus the fibre has the original G-action, with no inverse action or sign change. Local choices are used only to check this prescribed global morphism is an isomorphism; no global section is assumed. Pullback short exactness follows by local lifting through the sheaf epimorphism v and the explicit kernel, not by assuming v is surjective on every object.

Step 6 cites the statement of divisor-torsor-boundary-signs: it provides the exact raw formula (a,b) for a map from the ordinary canonical extension to I0 and identifies raw alpha as negative normalized c. Step 5 provides the required ordinary extension, h0 provides the required augmentation extension, and f(s)=0 gives b=0. This is what identifies the chosen complementary section; ordinary forgetting alone would not suffice. I checked that the cited node has no dependency on this item, so this use does not assume the result being proved.

Step 7 checks the coefficient functoriality on extensions, not just on their ordinary images. The pushout lemma gives a short exact pushout and its morphism from B; extClass_naturality gives the class. The contracted-product definition gives exactly the quotient universal property needed for the explicit invariant formula in the step. The relative extension statement gives uniqueness after checking equivariance and the zero value at [s,0]. The amb supported-Hom statement is natural in its complex argument; the divisor-relative-cone statement includes coefficient naturality; the relative-torsor-cohomology statement gives the corresponding coefficient naturality of c. Thus every compatibility used here is a statement-level clause.

Step 8 uses inverse-image exactness with R=Z, as that node explicitly allows, and the supported-Hom-naturality node for its closed exchange isomorphism and its displayed pullback equation. That node applies to bounded-below complexes; G[0] satisfies this hypothesis. The pulled extension still has the specified equivariant map and zero open section, so the relative extension uniqueness applies again. The c pullback clause is present in the relative-torsor-cohomology statement. In particular no finite coefficient or Cartier condition has slipped in from an adjacent purity theorem.

Step 9 writes the actual quotient arrow q:Q′→Q and checks p=q p′. The map to the pullback extension is written out and is zero on the smaller complementary open. Extension naturality and the relative extension uniqueness identify its class. The equality (zq)p′=zp checks the kernel-inclusion square directly; the second coordinate restricts to W′. The divisor-relative-cone statement explicitly says this is enlargement of support. Applying the already established relative equality to both framed pairs gives the claimed c compatibility; I did not cite the relative-torsor-cohomology statement for an enlargement clause it does not contain.

Step 10 uses the supported-Hom-naturality statement's explicit forgetting-equals-precomposition clause and the divisor-relative-cone statement's projection clause. The boundary-of-one convention is explicitly in the ordinary torsor theorem's statement. Combined with Step 5, it gives the positive ordinary torsor class. This verifies the final clause independently of simply naming it standard.

For B1–B9 and D1–D5, no statement-only auxiliary node was needed: elementary local kernel and generator calculations remain in the item's proof, while every non-elementary input is an existing cited statement. The ten steps are all below 2000 characters. Statement quotations were copied directly into citations.json; no quotation was paraphrased to make a mismatched citation pass. The off-unit statements are recorded as generic tool uses in split_report, not as maintainer-owned top-level tool_uses. I checked the source route against the current blueprint ancestor and the three levels in SETUP.

For the small cases in section E, I checked G=0 and the trivial framed torsor, where k and the class can be chosen zero; W=T, where Q=0 and the specified section globally trivializes P; W empty, where Q=Z_T and the argument becomes exactly the ordinary extension comparison; and T empty, where every group is zero. For a trivial torsor with an arbitrary section g on W, one may choose E_P=G⊕Z and h(g0,n)=epsilon(g0), giving raw class (0,epsilon(g)) and normalized class its negative, as the cited sign theorem requires. This checks the section contribution rather than testing only globally extendable sections. No Cartier, regularity, quasi-compactness, invertibility of a coefficient exponent, or global triviality hypothesis is used.

I corrected no statement. During the self-review I avoided two possible C4 mistakes: using the finite-coefficient normalization node at A=Z, and claiming that the relative-torsor-cohomology statement already includes enlargement of support. The proof instead uses the general roof formula and the explicit quotient/kernel square.

## Unfinished work

None in this stage-1 split. Existing cited unsplit or sorried helpers remain their own items. Server dry-run and delivery results are recorded below when available.
