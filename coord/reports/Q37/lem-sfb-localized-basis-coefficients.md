# Q37: lem-sfb-localized-basis-coefficients

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-localized-basis-coefficients.json`: statement, split into eight steps; not a Mathlib leaf. The statement, inherited sources, earlier searches and provenance are retained.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-ring-localization-sheafification.json`: new statement-only node, unsplit, not a Mathlib leaf. It states the ring-sheaf localization construction and its universal property, independently of any finite basis.
- `citations.json`: one verbatim statement quotation for each node used by each proof step (15 entries).
- `searches.jsonl`: actual Q37 search-command records; no inherited search was represented as a new Q37 search.
- `report.md`: this report.

## Attachments

None. I searched the project source by the exact blueprint tag, localized-basis terminology, ordinary localized-basis declaration names, and ring-sheaf localization terminology. The ordinary algebra and affine scheme files found do not state this arbitrary-site internal-module lemma. The existing sheafification node is already attached to `CategoryTheory.sheafification_sections_local`; that is a dependency, not an attachment of the item.

## WANTED

None. The sources used are present locally.

## Issues found and corrections

The imported item has the correct statement and no proof. It is not permissible to apply the ordinary `Module.Basis.localizationLocalization` directly to the section rings: sections of a sheafified localization need not equal the corresponding ordinary localization. I retained the statement and supplied the missing argument with local fractions. In particular no scalar map is silently identified with another one, and the prescribed square is proved by an explicit formula.

The blueprint finite-free proof's sentence beginning "Inverting" refers to a coefficient identification and states compatibility "by construction". The split makes the basis argument and the square explicit, while remaining on that localization route. No statement dispute or route change was necessary. No unfinished part of this item's proof remains; the one new supporting construction is intentionally a statement-only next-stage-1 item.

## Sources and searches

I read the chapter and unit records and the current `main-20261015` finite-free statement and `.proof.md`. The exact ancestor place is the proof sentence "Inverting ell ... gives E_X^d ... and the two isomorphisms are compatible with O to E by construction"; this realizes unit step 3. For the item and the new ring-localization node I read `literature/stacks-project/sites-modules.tex`, Tag 0EMC (`lemma-simple-invert`), including its preceding presheaf definition. I also read Tag 0EMD (`lemma-simple-invert-module`); it is not needed in the final proof. Both Stacks proofs are marked omitted, so the finite-coordinate proof is explicitly attributed to the agent. For the existing sheafification tools I read `sites.tex`, Tags 00WB (`theorem-plus`, its fraction/local-refinement description) and 00WK (`lemma-sections-sheafification`), and opened the existing DAG statements themselves.

Before creating the supporting node, I searched the whole DAG for 0EMC, 0EMD, `lemma-simple-invert`, ring localization, sheafified localization and fraction descriptions. I ran blueprint searches for localization, local fractions, sheafification of the presheaf, invertible sections, inverting a section, ring localization and simple-invert, and the ancestor command. I reused the existing local-section and underlying-set sheafification nodes; no equivalent ring-localization universal-property node was found.

The Q37 Mathlib searches were performed only with `msearch.py`, with LeanFinder, LeanSearch, Loogle and grep, including two semantic formulations for localization. Their actual summaries are copied from `searches.jsonl` into the nodes with the identical tools and query strings. I read `Mathlib/RingTheory/Localization/Module.lean:105-127,143-185`: the candidate basis lemmas apply to ordinary rings/modules. I read `Mathlib/Topology/Sheaves/CommRingCat.lean:74-107`: it constructs a localization presheaf on a topological space, with its objectwise instances, but has no arbitrary-site sheafified ring universal property. Scheme structure-sheaf local-fraction predicates in the search results are also a different setting. Thus neither the item nor the new node is a one-line Mathlib specialization.

## Not duplicates

lem-sfb-ring-localization-sheafification vs lem-sfb-localized-basis-coefficients: the new node has only one ring and an inverted global section; it constructs its ring-sheaf localization and identifies arbitrary universal-property models. The item has two ring objects, a specified scalar map and finite module basis, and proves that this basis remains a basis with its specified square. The new node asserts none of those conclusions.

lem-sfb-ring-localization-sheafification vs det-prop-sfb-cartesian-coefficients-finite-free: the latter is the integral and rational coefficient finite-basis comparison for a finite extension of local fields, with inverse-image compatibility and flatness; the new node is the arbitrary-site ring-localization construction, with no fields, coefficient pullback, basis or flatness assertion. These are the two existing nodes carrying Tag 0EMC.

lem-sfb-ring-localization-sheafification vs def-weil-pbc-local-coefficient-localization: the existing definition specifies an underlying module colimit on a localized ringed site and its sheafified sectionwise description, as well as a derived multiplication transformation. It does not state the ring-object universal property or the uniquely compatible identification with any ring localization supplied in the item's hypotheses.

lem-sfb-ring-localization-sheafification vs lem-weil-pbc-site-sheafification-sections-local: the existing result is the local representability and equality criterion for an arbitrary presheaf's set sheafification. It contains no ring localization construction or ring-map universal property; it is reused, not duplicated.

## Review by Q37

I checked every part of delivery-errors B to E against the final JSON and the sources. The new node introduces its site, universe, ring, global section, fraction relation, arithmetic, restrictions, sheafification and universal property; its notion dependencies define exactly the tensor, ring objects and sheafification used. It has an empty proof and empty proof dependencies, not a proof sketch hidden in its statement. Source places use the verified Stacks tag and label, and all mathematics uses single-escaped TeX in the parsed JSON. I checked the new construction is separate from the finite-basis claim: it is the supporting 0EMC localization theorem, while surjectivity, injectivity, the specified scalar action, the square and uniqueness are proved in the item's own steps. There is no new node for finite common denominators, gluing, standard generators or any other elementary subclaim.

For step 1, I opened the statements of `sk-def-sfb-sheaf-tensor`, `sk-def-sfb-ring-object`, `sk-def-sfb-module-objects` and `sk-def-sfb-change-of-scalars`. They give respectively the sheafified tensor, compatible multiplication/unit, module linearity, and the exact restriction-of-scalars action. The conversion to section operations is the sheafification universal property; the finite biproduct is constructed explicitly by componentwise gluing and its injection/projection identities. These are elementary consequences, not an appeal to an unmentioned general equivalence theorem. The inverse-coordinate identities used later are the given inverse of q, not another finite-free theorem.

Step 2 uses only the actual ring-localization universal property in the item's hypotheses. It applies to j_T composed with phi because its value on t is exactly the invertible j_T(phi(t)). This supplies the required phi_t, not a freely chosen action on B.

For step 3, I opened the full statement of the new ring-localization model and the existing `lem-pc-sites-sheafification-underlying-sets` and `lem-weil-pbc-site-sheafification-sections-local`. The first gives the quotient presheaf and identifies its ring sheafification with the supplied A or B, the second makes its underlying-set sheafification available, and the third supplies both local representatives and local equality. These statements say exactly what the step takes. Their small-site/universe assumptions hold; I use covering refinements and common test objects, and do not assume enough points or existence of fibre products in the category. The power-torsion relation is written in the supporting statement, not extracted from its nonexistent proof.

Step 4 uses precisely the module action and restriction formula in the two cited definition nodes. Its sum is an actual finite sum of morphisms on sections, it is A-linear for phi_t, and substitution of phi_t j_R = j_T phi proves the square.

Steps 5 and 6 cite the same three localization/sheafification statements as step 3, so they do not smuggle in a global fraction presentation. Step 5 applies the given inverse coordinates to a local numerator and displays its preimage. Step 6 first refines finitely many covers, changes numerators by t^(N-n_i), and then invokes only a locally available killing power. R-linearity of the given inverse q converts phi(t)^k u = 0 to t^k r_i = 0. Multiplication by the already invertible s proves vanishing in A. This checks all hypotheses at the exact uses and never cancels t in R or phi(t) in T.

Steps 7 and 8 are elementary. In step 7, injectivity on every object establishes compatibility of the local preimages on every common test object, and the sheaf axiom glues them. Additivity and scalar compatibility of the inverse follow by applying the injective map Q. In step 8, the prescribed square fixes the images of the standard basis vectors and hence every A-linear map from the finite free module. The precise scalar action and all clauses of the item survive.

I checked small cases explicitly: I empty forces T and B to be zero and the same proof gives the unique zero-module isomorphism, even when R to T is noninjective. At t=1 the localization models are the original rings and the formula returns q. At t=0, or at a nilpotent t (for example R=T=Z/4 and t=2), both localizations are zero and the killing-power argument remains valid. The zero ring and an empty covering cause no exceptions to the sheaf axioms. Exponents can vary across covers; no global bound is assumed. Every non-elementary step has cited statements, every citation quotation is literally part of that statement, and every step is under 2000 characters. The new node depends only on pre-existing notions and is not proved from the item, so it creates no cycle. The reused off-unit tools are a Mathlib leaf and a Lean-closed node, so they are tools rather than a replacement route.

## Validation

The server-side `review_split` check passed before this report was written. The required delivery dry run and push are recorded by the delivery tool; no compiler or local DAG-check script was run. All writes are confined to the assigned sandbox.
