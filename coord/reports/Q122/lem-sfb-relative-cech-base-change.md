# Worker report: lem-sfb-relative-cech-base-change

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-cech-base-change.json`: split into five steps, with the original mathematical statement and hypotheses retained. Corrected literal doubled TeX backslashes in that statement.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fibred-big-etale-abelian-functoriality.json`: new statement-only input, unsplit; Mathlib searches found general continuous/cocontinuous site machinery but no one-line specialization supplying the fibred-site hypotheses and displayed section formula.
- `dag/nodes/sec-six-functors-basics/lem-sfb-fibred-presheaf-pushforward-base-change.json`: new statement-only input, unsplit; Mathlib searches found generic Kan-extension machinery but no theorem supplying this fibred-groupoid comparison.
- `citations.json`: seven verbatim quotations, covering every node citation of every proof step.
- `searches.jsonl`: actual search command records; inherited item searches were retained in the item and five additional searches were recorded there. Each new node has LeanFinder with two phrasings, LeanSearch, Loogle and source grep records.

## Attachments

None. I searched the project under `lean/WeilConjectures/` for the exact blueprint tag, relative-Cech notions, base-change names, and fibred-groupoid/2-fibre-product vocabulary. The exact tag and fibred-groupoid encodings had no hits. The nearby `CategoryTheory/Sites/CechBaseChange.lean` was read: it concerns a finite cover, section modules and faithfully flat tensor base change, not the arbitrary fibred big-etale sites in this item. A sorried or partial scheme-Cech theorem is not an attachment.

## Wanted literature

None. All sources used are in `literature/stacks-project/stacks-sheaves.tex` and the current blueprint under `literature/blueprint/latest/` (main-20261024).

## Corrections and scope

The imported item had no proof. Its mathematical statement is correct: Stacks Tag 06XC even works for abelian presheaves. I preserved its abelian sheaf coefficients, arbitrary fibred groupoids, arbitrary base change, augmented degree -1 identity, face compatibility, and ordinary derived-category consequence. I corrected its TeX overescaping and made the existing etale-morphism notion an explicit statement dependency; its inherited null blueprint ancestor is retained. The new functoriality input explicitly binds both coefficient presheaves; the new base-change input specifies that its auxiliary functors are between fibred groupoids. `blueprint_refs.py ancestor` printed None because this inherited creation chain ends at a Lean-module identifier. The explicit inherited place and the existing `def-sfb-stable-pointed-moduli-groupoids` record point to paragraph (3) of `det-thm-sf-ctf-stability-direct-images`. I initially filled that inferred ancestor, but the dry run correctly enforced the brief's exact resolver convention: the nearest ancestor computed through `created.item` is None. I restored None in the item and new nodes, preserving the inherited via list and the complete explicit supporting place. The creation chain's missing DAG anchor is reported here for the maintainer, rather than being silently repaired outside this item. I read paragraph (3) in the latest direct-images proof and the latest unit and chapter. This is supporting cohomological work in the inherited alteration/moduli branch, not a change of the unit route. The old unit JSON still has its historical chapter/source; neither unit nor chapter was edited.

The two new inputs are not clauses of a relative Cech-complex assertion. The first is the generic sheaf-preservation theorem for a single fibred-category functor, without any nerve or base-change square. The second is generic underived pushforward base change for an arbitrary abelian presheaf, without a nerve, differential, augmentation or derived object. The item itself proves the nerve squares are 2-cartesian, constructs its term comparisons, and checks every face and the augmentation. This separates the actual lemmas used by the source (06TS and 075B) from elementary assembly, rather than replacing the conclusion by a new name.

## Review by Q122

I read the complete local statement and proof of Tag 06XC (`lemma-base-change-cech-complex`), the preceding `remark-cech-complex-sections`, the relative-complex definition including its extended degree -1 form, `lemma-generalities-sheafified`, `remark-cech-complex-presheaves`, and the explicit tuple formula in `lemma-generalities`. For the functoriality input I read Tag 06TS (`lemma-functoriality-sheaves`), its abelian-coefficients paragraph, the preceding presheaf formulas, and Tag 06W6 (`equation-pushforward`). For the other new input I read Tag 075B (`lemma-base-change`) and its test-fibre proof. These places assume only categories fibred in groupoids; the fppf subscript on the scheme category fixes the available objects, while 06TS explicitly includes the etale topology. No SGA route is used.

For step 1, I checked that the new functoriality statement supplies preservation of abelian sheaves for both precomposition and compatible-family pushforward, not merely a definition of those functors. This is the only non-elementary sheaf assertion used there. I opened `def-sfb-stable-pointed-moduli-groupoids`: it gives the actual objects and arrow relation of the 2-fibre product and the induced pullbacks. Iterating that definition yields the shared-target tuple model used in the proof. Cancellation in the alternating sum is written explicitly; the augmentation case is the equality of its two restrictions, so no spectral-sequence or exactness theorem is being used.

For step 2, I checked both directions of the tuple comparison. A tuple of fibre-product objects with isomorphisms beta_i to y is sent to the tuple with common target e(y), composing alpha_i with e(beta_i). Conversely a common-target tuple is lifted using y in every factor and identity beta_i. The beta_i and delta give the two composite isomorphisms; the arrow relation in the cited definition verifies naturality and the coefficient identification. All objects are over the same test scheme. This establishes 2-cartesianness without algebraicity or representability, and coordinate deletion visibly commutes. This is a routine application of an explicitly stated definition, not a new auxiliary lemma concealed behind a long step.

For step 3, I opened the new presheaf base-change statement and checked that it is natural in coefficients and in every test arrow, and that its actual component is restriction of compatible families. The square supplied in step 2 satisfies its 2-cartesian hypothesis. Its coefficient N is exactly f_p^{-1}F, and precomposition along the explicitly given h_p identifies it with g_p^{-1}e^{-1}F. The new functoriality statement, also cited, ensures these presheaf isomorphisms are between sheaves. Neither a higher-direct-image theorem nor an O-module theorem is silently specialized to arbitrary abelian sheaves.

For step 4, I checked the exact part of the new base-change statement that describes components, not just the existence of an abstract natural isomorphism. Evaluating each face square on a test object gives the two displayed components of the same family. They agree by the explicit deletion formula of step 2, including their maps on coefficients. In degree -1 the comparison is the identity; the two augmentation values are the restriction of the same t along the same structural arrow. This proves compatibility with the actual augmentation and every face rather than asserting unspecified canonicality. The quotation in `citations.json` for this step includes the restriction formula and its naturality.

For step 5, I opened `def-weil-abstract-derived-category` and checked that it states the localization functor from cochain complexes, exactly what is used. Adding the already proved face equalities gives the differential equality; the inverses give a complex inverse. The localization functor takes these mutually inverse maps to mutually inverse maps, so there is no unproved claim about derived inverse-image functors, cohomology comparisons, or an equality merely degree by degree. The split already provides an isomorphism of complexes, hence an isomorphism of derived objects.

I checked every new statement on the following small cases. For an identity functor or identity base change the family comparison is identity up to the specified canonical tuple identifications. For an empty source its compatible-family group is the zero group and both base-changed groups are zero. For a nontrivial fibre automorphism group, compatible families impose invariance under those arrows on both sides; nothing passes to sets of isomorphism classes. With f the identity, the augmented terms identify with F, augmentation is identity, and the alternating differentials start with 0 and then identity, consistent with the face calculation. Degree p=0 has two faces, degree -1 is fixed, and lower degrees are zero. Empty test schemes introduce no nonempty-cover assumption. Both new nodes and the item use the fixed small-skeleton convention so all families are indexed within the ambient universe.

I checked B--E of `coord/delivery-errors.md` against the files: the new nodes introduce every object, cite definition nodes, have statements only, correct Stacks tags and labels, searched blueprint references, and genuine logged Mathlib queries. All sources and cited statements were opened. `proof_deps` is precisely the union of the five steps' `uses`. No circular proof dependency was introduced; the server checks verify this. I reviewed the ordinary categorical Cech and general continuous/cocontinuous and Kan-extension search hits in their source files; they do not discharge the geometric/fibred hypotheses in one line. No service outage was described as absence. The new nodes' empty proof fields are intentional one-level splits, not unfinished work on this item. The five proof steps have all fewer than 1000 characters, so none hides a long-step subclaim. No Lean file or compiler was used.

## Not duplicates

lem-sfb-fibred-big-etale-abelian-functoriality vs def-sfb-adequate-moduli-space: the existing definition gives qcqs algebraic-stack power lifting to an algebraic-space target; the new statement gives generic abelian sheaf functoriality and no adequacy or power-lifting assertion.

lem-sfb-fibred-big-etale-abelian-functoriality vs def-sfb-stack-quasi-coherent-algebra: the existing definition fixes fppf structure algebras and a direct image to an algebraic space small-etale site; it does not assert abelian-sheaf functoriality between arbitrary fibred big-etale sites.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-fibred-big-etale-restriction-calculus: the existing statement concerns O-module restrictions to small-etale scheme tests and only asserts precomposition preserves module sheaves; it does not give the abelian compatible-family pushforward or its sheaf preservation.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-fibred-fppf-ringed-inverse-image: the existing statement concerns fppf structure modules and precomposition/tensor inverse image; the new statement concerns etale abelian sheaves and also the compatible-family direct image.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-fibred-fppf-space-module-comparisons: the existing statement is about structure modules, fppf ringed sites and small-etale algebraic-space tests; the new statement is about abelian presheaf functors and both directions of sheaf preservation on big-etale sites.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-space-big-small-ringed-comparison: the existing statement is a ringed big/small comparison for algebraic-space-represented categories and module test comparisons; the new statement gives arbitrary fibred big-etale abelian functors.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-stack-big-etale-derived-base-change: the existing statement assumes algebraic stacks and structure-module coefficients and gives exactness plus derived base change; the new statement gives abelian sheaf functoriality on arbitrary fibred groupoids, including compatible-family pushforward.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-stack-higher-image-fibre-cohomology-presheaf: the existing statement assumes algebraic stacks and structure modules and identifies higher direct images with sheafified fibre cohomology; the new statement gives functoriality for arbitrary fibred big-etale abelian sheaves.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-stack-qcqs-module-adjunction: the existing statement concerns a qcqs algebraic-stack morphism and a QCoh right adjoint on big fppf sites; the new statement concerns all abelian sheaves on arbitrary fibred big-etale sites.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-stack-quasi-coherent-scheme-restriction: the existing statement requires quasi-coherent structure modules and fppf ringed restrictions; the new statement allows arbitrary abelian sheaves on big-etale sites and asserts pushforward as well.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-stack-representable-module-injective-transport: the existing statement assumes algebraic stacks and concerns structure-module adjunction and injectives; the new statement gives abelian sheaf functoriality for arbitrary fibred groupoids.

lem-sfb-fibred-big-etale-abelian-functoriality vs lem-sfb-stack-test-fibre-restriction-injectives: the existing statement assumes algebraic stacks and is about structure-module restrictions to test fibres and injectives; the new statement treats arbitrary fibred groupoids and abelian sheaf pullback and pushforward.

lem-sfb-fibred-presheaf-pushforward-base-change vs lem-sfb-stack-big-etale-derived-base-change: the existing statement assumes algebraic stacks and structure-module coefficients and concludes derived base change; the new statement concerns arbitrary fibred groupoids and arbitrary abelian presheaves without a derived functor.

## Unfinished work

None on the assigned split. The two new statement-only nodes remain unsplit as required. The first dry run returned only the B9 ancestor mismatch described above; I repaired it by using exactly the required resolver output. Delivery validation follows.
