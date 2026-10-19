# Stage-1 report: lem-per-birational-isomorphism-dense-open

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-birational-isomorphism-dense-open.json: item, statement unchanged, split into three proof steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-birational-common-dense-opens.json: new statement-only lemma, Stacks 0BAC alternative (2), unsplit; five logged Mathlib searches, no match.
- citations.json: one verbatim statement quotation for each node used in each item step.

## Attachments

None. Searches of WeilConjectures/ and Comparator/ by the item tag, birational/dense-open wording and Birational found no project declaration stating this item. The only Birational hits were imports; master is reference material only.

## WANTED

None. All source arguments used are available in literature/stacks-project/.

## Audit and corrections

The item statement matches Stacks 0BAJ in the separated, locally-of-finite-presentation alternative, including the generic local rings rather than merely residue fields. It is unchanged. No source or statement dispute was found. Its original proof was empty. This is a technical scheme input beneath the normal-modification node; the chapter and unit records were read and no unit step or realization was altered.

I used the freedom below the unit level in SETUP.md: the separated case of 0BAJ has a shorter proof from its input 0BAC. The source reduces to a finite map before removing a closed complement. Here separatedness already makes the inverse of the common-open isomorphism a closed section. The section image is dense, so there is no complement. This avoids creating generic-fibre and generic-finiteness nodes and still proves the stronger saturated-inverse-image conclusion of the item.

Mathlib searches ran through msearch.py and are retained in searches.jsonl. I read the hits. PartialIso and Birational in Mathlib/AlgebraicGeometry/Birational/Birational.lean only package isomorphic dense opens; they do not construct them from generic local-ring maps. IsLocalIso describes a map locally isomorphic everywhere. OpenImmersion.of_isIso_stalkMap assumes an open embedding. The spreading lemmas require germ-injectivity hypotheses not present for arbitrary nonreduced schemes here. No returned declaration states 0BAC or 0BAJ under these hypotheses. The Loogle query Birational, IsIso reports an unknown identifier; it is recorded faithfully, and the later fully qualified Loogle query succeeded with zero hits. No unavailable service has been reported as evidence of absence.

## Not duplicates

lem-per-birational-common-dense-opens vs lem-trf-birational-quasi-modification-common-cover: the existing node mentions 0BAC only inside its proof; its statement constructs a common proper refinement from a valuation cover of reduced qcqs schemes. It does not state the common-open consequence of generic local-ring isomorphisms for a single possibly nonreduced lfp morphism.
lem-per-birational-common-dense-opens vs lem-sbc-affine-birational-fraction-ring-equiv: the existing node assumes integral affine schemes and a compatible fraction-field isomorphism; 0BAC allows nonreduced and reducible schemes and uses generic local rings of a given morphism.
lem-per-birational-common-dense-opens vs lem-sbc-generic-fibre-partial-iso-spread-open: the existing node assumes an integral affine base and an already supplied partial generic-fibre isomorphism of two affine families; it neither supplies the generic-fibre isomorphism from a birational morphism nor gives opens dense in both original schemes.
lem-per-birational-common-dense-opens vs lem-per-birational-isomorphism-dense-open: the new node requires no separatedness and gives two common dense opens, not the full inverse image of a target open. The additional closed-section and density argument is exactly what proves the item's stronger conclusion. The new node is Stacks 0BAC, not a relabelling of 0BAJ.

Whole-DAG searches used 0BAC, lemma-birational-birational, birational, common dense opens and generic local-ring terminology; blueprint_refs.py searches for 0BAC, birational, generic local ring and dense open isomorphism found no blueprint statement matching the new node. Existing normalization statements concern a particular morphism and do not generalize it. The blueprint ancestor is lem-per-artin-gabber-affine-curve; from.via is the item's existing chain with the item prepended. The new node has a statement only, with all notions explicitly cited.

## Review by Q45

I read morphisms.tex, section Birational morphisms, especially the statements and complete proofs of 0BAC and 0BAJ, and schemes.tex lemma-section-immersion (01KT) and separated-permanence (01KU), with the tag table open. The 0BAC statement explicitly permits locally finite presentation without target reducedness. Its finite-generation-and-relations argument is the source of the new statement-only node; no argument is smuggled into that node's statement. The source's base S is harmless: taking S=X with the identity target structure gives precisely the restricted given morphism, not an unrelated abstract isomorphism.

For Step 1 I reread the new node: it supplies both dense opens and the fact that the isomorphism is the restriction of f, with every birational hypothesis identical to the item's. The open-immersion definition identifies open subschemes with restricted structure sheaves, so U factors as the stated open inclusion into W=f^{-1}(V). Step 1 does not assert U=W.

For Step 2 I opened and read the statements of lem-weil-pbc-separated-lqf-base-change and lem-weil-pbc-section-separated-closed-immersion. The former clause (1) has arbitrary base change and needs no quasi-finiteness; I use only that clause for the restriction along V to X. The latter takes exactly a separated map and a right inverse. The formula s=j composed with g^{-1} satisfies p composed with s=id_V. It is a closed immersion with underlying image U; the closed-immersion definition explicitly says its underlying image is closed. Thus the cited statements really give closedness in W, not merely closedness of a different morphism or in the original Y. The base-change lemma is declared as an off-unit generic tool; the section lemma is already a Mathlib leaf. No perverse-unit route is replaced.

For Step 3 I checked the elementary topology directly. U is contained in W and dense in Y. Because W is open in Y, every nonempty relatively open subset of W is open in Y and intersects U. Closedness in W then forces U=W as subsets. This is an equality of open subschemes since both have the restricted structure sheaf of Y; it is not an inference that a surjective closed immersion is an isomorphism (which would be false for nonreduced schemes). Therefore the restriction of f to its entire inverse image really is the isomorphism g. Each step is under 2000 characters and hides no additional lemma. All proof dependencies are precisely the union of step uses, and each quotation in citations.json is copied from the corresponding statement.

I tested the empty case (birationality forces both component sets empty, so both schemes are empty), identity maps on arbitrary nonreduced schemes, disjoint finite unions of components, and a cusp normalization (discard its singular point). For the new lemma I also checked the doubled-origin line: one chart can be isomorphic to the entire target while not being the entire inverse image, illustrating why 0BAC has a genuinely weaker conclusion. The doubled-origin map is not separated and cannot be used at Step 2. Nonreduced schemes are retained throughout; no reduction, normality, Noetherian hypothesis, quasi-compactness or integral-base hypothesis was silently added. The section tag was initially misidentified while drafting and corrected to 01KT against tags/tags before delivery. No SGA source, Lean edits, compiler, Lake or live-project writes were used.

## Unfinished work

The item is fully split by one level. The one new non-elementary lemma is intentionally unsplit, with its exact source and logged searches, for a subsequent worker.
