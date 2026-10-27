# Q160: lem-sfb-stack-higher-images-flat-comparison

## Files written

The item in dag/nodes/sec-six-functors-basics/lem-sfb-stack-higher-images-flat-comparison.json is split in seven steps, with its statement unchanged. Added the injective-resolution definition to its statement dependencies.

Five new statement-only nodes in the same directory, all unsplit, none Mathlib leaves:

- lem-sfb-stack-smooth-descent-higher-image-criterion: the general smooth-descent criterion of Stacks 076Z, for an arbitrary weak Serre system.
- lem-sfb-stack-lqc-flat-comparison-local-structure: weak Serre closure, pullback stability and smooth detection; 06WL, 06WM, 075Y, 0764.
- lem-sfb-stack-representable-derived-restriction: the canonical derived comparison 075P, including exact restrictions and its natural comparison maps.
- lem-sfb-stack-representable-higher-image-restriction: the cohomology consequence of that derived comparison, retained separately according to the derived-form rule; its only substantive proof dependency is the derived node.
- lem-sfb-stack-lqc-lfp-topology-comparison: 076T and 075R under the weaker flat-locally-finitely-presented comparison assumption, including comparison-morphism acyclicity and higher-image sheafification.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, locally quasi-coherent, algebraic stack and flat comparison terminology. No declaration supplies this statement. The similarly named pro-etale comparison-flatness theorems concern a different site and constant coefficient category. Read also the generic scheme module and site search hits; these are not attachments for a theorem on structure modules on the big site of arbitrary algebraic stacks.

## WANTED

None. The Stacks TeX sources used are present. Read the current blueprint only under literature/blueprint/latest, particularly sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof. The inherited ancestry is a generic stack-cohomology prerequisite below the scalar-section/moduli branch; no chapter or unit record is changed. blueprint_refs.py ancestor returns None for this inherited chain; new from.node fields retain that result and prepend the item to via.

## Issues and corrections

There was no prior split or report in the sandbox, only searches.jsonl. Read all 25 inherited search results and reused them rather than issuing the same questions again. Ran fresh item searches and searches for the separate higher-image restriction obligation. The original item's source and assertion are correct, including no Noetherian or finite-generation assumption. Its statement was not corrected or weakened.

The tempting direct citation of 0765 would restate an item's clause. Instead the proof checks the affine hypothesis of 076Z using three existing algebraic-space results. Positive degrees vanish in that affine case, so no new general flat higher-base-change theorem is needed. The existing degree-zero result requires separatedness; our affine morphisms satisfy it. The topology comparison alone supplies fppf sheafification, not identity with the original etale sheaf; this distinction is explicit in Step 6.

The derived representable restriction remains an unsplit obligation, with the per-degree consequence separate. No claim is made that restriction preserves module injectives: the source explicitly warns that this is false. The derived comparison can instead use 075N's derived composition and exact restriction argument.

## Not duplicates

lem-sfb-stack-smooth-descent-higher-image-criterion vs lem-sfb-stack-higher-images-flat-comparison: the new statement is a conditional theorem for an arbitrary system of subcategories; the item must establish its hypotheses for locally quasi-coherent flat-compatible modules.

lem-sfb-stack-lqc-flat-comparison-local-structure vs lem-sfb-stack-higher-images-flat-comparison: local structure asserts closure, pullback stability and smooth detection, with no higher direct-image preservation assertion.

lem-sfb-stack-representable-derived-restriction vs lem-sfb-stack-higher-images-flat-comparison: representable restriction is a canonical derived comparison for arbitrary modules under representability, not preservation for arbitrary qcqs stack morphisms.

lem-sfb-stack-representable-higher-image-restriction vs lem-sfb-stack-representable-derived-restriction: this is the separately required cohomology consequence of the derived form, including the specified comparison maps; it is linked only to that derived node as proof dependency.

lem-sfb-stack-lqc-lfp-topology-comparison vs lem-sfb-stack-higher-images-flat-comparison: the new statement needs only lfp-flat comparisons, imposes no qcqs condition on the pushforward morphism, and gives sheafification rather than preservation or equality of underlying higher-image presheaves. It also gives the derived acyclicity of the comparison morphism. The argument must first prove that the etale images themselves are fppf sheaves.

lem-sfb-stack-lqc-lfp-topology-comparison vs lem-sfb-stack-flat-scalar-sections: the existing result is a degree-zero scalar-extension isomorphism for sections of a quasi-coherent algebra over an affine base; the new statement compares two topologies for general locally quasi-coherent modules.

No existing node stating the five new obligations was found by whole-DAG statement/source searches for 076Z, 0764, 075Y, 06WL, 06WM, 075P, 075R, 076T, and the associated labels and concepts. Whole-blueprint searches for flat comparison, locally quasi-coherent, general pushforward, representable morphism cohomology and tags found no equivalent blueprint node. Incidental occurrences of these four-character strings in unrelated sources or Mathlib search output do not state the corresponding Stacks fact.

lem-sfb-stack-lqc-flat-comparison-local-structure vs lem-weil-pbc-flat-local-completion-iso: the existing source contains line number 10764 (not a citation of Tag 0764) and its statement concerns an isomorphism of completions for flat unramified local ring maps; it has no statement about closure or locality of stack module sheaves.

## Unfinished work

The five new obligations are intentionally left statement-only for later stage-1 workers. This delivery provides the full one-level split of the dispatched item. No Lean code or compilation was performed, and no repository or launcher file was edited.

## Review by Q160

I read the proof of 0765 and the relevant clauses and proof of 0771 in stacks-cohomology.tex. I also read 076Z's actual four hypotheses, 075Y's smooth detection argument and 0764's first three properties. For the local-structure obligation, I checked 06WL and 06WM in stacks-sheaves.tex: the former is precomposition preservation and the latter gives the weak Serre closure needed here. Their intersection has precisely the properties stated in the new node. The zero module and the identity cover pass as small cases; there is no requirement of Cartesian comparisons for nonflat arrows.

For Step 1 I opened both new cited statements: the closure/locality node gives the first three hypotheses, while the criterion still requires the affine calculation. Thus this is not an application of a disguised copy of the item. For Step 2 I read the existing Zariski-etale quasi-coherent equivalence, algebraic-space higher-image quasi-coherence, and affine-spectrum fibre-product statements. Local quasi-coherence gives the associated Zariski module on every test scheme; the equivalence turns it into the small-etale quasi-coherent module the space theorem actually assumes. The product is a scheme, and affineness is explicit on tensor-product charts. Inverse images of affine opens are affine; multiplication on the tensor square is surjective, giving the closed relative diagonal and hence separatedness. Nothing assumes that an arbitrary intersection of affine opens is affine.

For Step 3 I read the full chartwise calculus statement, which includes arbitrary flat base change even for scheme morphisms. It therefore supplies flatness of e, without requiring b to be locally finitely presented. I read 075P, the preceding 075N module proof and 075H's canonical comparison. The representable derived obligation states an isomorphism in the module derived category; its separate higher-image statement gives the exact restriction formula and identifies the map with the usual base-change map followed by the coefficient comparison. This is what Step 3 uses, not just equality of isomorphism classes. I checked that the coefficient comparison is an isomorphism from the given flat compatibility of M.

For Step 4 I opened both existing space statements. The flat direct-image result supplies the ordinary adjunction-mate map only in degree zero, and requires a quasi-compact separated map, which a-prime is. The affine module higher-image vanishing is genuinely about injective resolutions in module sheaves, not merely additive sheaves; it applies to both a and a-prime and every positive degree. Hence the positive-degree comparison is a map between zero modules. This eliminates the need for a stronger new algebraic-space cohomology base-change node. Empty sources, zero coefficients, non-Noetherian base rings and infinite-rank quasi-coherent modules satisfy the same argument; for identity b the comparison specializes to identity.

For Step 5 the general criterion now has all four premises, and the original f has exactly its qcqs hypotheses. For Step 6 I read 076T and every clause used from 075R. The new topology node deliberately assumes only flat-lfp comparisons, weaker than the hypothesis on F and on the images from Step 5. Its fppf-sheaf conclusion applies separately to every image. Its sheafification conclusion then identifies the two computations canonically, preserving restriction maps and therefore the c_a maps. It would be incorrect to skip the second application to the higher images, and I checked that it is present.

For Step 7 I opened the injective-resolution definition. Exactness of the augmented resolution and the objectwise kernel of compatible section families give the degree-zero identification in the elementary argument written there. No theorem that direct image preserves arbitrary cokernels or arbitrary base change is used.

For each new node I checked the displayed objects are introduced, the site is the big etale site on all test schemes rather than the lisse-etale site, and the coefficient is the structure module rather than a fixed constant ring. I read the saved Mathlib hits: quasicoherent local presentations, scheme module pushforward, scheme flatness and fppfTopology do not prove any of the stack-specific statements; the general IsSerreClass is a stronger closure predicate and supplies no stack-descent theorem. A second phrasing was tried for every search question. Every recorded query occurs in searches.jsonl, with service successes and their actual top hits retained. All sources are Stacks; no excluded SGA route is used. The original statement is unchanged, all new nodes are smaller general tools or the explicitly mandated derived/cohomology pair, and none is elementary. Every proof citation has a verbatim statement quote in citations.json. I checked that no new step exceeds 2000 characters and no cited existing node reaches the dispatched item, so these citations introduce no cycle.
