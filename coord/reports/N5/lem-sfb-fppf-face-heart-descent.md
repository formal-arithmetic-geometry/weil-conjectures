# N5 stage-1 delivery: lem-sfb-fppf-face-heart-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fppf-face-heart-descent.json: item split into six explicit steps; original statement unchanged, prior searches retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-fppf-qcoh-descent.json: statement-only prerequisite, effective descent of arbitrary quasi-coherent modules and their morphisms along fppf coverings of algebraic spaces. Not a Mathlib leaf.
- citations.json: verbatim statement quotations for all 15 step/node citations.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, fppf descent, quasi-coherent hypercovers and cartesian modules found scheme descent and hypercover cohomology declarations, not the face-only ringed algebraic-space module assertion. In particular the scheme theorems in AlgebraicGeometry/Modules/DescentEffective.lean and FpqcFullyFaithful.lean do not have the item's objects and conclusion.

## WANTED

None. All mathematical sources used are present locally.

## Problems found and repaired

The imported item has no proof. Stacks 0DHD is an all-simplicial result, so merely applying it to a system indexed by injections would not justify the assertion. The replacement constructs the ordinary descent datum from the first three degrees. Degeneracies are used only as maps of algebraic spaces along which module equations are pulled back; their flatness and transitions along degeneracies are never assumed. No change of statement or unit route was necessary.

The inherited provenance's nearest-blueprint-node field is null; tools/blueprint_refs.py ancestor reports None. Its full inherited chain and precise place are retained; the new node adds the item to that chain. The current latest blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), is a high-level direct-image preservation argument, and does not itself state the remote algebraic-space hypercover prerequisites. Nothing in its fixed route is changed. The chapter and unit records were read; this supporting item is not their key statement, and no realization records were edited.

## Not duplicates

lem-sfb-space-fppf-qcoh-descent vs lem-trf-polarized-scheme-etale-descent: the latter descends polarized schemes, not arbitrary quasi-coherent modules on algebraic spaces along arbitrary fppf covers.
lem-sfb-space-fppf-qcoh-descent vs lem-trf-algebraic-space-invertible-descent: the latter is the rank-one case for etale scheme charts; this prerequisite requires arbitrary quasi-coherent modules and fppf algebraic-space covers, including covers of the matching relation.
lem-sfb-space-fppf-qcoh-descent vs lem-trf-polarized-fine-log-etale-descent: the latter descends fine log schemes with polarization, not arbitrary module descent data.
lem-sfb-space-fppf-qcoh-descent vs lem-trf-etale-scheme-line-morphism-gluing: the latter glues scheme morphisms and line maps along etale scheme covers, not arbitrary module objects along fppf algebraic-space covers.
lem-sfb-space-fppf-qcoh-descent vs lem-sfb-space-quasicompact-fppf-local: the latter descends quasi-compactness of morphisms, not module objects or compatible module maps.
lem-sfb-space-fppf-qcoh-descent vs lem-sfb-space-fppf-finite-affine-refinement: the latter constructs finite affine refinements, not effectivity of module descent.
lem-sfb-space-fppf-qcoh-descent vs lem-pc-fpqc-descent: the existing result has schemes as both covering members and base; the new statement is needed with algebraic spaces on the matching relation and with their small etale module categories.
lem-sfb-space-fppf-qcoh-descent vs lem-sfb-fppf-face-heart-descent: ordinary covering descent is a strictly smaller input; it does not contain a simplicial system, face-map reconstruction, the total ringed category or identification of its ordinary direct image. Steps 1--4 carry that reconstruction, and Steps 5--6 identify the actual right adjoint and adjunction maps.

## Mathlib and blueprint searches

All additional Mathlib queries were run with the mandated msearch.py; searches.jsonl records the actual responses. Each service answered. The new node records the exact query text and the names returned. The two semantic phrasings for ordinary fppf descent returned quasi-coherent-presentation constructors and scheme gluing. LeanSearch additionally returned CategoryTheory.Pseudofunctor.isEquivalence_toDescentData and fullyFaithfulToDescentData. I read IsStack.lean lines 45--74: the equivalence assumes the IsStack property for the particular pseudofunctor, which is the substantive missing module descent theorem here. Thus this is not a one-line specialization. I also read PushforwardContinuous.lean lines 372--390: pushforwardPushforwardEquivalence requires an equivalence of underlying site categories, which an fppf cover does not supply. The broader grep located these generic declarations at their actual source lines; the concept grep found no module fppf descent theorem. The item-specific semantic search returned scheme limit/gluing and one-hypercover section results, not this equivalence.

Whole-DAG searches used both statements and tags 04W8, 0DFQ, 0DHD and the expressions quasi-coherent/descent, descent datum and fppf. Whole-blueprint searches with tools/blueprint_refs.py included quasi-coherent, quasi-coherent descent, quasi-coherent modules, fpqc, fppf descent, 04W8, hypercover, total site and augmentation. None states the new algebraic-space covering theorem. Existing scheme descent, line descent, module pullback preservation, fppf covering calculus and enlarged etale models were opened and reused where their exact statements apply. In particular no second node for base change or composition of fppf covers was created.

## Review by N5

I read Stacks spaces-simplicial.tex, Tag 0DHD (lemma-descent-qcoh-for-fppf-hypercovering), including its proof through the big fppf site, and Tag 0D70 (lemma-augmentation-site)'s compatible-family construction. The new input is spaces-descent.tex Tag 04W8 (proposition-fpqc-descent-quasi-coherent), whose statement gives both effectivity and full faithfulness for algebraic spaces; spaces-topologies.tex Tag 0DFQ explicitly says fppf covers are fpqc. I read that definition and proof too: no quasi-compactness hypothesis on the original morphism is needed. Thus the new statement is faithful to the source and not an attempt to apply the scheme-only 023T node to an algebraic space.

For Step 1 I checked the statements of semisimplicial-ringed-total-category and space-module-pullback-quasicoherent. The former really supplies coherent module transitions and component pullback; the latter preserves quasi-coherence for arbitrary morphisms. Their stated hypotheses hold for the chosen enlarged ringed models. Cancellation gives the triangle equation. Pulling it back to a twice-degenerate vertex produces an invertible idempotent, hence identity, even for non-flat degeneracies.

For Step 2 the covering-calculus statement explicitly supplies base change of fppf covers. The proposed boundary has vertices (x,y,y), edges 01=a, 02=b and 12=e(y), so its endpoints match. Its pullback of U_2 is a cover. The new descent statement gives uniqueness of maps along this cover, then descent of t and its inverse along U_1 over the relation. The pullback-preservation statement supplies quasi-coherence of the two vertex modules on every space in this argument. This verifies C4 rather than treating a definition of flatness as a descent theorem.

For Step 3 I verified that M_2 is exactly the product over the triple vertex space of the three edge-cover base changes; this follows from the stated matching-object definition, not a global choice of fillers. Covering calculus therefore applies twice, and full faithfulness in the new descent statement detects the cocycle equality. Its effectivity clause then applies to q_0, which is flat, locally finitely presented and surjective by the item's hypothesis. The resulting b_0 induces theta, as required by the conclusion of that clause.

For Step 4 I checked the system statement for compatibility of component morphisms. Every pair of vertices spans an injective edge; their two formulas agree by theta, and composition gives the square for each injection. Ordinary full faithfulness descends the degree-zero map; the higher maps are forced by the invertible vertex transitions. Thus this step contains an assembly proof, not an application of a new node restating the face-only assertion.

For Step 5 I opened the general ringed-topos module-adjunction statement and checked its tensor and ring-map conventions against the enlarged-etale-model statement. It gives Hom bijections for every ambient module N, not just quasi-coherent N. The equalizer represents exactly maps with degree-one compatibility; the written vertex construction proves all higher compatibilities. This direct universal-property argument identifies the ambient right adjoint, avoiding an unjustified inference from an equivalence of full subcategories to a statement about ordinary pushforward. The enlarged-model statement identifies direct-image evaluation by fibre products, with the canonical ring maps used here. This is the sole generic adjunction tool from another unit, declared in split_report.tool_uses.

For Step 6 the descent theorem applies after etale base change V and after base change of r, by covering calculus. It supplies full faithfulness for maps from the structure module to G; the elementary map/section identification is written out, so no Yoneda-full-faithfulness node is misused for a section formula. This recovers sections of G with their restrictions and scalar operations. The resulting map for u^*G is exactly the unit. The triangle identity, followed by naturality along the constructed system isomorphism, gives the actual counit on every object of A.

I tested the empty base (only empty source spaces, unique module), the identity constant hypercover (edge automorphism is an invertible idempotent and therefore identity), an ordinary Cech nerve (the construction recovers the usual descent cocycle), non-quasi-compact fppf covers (the source theorem allows them), arbitrary infinitely generated modules (no finite presentation is used), and non-flat degeneracies (only equation pullback is used). Every non-elementary input has a node and every citation is backed by its full verbatim statement in citations.json. All six steps are shorter than 2000 characters after TeX normalization; the comparison in Step 5 is explicitly proved by a natural Hom bijection and the vertex formula. No lemma is hidden behind a long-step assertion.

## Unfinished work

None for this one-level split. The new node intentionally remains statement-only and unsplit, for a later worker. No Lean was written or compiled, no agent was started, and all writes were confined to this sandbox.
