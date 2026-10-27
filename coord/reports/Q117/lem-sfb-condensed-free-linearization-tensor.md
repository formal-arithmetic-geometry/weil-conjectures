# Stage-1 report: lem-sfb-condensed-free-linearization-tensor

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-free-linearization-tensor.json: split, seven proof steps; no full Mathlib match.
- citations.json: 21 entries covering every use of a node in every step, quoted verbatim from its live statement.
- report.md: this report. searches.jsonl contains the actual search command log; write_split.py is a sandbox-only authoring aid.

Zero new nodes, zero new Mathlib leaves. Nothing was written to Lean, the shared repository or launcher files, and no compiler or build was run.

## Attachments

None. Searching WeilConjectures for the exact blueprint tag found no declaration. Concept searches found SheafOfModules.freeTensorFreeIso in WeilConjectures/Algebra/Category/ModuleCat/Sheaf/MonoidalFree.lean:61, but its indices are finite constant types, not condensed sets with variable section sets. It does not state this item. The related ordinary free-module and free-module-presheaf declarations are components only.

## Literature and searches

I read the chapter sec-six-functors-basics and the recorded unit sk-thm-sf-ctf-stability, together with its current main-20261015 _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The item supplies the extracted formal bar input below paragraph (3), open direct image; the blueprint itself does not prove this auxiliary assertion. Therefore proof_origin.by is agent. The ancestry contains a null blueprint.from.node; tools/blueprint_refs.py ancestor confirms this, and I preserved it and its full via chain.

I read Stacks sites-modules.tex, Tag 03CY (lemma-sheafification-presheaf-modules, lines 815 onward), Tag 03EK (section-tensor-product, lines 3550 onward), Tag 0GMW (lemma-sheafification-tensor, lines 3606 onward), and Tag 04BL (lemma-universal-module, free-sheaf construction in its proof, lines 5950 onward). The tags were checked against tags/tags. These sources give the module sheafification, the presheaf tensor, its comparison with sheaf tensor, and the free-module-sheaf model. The existing internal-to-section comparison provides the internal relative tensor bridge; I did not attribute that bridge to 03CY alone. No SGA source is used. No WANTED document.

Before considering new nodes I searched the whole DAG for free-module, tensor, presheaf, internal-section comparison, 03CY and 0GMW statements, and ran blueprint_refs.py searches for free linearization, sheafification tensor, free, internal section tensor and 0GMW. The free-sheaf universal-property search found the already reviewed lem-trf-free-module-sheaf-universal-property; the tensor searches found the already reviewed lem-pe-internal-section-tensor-comparison and lem-pc-sites-module-sheafification-tensor. I opened each full statement and checked their dependency closures do not reach this item. Thus no helper needs to be created.

For the item I ran msearch.py LeanFinder with two different phrasings, Loogle, LeanSearch and grep. All services answered; the exact queries and returned names/files are recorded in the item and searches.jsonl. I read Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean:148-198 (the ordinary free-module tensor comparison), Presheaf/Free.lean:40-123 (free presheaf and adjunction), Sheaf/Free.lean:40-64 (constant-type indexed free sheaf), and Condensed/Light/Monoidal.lean (ordinary coefficient-ring monoidality). The ordinary comparison supplies a sectionwise formula, the presheaf declaration supplies no sheafification/internal identification, and LightCondensed.free assumes an ordinary ring. None is the whole item or its one-line specialization. Previous item searches are retained; the new queries were actually run and read.

## Corrections and scope

No mathematical statement dispute was found. I corrected doubled TeX escapes in the imported statement and explicitly cited the ordinary free-module notion, section-module tensor definition and the specified internal-section tensor comparison already used in its wording, adding their statement dependencies. No hypotheses or conclusions changed. The current item had an empty proof and no Lean audit entry; the missing audit information was treated as no matching declaration, then checked by source search. The old search history and created/blueprint/source fields are retained.

The assembly uses three general tools outside the item's unit: the free-sheaf universal property (trace-formula chapter), the internal-section monoidal equivalence (pro-etale coefficients), and tensor/sheafification (Picard framework). Each is declared in split_report.tool_uses with its role. None imports the original chapter's proof route: their statements concern arbitrary small sites, sheaves and modules. I did not write the maintainer-only top-level tool_uses field. No imports were edited. No old proof dependency had to be removed because the item's old proof_deps was empty.

## Not duplicates

No new nodes. Existing generic statements are cited directly. In particular, the finite-basis lemma lem-sc-tensor-product-free-basis would not handle arbitrary X(S), and the normalized free-module comparison calculus concerns transport under another functor, not the internal-module tensor identification. This split proves the remaining assembly and coherence, rather than recreating those statements as helpers.

## Review by Q117

I checked delivery-errors B through E against the item and cited statements, not just their titles. There are no statement-only children needing a separate source or search record; the item retains all objects and hypotheses, and all TeX commands have single escaping after JSON decoding. Every proof step is under 2000 characters. The finite-sum arguments remain explicit elementary steps, rather than unnecessary nodes.

Step 1 uses the free-module-sheaf universal property, whose statement gives the generator bijection, its finite-sum inverse and naturality for an arbitrary small site and commutative ring sheaf. The module-sheafification definition explicitly gives the required unique linear factorization. Our A is a ring sheaf and X a set sheaf on the fixed small site, so these hypotheses hold. I read the source for both (04BL and 03CY).

Step 2 uses the fixed free internal adjunction, the underlying-sheaf-preserving equivalence and the normalized uniqueness clause of the free-sheaf statement. The adjunction node explicitly specifies its unit; the equivalence preserves section groups, restrictions and maps, so its generator map is the same underlying natural transformation. Full faithfulness and essential surjectivity are the defining properties of an equivalence, and the proof explicitly passes to all section-module targets. The unique comparison is chosen to carry this unit to the actual sheafified basis map. Its inverse identities are checked by the injectivity of the same representing bijections. No unrelated choice of free functor is substituted.

Step 3 uses the adjunction's functorial generator map, the free-sheaf bijection and the equivalence's unchanged underlying maps. The step spells out why all generalized generators, rather than global sections or sections of a falsely sectionwise-free sheaf, detect equality. Naturality in u is tested on those generators.

Step 4 uses only the ordinary free-module basis definition and the tensor universal property, which explicitly says pure tensors generate and balanced bilinear maps extend uniquely. I wrote both finite-sum formulas and their inverse identities; commutativity of A(S) is needed for balancing and is present. Restriction maps are semilinear, and can merge basis elements: grouping equal images in a finite sum respects both formulas, so no injectivity or flatness is assumed. The same calculation handles maps of X,Y. This is the elementary algebraic counterpart mentioned by 03EK, not an uncited theorem about sheafified sections.

Step 5 cites the actual tensor/sheafification theorem, not its definition, and the actual internal-section monoidal comparison, not merely the equivalence definition. The former allows presheaves over a presheaf ring, so it applies to F_X,F_Y; since A is a sheaf its sheafified ring is canonically A. The latter explicitly identifies the coequalizer tensor with section-module tensor and characterizes its map on local pure tensors. Its universe bound and monoidal-local-equivalence assumptions hold on the fixed small site with the sheaf tensor structure already assumed in the item. The displayed chain spells out each comparison; full faithfulness transports both inverse maps. The comparison is normalized on local pure tensors, so it agrees with the prescribed generators.

Step 6 checks the singleton basis isomorphism before sheafification, then uses the unique factorization to identify the sheafification of the sheaf A with A. The regular-module comparison in the internal-section theorem supplies its internal interpretation. The unit sends the fixed basis generator to 1 and not a freely rescaled generator.

Step 7 uses the specified associator/symmetry/unitor definitions and the comparison theorem's explicit coherence clause. I wrote the value of both paths in each diagram, including all three factors for associativity and the two unit equations. Iterating the already proved product-tensor isomorphism makes these tensors into the generalized generators of a free object, so step 3 detects equality. Uniqueness through sheafification justifies comparison of presheaf maps with the sheaf maps, without claiming the unit is surjective on sections. No extra coherence lemma or unproved transport identity is hidden here.

Small cases checked: A=0, a singleton or empty basis set at an object, infinite X(S), restrictions identifying distinct generators, either factor the initial set sheaf (whose empty-object sections need not be empty before sheafification), the terminal sheaf, and three-factor tensors. The formulas respect finite support in all cases. No projectivity, discreteness, finite rank, sectionwise freeness after sheafification or flatness hypothesis is used. There is no new dependency cycle and no new node restating a clause of the item.

## Completion

All seven steps and every citation are complete. No mathematical work was left unresolved; the required remote dry run and delivery determine acceptance mechanically, followed by the maintainer's independent review.
