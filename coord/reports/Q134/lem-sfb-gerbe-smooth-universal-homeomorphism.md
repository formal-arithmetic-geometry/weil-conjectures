## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-gerbe-smooth-universal-homeomorphism.json: split into five explicit steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-neutral-gerbe-section-fppf.json: statement-only, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every step/node pair.

Attachments: none. The search by blueprint tag and by gerbe in lean/WeilConjectures returned no project declaration. No Lean was written or compiled.

WANTED: none. All proof sources were available locally.

The item was unsplit and contained doubled TeX backslashes in its decoded statement. I normalized those without changing the mathematics. Stacks 06R9's proof has two reversed map-direction typographical errors; the argument here consistently uses the map from the source point space to the target point space. Its omitted injectivity details are supplied in step 4. No hypothesis or conclusion was corrected or weakened, and no statement dispute arose.

The imported ancestry has blueprint.from.node = null, as confirmed by tools/blueprint_refs.py ancestor. I retained it and the full inherited via list; the new node extends that list by the item. The current latest blueprint proof det-thm-sf-ctf-stability-direct-images (3), and the unit and chapter records, were read. The inherited place describes this gerbe lemma's role in the downstream alteration/moduli branch; no unit or chapter route was changed.

Nothing mathematical remains unfinished at this level. The new section lemma remains unsplit by design.

## Searches

Whole-DAG searches for gerbe, neutral gerbe, 06QG, lemma-gerbe-with-section, classifying stacks, smooth quotient and fppf smooth descent were compared with the relevant statements. Whole-blueprint searches gerbe, gerbe with section and 06QG returned zero matches. The only other node carrying 06QG is the singleton-stack parent; its assertion is a finite-field universal-homeomorphism conclusion, not the fppf property of a neutral section. Project Lean contains no gerbe declaration. All Mathlib searches were made through msearch.py; searches.jsonl records the exact commands and hits. Two LeanFinder phrasings, Loogle, grep and LeanSearch were used for the item and the new lemma. Hits concern schemes, Zariski representability, ordinary group extensions, scheme covers or ordinary topological spaces; none specializes to this algebraic-stack section assertion in one line. The item retains its original search results as well.

## Not duplicates

lem-sfb-neutral-gerbe-section-fppf vs lem-sfb-singleton-stack-finite-field-homeomorphism: the new node asserts that a specified section of an arbitrary neutral gerbe over a scheme is representable and fppf; the existing node constructs a finite field quotient of a reduced singleton stack locally of finite type over a field and says nothing about the geometric properties of a section.

## Review by Q134

I read stacks-morphisms.tex 06QG (lemma-gerbe-with-section), especially assertion (3) and its final proof paragraph, for the new lemma. The assumption is an algebraic gerbe with an actual section; the base in the new statement is a scheme, which is a permitted special case of the source's algebraic-space base. The explicit scheme-test clause is exactly representability plus surjective/flat/local finite presentation, not an extra property. It asserts no smoothness of a stabilizer or section. This is a genuine auxiliary lemma, not the item's smoothness or topological conclusion.

For the item I read 06QE (base-change gerbe), 06QI (gerbe fppf), 06R9 (gerbe universal homeomorphism), 0DN8 (gerbe smooth), and the full argument of 0DLS (smooth quotient stack). I also read descent.tex 05B5 (lemma-smooth-permanence), spaces-descent.tex 0AHE, and the local project declaration's source-descent statement. Instead of introducing another node restating the item's smoothness clause, steps 2 and 3 perform the 0DLS source-descent diagram directly after choosing local gerbe sections. The quotient-stack equivalence itself is not used. The section fact is the only new input needed.

Step 1 uses the actual triple description in def-sfb-stable-pointed-moduli-groupoids and the algebraicity conclusion of lem-sfb-algebraic-stack-fibre-products. The latter explicitly applies to arbitrary algebraic stacks, so the product with an arbitrary test stack is legitimate. The fppf-site definition supplies jointly surjective families. Taking the residue field of a point on a nonempty cover member proves field-extension lifting without claiming a rational point over the original field. Base-change preservation of the gerbe condition is written out using its two local conditions.

Step 2 uses def-trf-algebraic-space's representable diagonal to make U_V a scheme. The atlas calculus gives its base changes and those of the neutral section; it only handles representable maps, and every use here is on an atlas, an algebraic-space map, or the new lemma's explicitly representable section. The gerbe condition supplies the covering and objects. The new lemma's exact conclusion gives W_i -> U_i surjective flat and locally finitely presented, while the atlas base change makes W_i -> V_i smooth. I checked both arrows and did not interchange them. Algebraicity of the gerbe base changes was already supplied in step 1.

Step 3 applies lem-sbc-smooth-flat-surjective-source-descent to schemes Z_i -> U_i -> V_i. Its hypothesis requires a merely fppf first arrow, exactly what step 2 and an etale chart of W_i give. The existing space-smooth-surjective-fppf-locality lemma requires a scheme target for covering descent; it is applied to V, which is a scheme. Thus smoothness descends to U_V, and the chart test gives U -> Q smooth for every atlas. The atlas calculus then gives flatness and finite presentation and its field-extension notion of surjectivity proves the composite surjective. This source-descent lemma is an off-unit generic tool declared in split_report.tool_uses, not a replacement unit route.

Step 4 uses the point-equivalence definition of lem-sfb-stack-point-topology-flat-lfp-open and the triple/isomorphism condition of def-sfb-stable-pointed-moduli-groupoids. After an isomorphism in the target over a common field, the two gerbe objects are in the same fibre. The gerbe's local-isomorphism condition is relative to that fibre, so its isomorphism is compatible with the selected target isomorphism. Choosing a residue field on a nonempty covering member yields the needed isomorphism in the fibre product. The argument proves injectivity on equivalence classes and does not assume an algebraically closed field or neutral gerbe globally.

Step 5 uses the actual continuity, atlas openness criterion, and openness of flat locally finitely presented algebraic-space-source maps in lem-sfb-stack-point-topology-flat-lfp-open. The map to which openness is applied is Z -> A, between schemes, not the nonrepresentable map of stacks. The atlas Z exists because the cited product lemma makes the base change algebraic. I wrote both inclusions in the inverse-image/image equality using representatives in a common field and a lift through the atlas, rather than assuming point spaces preserve fibre products. Atlas detection then proves openness on the arbitrary target stack. Continuity, bijectivity and openness give the homeomorphism by the explicit inverse-open argument.

I tested the identity gerbe, an empty base, a neutral gerbe BG with a nonsmooth flat locally finitely presented group (for example mu_p in characteristic p), and a gerbe which is only locally neutral. The nonsmooth example confirms why the section must not be called smooth. Empty targets make all lifting assertions vacuous and all homeomorphisms empty-to-empty. No step requires a field base, reducedness, Noetherian hypotheses, finite inertia, separation or a quasi-compact cover. A set-indexed covering family is used member by member, so no quasi-compactness or unjustified finite subcover enters.

Against delivery-errors B--E, I checked self-contained objects and definitions, source tags and labels, statement-only new-node shape, actual logged search texts, duplicate exclusion, exact statement-level citations, no clause moved to a new node, and the two descent hypotheses above. Every proof step is shorter than 2000 characters. I corrected an initial quotation using the shorter topology node's wording to quotations copied from the actual cited node; citations.json now contains each cited statement verbatim. The substantive changes were TeX normalization, the explicit two descent arrows, and completing the source's omitted injectivity argument. There was no previous sandbox split or report to reuse.
