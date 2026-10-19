## Worker report

Files written:

- dag/nodes/sec-deligne-laumon-a1/lem-per-completed-affine-localization-diagram.json: statement retained; eight proof steps and their exact dependency union; blueprint provenance retained and split report added.
- dag/nodes/sec-deligne-laumon-a1/lem-per-affine-support-cech-localization.json: new statement, unsplit; no Mathlib match. This is the canonical derived ideal-torsion/open-section localization theorem on arbitrary Noetherian affine schemes.
- dag/nodes/sec-deligne-laumon-a1/lem-per-derived-completion-finite-cohomology.json: new statement, unsplit; no Mathlib match. This is the finite-cohomology completion formula, with its canonical unit and finite-module consequence.
- citations.json: a verbatim statement witness for every citation in every proof step.

Attachments: none. Exact blueprint-tag searches and local-cohomology/completion notion searches in WeilConjectures/ of the read-only slopmaster2 checkout found no declaration of the item or either new theorem. I read Mathlib/Algebra/Homology/LocalCohomology.lean, including its explicit future-work list: the right-derived and Cech comparisons are not provided there. The finite-module ordinary-completeness declaration already belongs to lem-weil-pbc-finite-module-complete-over-complete-noetherian and is reused by its existing node.

WANTED: none. Every source used is present locally.

What required work: the imported node had an empty proof, although its statement already distinguished canonical derived-functor maps from arbitrary cone lifts. The source proof of 0DXQ writes the triangles but suppresses the diagram construction. I expanded the quotient-level support comparison, the direction of the invertible support map, the middle-term identification through the actual completion unit, the connecting square, and the restriction equation. No target or item statement was changed. The source's dualizing-complex and depth hypotheses serve its algebraization conclusion and are not used in the preliminary localization construction proved here.

An initially considered third helper, exactness of derived completion, was not created: the existing strict-diagram K-flat replacements, K-flat cone closure and exact strict-tower Rlim theorem give it by the cone calculation in step 4. Its exploratory searches remain in searches.jsonl and the search output files. No search is claimed unless it was run; the new nodes carry their exact query strings and full recorded outputs, including both semantic phrasings. All five searches for each new node succeeded; none was reported unavailable.

Nothing remains unfinished within the one-level split. The two new inputs intentionally have no proof steps. No Lean file, compiler, Lake command, live node, launcher file or shared repository git command was used.

## Searches and blueprint route

I read the chapter and unit records and the imported ancestor lem-per-artin-gabber-affine-curve. The item's existing ancestry passes through the formal-sections comparison used for complete-local connectedness in the potential-dualizing construction. This split makes that same input precise; it does not replace the unit's Fourier/perverse route. The new blueprint.from.node is lem-per-artin-gabber-affine-curve and via prepends this item to its inherited chain.

Whole-DAG concept and source searches included 0A6T, 0955, 0956, 0A6W, 0922, 0A06, localization triangles, Cech models, finite-module completeness and completion exactness. Whole-blueprint searches via tools/blueprint_refs.py included 0A6T, 0A06, 0922, 0955, local cohomology, completion functor, adic completion, derived completion, affine localization, finite cohomology and Cech complex. None supplies the new theorem as stated. The punctured unit-module comparisons and scalar ordinary-completion facts are insufficient for arbitrary derived coefficients and canonical triangle maps. Existing generic resolution and Rlim results are cited, rather than copied into a new completion-exactness node.

The off-unit generic tools are declared in split_report.tool_uses for maintainer review: diagram K-flat replacements, K-flat cone closure, strict-tower Rlim, bounded flat module complexes, and localization flatness. Each supplies only homological or ring-theoretic calculus. The closed finite-module completeness result and the Mathlib cohomology-sequence leaves need no route exception.

## Not duplicates

lem-per-affine-support-cech-localization vs new-punctured-restricted-abelian-functor: defines the restricted tilde-to-abelian-sheaves functor and its zero maps, without any derived support triangle.

lem-per-affine-support-cech-localization vs lem-sbc-punctured-h-one-derived-torsion: only identifies degree-one sections of the structure sheaf with degree-two maximal-ideal torsion on a local puncture; it has no arbitrary ideal, coefficient complex or natural triangle.

lem-per-affine-support-cech-localization vs new-punctured-tilde-sections-comparison: compares two ordinary section complexes after forgetting module scalars, without derived torsion or the supported triangle.

lem-per-affine-support-cech-localization vs new-punctured-flasque-resolution-comparison: compares abelian cohomology of the structure sheaf with one injective-resolution section complex, without arbitrary coefficients and support inclusions.

lem-per-affine-support-cech-localization vs lem-sbc-punctured-injective-restriction-exact: is the kernel and surjectivity assertion for one injective module on a maximal-ideal puncture, not the full derived support triangle or arbitrary supports.

lem-per-affine-support-cech-localization vs def-sbc-ideal-power-torsion-cocomplex-inclusion: defines the torsion subcomplex inclusion and asserts only its monomorphism, not the localization comparison.

lem-per-affine-support-cech-localization vs lem-sbc-depth-three-puncture-h-one-comparison: is a vanishing implication for degree-one structure-sheaf cohomology from local Ext colimits, not a canonical derived triangle.

lem-per-affine-support-cech-localization vs lem-sbc-punctured-flasque-resolution-cohomology: computes cohomology of the unit structure module from one injective resolution, with no arbitrary coefficient complex or support map.

lem-per-affine-support-cech-localization vs new-punctured-tilde-resolution-exact: is an augmented sheaf resolution before taking sections, without local cohomology, a triangle or its canonical maps.

lem-per-affine-support-cech-localization vs lem-sbc-punctured-injective-quotient-cohomology: identifies the cohomology of one structure-sheaf puncture with an injective torsion quotient; it does not give the arbitrary-ideal derived triangle.

lem-per-affine-support-cech-localization vs lem-sbc-punctured-sections-torsion-quotient: is a chain isomorphism for the unit module and maximal-ideal puncture, explicitly not a sheaf-cohomology comparison.

lem-per-affine-support-cech-localization vs new-punctured-kernel: computes only the kernel of ordinary punctured restriction on a module.

lem-per-affine-support-cech-localization vs lem-per-local-cohomology-flat-base-change: only concerns flat ring maps and individual cohomology modules; this delivery uses derived reduction modulo possibly nonflat I-powers and a natural triangle.

lem-per-affine-support-cech-localization vs lem-per-algebraic-local-duality: is the Matlis/dualizing-complex Ext duality theorem, with no affine localization triangle.

lem-per-affine-support-cech-localization vs lem-per-local-cohomology-cech-bound: computes individual cohomology modules for a module in degree zero; it does not identify derived functors on arbitrary complexes, the open term, or the support/restriction triangle morphism.

lem-per-affine-support-cech-localization vs lem-per-ideal-torsion-cech-computation: likewise computes cohomology of an augmented localization complex for a module, not the canonical derived support triangle for arbitrary complexes and inclusions of supports.

lem-per-affine-support-cech-localization vs lem-per-local-cohomology-sum-spectral: is the spectral sequence for composition of torsion functors, not the supported/open localization triangle.

lem-per-affine-support-cech-localization vs lem-per-completed-affine-localization-diagram: the new input is the ordinary affine localization triangle for arbitrary Noetherian rings and complexes, with no completion ideal, completeness, finite-module hypothesis or comparison to a second support; the item combines it with completion and proves the diagram.

lem-per-derived-completion-finite-cohomology vs lem-per-completed-affine-localization-diagram: the new input computes derived completion of complexes with finite cohomology for arbitrary Noetherian rings, without any spectrum, support, section map or localization diagram.

lem-per-derived-completion-finite-cohomology vs lem-weil-pbc-noetherian-koszul-augmentation-pro-zero: identifies a pro-zero cone tower for Koszul augmentations; it does not compute cohomology of completion for finite cohomology modules.

lem-per-derived-completion-finite-cohomology vs new-q2-koszul-cone-homology-pro-zero: is a cone-homology transition statement under pro-vanishing hypotheses, not a derived-completion cohomology formula.

lem-per-affine-support-cech-localization vs lem-sc-qcoh-complex-alternating-cech-derived-sections: the existing result computes the unaugmented open-section complex; it says nothing about right derived ideal torsion or its augmented support triangle and inclusion maps. Its useful unaugmented part alone cannot supply the support term used here.

## Review by Q146

I reread algebraization.tex, Tag 0DXQ, theorem-algebraization-formal-sections, including the two displayed triangles and the sentence about their canonical map. I checked that the present item is only their comparison, without importing the theorem's depth, dualizing-complex or algebraization conclusions. For the first new theorem I read local-cohomology.tex Tag 0A6T in full, including both total localization complexes and its functorial comparison; dualizing.tex Tags 0955(3) and 0956 supply the Noetherian identification with the right derived ideal-power torsion functor. The distinction matters: over an arbitrary ring the closed-support functor need not equal right derived ideal torsion, so the new theorem retains Noetherianity. For the other new theorem I read more-algebra.tex Tag 0A06, including the finite-free-resolution and completion-exactness argument, together with Tag 0922 identifying the quotient-tower completion and unit. No finiteness of the cohomology of the open-section term is asserted or used. I removed a ring-only completion-definition citation from the second helper: its ordinary module completion and map are defined by the displayed compatible sequences themselves.

Step 1 uses exactly the first helper's distinguished triangle and its closed-support inclusion clause. I checked J is contained in the maximal ideal, hence V is contained in U, and that support inclusion runs from maximal-ideal torsion to J-torsion. Thus the arrows initially run from the U-triangle to the V-triangle; their inverses are introduced only after completing.

Step 2 cites the first helper's tensor models, the actual localization-flatness statement, and the bounded-above flat module K-flat statement. I checked the latter is a module theorem, not just a result about a different sheaf site. The tensor calculation uses the whole complex P tensor B_n, so higher Tor terms are retained. I added the explicit fraction maps, K-flatness checks by associativity, and a common principal-open refinement to verify that reduction preserves the actual restriction and support arrows. Flatness of A to B_n is neither asserted nor required.

Step 3 uses the geometric-support and closed-set identity clauses of the first helper, not the proof of an unrelated Cech node. In Spec B_n every prime contains I, so J and the maximal ideal define exactly the same closed set, by the item's intersection hypothesis. The supports and opens are equal at every level. This is the elementary step deduced from the models and the hypothesis, not a new lemma merely restating the completed restriction clause.

Step 4 uses the strict-diagram replacement theorem for coherent arrows and squares, the K-flat cone closure theorem for their derived tensors, and the strict-tower Rlim theorem's exact functor and natural Roos triangle. I checked the one-object site really gives ordinary A-modules, and supplied the coordinatewise argument for exact products there. The cone differential matrix explicitly explains triangle preservation and its compatibility with the unit, including the shifted square. Thus no arbitrary TR3 lift or nonunique abstract cone morphism is being treated as canonical. The quotient-level maps from step 3 are inverted as maps in the derived strict tower category.

Step 5 uses the new finite-cohomology theorem only at M[0]. Its module consequence names the completion map itself. The already existing finite-module completeness node says that precisely this map is bijective for a finite module over an I-adically complete Noetherian ring. Those hypotheses are all in the item. This is why the middle vertical map is the identity, rather than an untracked isomorphism.

Step 6 is composition and inversion of the particular triangle morphisms already constructed. I checked its third square by multiplying the equation for the completed morphism by inverses; the displayed alpha is inverse completed support-inclusion after the unit. This is the natural identification intended in the item. The resulting open-term map is exactly inverse completed restriction after completion.

Step 7 cites the actual long exact cohomology statement and its naturality ladder, both read in full. Their abelian-category quantifier allows A-modules. The Zariski module-cohomology definition supplies H^0 equals ordinary sections. I checked H^1(M[0])=0 gives the terminating zero in both rows; no injectivity at the left endpoint and no connectivity assertion about completed supported sections is needed. The ladder supplies the connecting square, not merely the first two squares.

Step 8 has no additional black-box lemma: restriction composes, the unit is natural, and the displayed inverses cancel. An open V' in the asserted range has closed complement V(J') by the definition of the spectrum topology; the maximal ideal lies in that complement. The neighborhood hypothesis gives the same closed-fibre support equality, so the earlier proof applies. This argument does not assume an open set has a unique defining ideal.

I tested the first new statement at the empty generating list (support all of Spec A, E=A and T=0), at the unit ideal (support empty, acyclic augmented localization complex), and at a nilpotent principal generator (localization zero, full support). For the finite-cohomology completion theorem, I checked I=0 (constant quotient tower), I=A (zero tower and zero completion), N=0, and N=A/I (completion leaves the degree-zero torsion module). For the item I checked M=0; A a field, I=J=0 and U=V empty; I=0 with V(J) the closed point; I maximal with J=0, where V is empty and completed punctured sections vanish; and A=k[[x,y]], I=(x), J=(y), where J and the maximal ideal have equal support only after reduction modulo x-powers. The last case confirms the proof must not identify the original uncompleted supports. All proper-ideal, finite-generation and Noetherian hypotheses used were verified where applied.

Every cited statement has a verbatim witness in citations.json. Both new statements introduce their own objects and define their complexes or completion models; neither contains proof steps or a proof sketch. Their source tags were checked against tags/tags. Their statement dependencies name the definitions actually used. The same-source nodes listed above were read for their quantifiers and conclusions. None supplies the canonical derived localization theorem or the finite-cohomology completion theorem. I also checked every proof dependency for a path back to the item: none was found. All eight step texts are below 2000 characters; the comparisons in step 2 are explicit finite localization calculations, and step 4 cites the general lemmas it needs. The chapter and unit records are unedited. This review is my direct-delivery self-review under the dispatcher's brief.
