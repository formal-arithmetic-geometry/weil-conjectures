# Stage 1 delivery: lem-sfb-space-higher-direct-image-quasi-coherent

Group NQ; 2026-10-23. Continued the saved sandbox after provider interruptions; the saved JSON files and search records were retained. The interrupted writing process no longer existed, its outputs were present, and no delivery had been launched.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-higher-direct-image-quasi-coherent.json: statement, split; unchanged statement and statement dependencies; five proof steps, complete proof dependencies, blueprint explanation, and search records retained and supplemented. No exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-cech-module-spectral-sequence.json: statement, unsplit; relative first-quadrant spectral sequence for arbitrary structure-sheaf modules on small etale topoi, with finite abutment filtration. No Mathlib match after both semantic phrasings, Loogle, grep and LeanSearch.
- citations.json: one verbatim statement quotation for every citation in every proof step. Whole statements are quoted to retain their hypotheses.
- report.md: this report. searches.jsonl and the two saved search-result JSON files retain actual searches, including exploratory searches for candidate nodes that were not created. write_split.py is a sandbox preparation script, not a delivered project file.

## Attachments

None. Searched the project Lean by the item id, blueprint tag and algebraic-space/quasi-coherent higher-image terminology. Scheme.Modules.isQuasicoherent_higherDirectImage in WeilConjectures/Cohomology/DirectImage/Sections.lean:66 concerns schemes, not the full algebraic-space assertion. Neither that partial result nor sorry declarations give an attachment. No Lean was written or compiled.

## WANTED

None. All sources needed here are in literature/.

## Findings and route

The imported item had no proof. Its statement agrees with Stacks spaces-cohomology.tex Tag 0720 and needs no correction: qcqs morphism, arbitrary quasi-coherent module, all nonnegative degrees, no Noetherian or separatedness addition. There is no released repair note and the current repository item remains unsplit.

Read the latest blueprint's sk-thm-sf-ctf-stability-direct-images statement and proof, and its section. This is the downstream quasi-coherent-cohomology prerequisite in the inherited alteration/stable-curve chain serving det-thm-sf-ctf-stability-direct-images proof (3), rather than a new route for the constructible direct-image theorem. The inherited from.node is null and the ancestor tool returns None; retained its explicit place and via chain, and prefixed the item to the new node's chain. Whole-blueprint searches found no identical relative structure-module spectral sequence. same_as is empty.

I read Tag 0720 including the preceding paragraphs. They explicitly suggest a relative Cech proof as an alternative to the induction printed there. The split follows that alternative: after affine etale localization, the entire atlas nerve consists of qcqs schemes, so the existing scheme comparison makes the whole first page quasi-coherent. Page homology and the finite filtration then use only the existing kernel/cokernel/image and extension closure statements. This avoids assuming closure under arbitrary subobjects, which quasi-coherence does not have.

The only new input is genuinely different from the item: it is a spectral sequence for arbitrary modules and arbitrary morphisms, with no quasi-coherence or qcqs conclusion or hypothesis. It cannot by itself prove the item. It is left statement-only as required. I read stacks-sheaves.tex Tag 072E and its proof, including the relative abelian version immediately before it. Tag 072E is written for big stack sites; the new statement explicitly specifies its small-etale localization version, rather than silently identifying those sites. The cited enlarged-site model identifies the small etale ringed topoi and their etale localizations. The same proof uses an injective module resolution on X: restriction to each localization preserves injectives, and the augmented Cech rows are exact on injectives. The two first-quadrant double-complex spectral sequences give the stated first page and finite convergence. The coefficient category is Mod(O), not constant-coefficient sheaves or bare abelian sheaves. The new node records the required localization model and injective-resolution notions.

Mathlib search results were read, not inferred from empty name searches. Semantic hits cover module pushforwards, scheme modules, generic homological constructions and Mayer-Vietoris, but do not state this relative small-etale structure-module spectral sequence or specialize to it in one line. The item's scheme hits likewise do not prove the algebraic-space theorem. All searches in node metadata are actual logged msearch queries; no unavailable service was counted as a negative answer. Whole-DAG searches by tags and notions, blueprint_refs searches, and project Lean searches preceded creation. The existing augmentation spectral-sequence nodes use abelian or constant-coefficient categories, so they do not supply this O_X-module statement.

## Review by NQ

I checked the split against delivery-errors B through E, with the sources and every cited node's statement open. I retained the exact target hypotheses, kept the new node statement-only, and checked that no step merely applies a renamed clause of the item. No proof step exceeds 2000 characters. No SGA source is used.

Step 1 uses the local-presentation definition of quasi-coherence, the full higher-image etale-restriction statement, and the affine-test/base-change statement. The restriction node is explicitly for all modules, every nonnegative degree and arbitrary etale base change, so this use does not assume the result being proved. Presentations restrict and compose over covers by their definition; affine open refinements cover arbitrary scheme charts. Base change of the relative diagonal proves the required quasi-separatedness after localization. The source is the opening reduction in 0720; no proper or flat base-change theorem is substituted.

Step 2 uses the affine qcqs statement, both clauses of qcqs-source-products, change-base-to-integers, the affine-atlas statement, fibre-product representability, qcqs-permanence and the representable affine-test equivalence. I read their complete statements. Change of base supplies the same spaces, fibre products and small ringed sites over Spec Z, where the absolute source/product lemma is stated. The product lemma requires all three spaces qcqs: here they are U_p, U and X, and induction supplies each hypothesis. The nerve terms are schemes by representability of the atlas, not by any claim that a fibre product of arbitrary spaces is a scheme. Their maps to affine Y are qcqs by permanence, and the same affine-test statement applies to their diagonals. I corrected a convention gap during self-review: the atlas and permanence lemmas use point-space quasi-compactness, whereas the affine-test/source-product lemmas use scheme atlases. The now-cited lem-a1-space-etale-open-image states exactly the equivalence of these two notions. Its off-unit generic-tool use is declared.

Step 3 uses the etale permanence statement, the local-presentation definition, the new module spectral sequence, and the existing scheme-etale higher-image comparison. The restrictions to U_p are etale restrictions of the actual structure sheaf, so presentations remain presentations. Step 2 gives exactly the qcqs scheme hypotheses of the comparison theorem. That theorem explicitly states quasi-coherence of the Zariski higher image and the canonical comparison with the small etale higher image in all module sheaves. Thus it supplies the whole first-page assertion, not just its degree-zero part. I checked it does not depend on the present item. The spectral-sequence input has neither a quasi-coherence hypothesis nor a derived-image preservation conclusion.

Step 4 uses the kernel/cokernel/image closure statement and the spectral-sequence statement. For a page differential the incoming image and outgoing kernel are quasi-coherent; their quotient is the cokernel of a map between quasi-coherent modules. This gives induction on pages using exactly what the closure node says. At a fixed bidegree, an incoming differential requires r <= p and an outgoing one requires r <= q+1, so first-quadrant stabilization uses only finitely many pages. I did not infer quasi-coherence of an arbitrary submodule of a quasi-coherent sheaf.

Step 5 uses the explicitly finite filtration in the new statement and the extension-closure statement. Its short exact sequences have quasi-coherent outer terms, precisely the hypotheses of the extension node. Descending induction starts with the zero module and ends with the desired higher image. This is an elementary finite assembly argument and is written out; no extra spectral-sequence closure lemma is concealed.

I tested empty source/atlas (Spec 0 is allowed), zero module, degree zero, and an identity/affine scheme morphism. In degree zero the finite filtration has one graded term. Empty and zero cases give zero throughout. The argument does not require the higher nerve schemes to be affine or separated: qcqs suffices for the scheme comparison. Thus a nonseparated but quasi-separated source introduces no accidental separatedness assumption. Infinite degrees are treated separately, each with its own finite first-quadrant filtration; no bounded cohomological dimension or infinite extension closure is assumed. Non-Noetherian rings and arbitrary-rank presentations remain permitted throughout.

## Not duplicates

lem-sfb-space-relative-cech-module-spectral-sequence vs lem-sfb-space-higher-direct-image-quasi-coherent: shared contextual Tag 0720; the new node supplies relative Cech descent for arbitrary modules and morphisms, while the item asserts preservation of quasi-coherence by qcqs direct images and proves that using the scheme first page and closure statements.

lem-sfb-space-relative-cech-module-spectral-sequence vs lem-trf-space-enlarged-site-scheme-density: shared Tag 03G1; density and a sheaf equivalence do not state a derived relative spectral sequence or its filtration.

lem-sfb-space-relative-cech-module-spectral-sequence vs lem-trf-space-chart-limit-enlarged-sections: shared Tags 03G1/03LX; the existing node identifies degree-zero section limits and localization squares, not derived Cech descent.

lem-sfb-space-relative-cech-module-spectral-sequence vs lem-trf-space-enlarged-etale-ringed-site-model: shared Tag 03G1; the existing ringed-site/localization model is a stated dependency, and contains no Cech spectral sequence.

lem-sfb-space-relative-cech-module-spectral-sequence vs def-trf-scheme-algebraic-space: shared Tag 03G1; representable-sheaf algebraic-space definition versus a higher direct-image spectral sequence.

lem-sfb-space-relative-cech-module-spectral-sequence vs lem-trf-graded-pushforward-etale-restriction: shared Tag 03LX; graded degree-zero pushforward/evaluation compatibility versus derived atlas descent for arbitrary modules.

lem-sfb-space-relative-cech-module-spectral-sequence vs lem-trf-space-etale-module-pushforward-restriction: shared Tag 03LX; degree-zero base-change and pullback comparison versus an all-degree relative Cech spectral sequence and convergence.

lem-sfb-space-relative-cech-module-spectral-sequence vs lem-trf-space-section-algebra-etale-base-change: shared Tag 03LX; section algebras for separated qc maps and line modules versus arbitrary-module relative Cech descent.

lem-sfb-space-relative-cech-module-spectral-sequence vs lem-trf-canonical-proj-open-cover-gluing: shared Tag 03LX; gluing section algebras and Proj maps versus derived module descent; neither statement implies the other.

lem-sfb-space-relative-cech-module-spectral-sequence vs lem-sfb-space-higher-image-etale-restriction: shared Tag 03LX; restriction of higher images along one etale base change versus the spectral sequence of a surjective atlas and its abutment filtration.

## Remaining work

No stage-1 assembly step remains. The sole new spectral-sequence lemma is deliberately unsplit and is the downstream queue item. No Lean/stage-2/stage-3 work was attempted. Required server dry run and direct delivery follow this report.
