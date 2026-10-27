## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-flattening-by-admissible-blowup.json: item, split into six complete steps; Mathlib searches found no matching flattening theorem.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-module-flattening-by-admissible-blowup.json: statement-only input, Stacks 087C; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-strict-transform-etale-localization.json: statement-only input, Stacks 0863; no Mathlib match.
- citations.json: a verbatim statement quote for every node used by every numbered step.

## Attachments

None. Searched WeilConjectures for the item blueprint tag, flattening/flatification and strict transforms. Existing blowup and strict-transform declarations concern schemes and do not give algebraic-space flattening with all the hypotheses and clauses here. No Lean was written or compiled.

## WANTED

None. All mathematical source material used is in literature/stacks-project.

## Corrections and route

The imported statement is correct, including the absence of Noetherian and global finite-presentation hypotheses. No statement dispute or hypothesis change was needed. The proof was empty. I read spaces-more-morphisms.tex Tag 087E (lemma-flat-after-blowing-up) and its module input 087C (theorem-flatten-module). The latter cannot be applied directly to the given finite-type map.

I retain the source's envelope, module-flattening, and strict-transform comparison argument. One node-level simplification uses the existing 0872 qcqs finite-type envelope directly: Y is qcqs because g is quasi-compact and quasi-separated over qcqs T. This avoids the preliminary affine-atlas replacement and the separated 0873 envelope, whose separatedness is not needed by 087C. This is the immediately preceding envelope result in spaces-limits.tex and preserves the unit's route. The envelope statement is over Spec Z; forgetting S is harmless since only the resulting maps over T are used. The current blueprint latest/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability.proof.md were read: the relevant inherited prerequisite is the compactification/direct-image paragraph, and no unit or chapter file is edited. The inherited null blueprint ancestor and via chain are retained with explicit source places.

The DAG has scheme analogues of module flattening and closed-immersion transfer. I did not apply their statements directly to algebraic spaces. I use the existing scheme transfer only after passing to compatible etale scheme charts, with a blowup of a scheme base. The new localization lemma states exactly the comparison needed to justify that reduction. The pre-existing closed-pushforward flatness lemma has a scheme base; step 3 therefore applies it separately over every etale scheme chart of U, not directly over U.

## New nodes

lem-sfb-space-module-flattening-by-admissible-blowup states 087C for a general finite-type quasi-coherent module on a quasi-compact space locally of finite presentation over a qcqs space. Relative flatness is explicitly tested over scheme charts; module type/presentation and centre-dependent strict transform are defined inline. I read 087C in spaces-more-morphisms.tex and the convention 0862 in spaces-divisors.tex. This is a module theorem with different input data, not the original space theorem moved to a renamed node. Searches used LeanFinder in two phrasings (module flattening and Raynaud–Gruson platification), LeanSearch, Loogle, and grep through msearch.py. Hits were local-presentation definitions and scheme flatness facts; none constructs a blowup. The existing scheme flattening theorem 0815 cannot specialize to a nonschematic base.

lem-sfb-space-strict-transform-etale-localization states 0863 for compatible scheme charts, with both the space and module comparison and the induced coverings. I read all three clauses and the proof of 0863 in spaces-divisors.tex. The last assertion is ordinary base change of the given surjective atlases; it does not assume X' surjects onto X. Searches used two LeanFinder phrasings, LeanSearch, Loogle and grep through msearch.py. Hits concerned etale permanence, scheme restrictions and local-ring maps; none identifies strict transforms of spaces or modules. There is no corresponding project declaration. No new node has a proof, hidden proof sketch or proof dependency.

## Not duplicates

lem-sfb-space-module-flattening-by-admissible-blowup vs lem-trf-flattening-module-by-admissible-blowup: the existing 0815 statement requires schemes, while 087C permits arbitrary algebraic spaces for both source and base.
lem-sfb-space-module-flattening-by-admissible-blowup vs lem-sfb-space-flattening-by-admissible-blowup: 087C flattens a general quasi-coherent module on an already locally finitely presented ambient space; the item flattens a finite-type space not assumed locally finitely presented.
lem-sfb-space-module-flattening-by-admissible-blowup vs lem-sfb-space-strict-transform-as-blowup: that node identifies the space transform with a blowup and gives some permanence, without a flattening theorem for modules.
lem-sfb-space-module-flattening-by-admissible-blowup vs lem-sfb-space-zariski-after-admissible-blowup: that node makes a map which is an open immersion over U into an open immersion after blowup; it has no arbitrary-module assertion.
lem-sfb-space-strict-transform-etale-localization vs lem-sfb-space-composition-centres-and-transforms: the existing node mentions 0863 in its source to justify extending the successive-transform theorem 0868, but states only composition of blowups and their transforms, not etale localization.
lem-sfb-space-strict-transform-etale-localization vs lem-trf-strict-transform-flat-etale-base-change: that node concerns a closed subscheme in a scheme ambient, has an extra generic-component condition, and states no quasi-coherent module comparison or algebraic-space chart theorem.
lem-sfb-space-strict-transform-etale-localization vs lem-trf-module-strict-transform-flat-pullback: the existing node is a scheme module theorem; the new result simultaneously identifies algebraic-space transforms and their module restrictions on etale scheme charts.

## Review by Q127

I checked sections B through E of delivery-errors against the actual JSON and the cited source statements. I read the imported statement clause by clause against 087E and the two new statements against 087C and 0863. All new objects and notions are introduced, sources use the actual tag/label mapping, and TeX has one semantic backslash. Mathlib searches are only recorded from actual msearch.py results; there were no unavailable service results in the searches used here. I searched the entire DAG by source tags, flattening, strict transforms, closed module criteria and envelope statements, and used blueprint_refs.py searches for the same concepts. No blueprint node states either new result.

Step 1 uses the affine-test quasi-compactness criterion, atlas composition and fibre-product nodes to establish quasi-compactness of Y from g and T. The quasi-separated-test-calculus statement explicitly gives composition, and the 0872 envelope explicitly permits qcqs X,Y and merely locally finite type f; these are exactly the hypotheses established here. I initially described an affine atlas construction unnecessarily; I corrected the text to use the quasi-compact scheme atlas already supplied by the definition, so no unproved finite-affine-subatlas identification is hidden.

Step 2 uses the closed-immersion quasi-coherent-module statement for both quasi-coherence and the surjection O_Z onto F; image of 1 gives finite type directly. The relative-lfp permanence node says that a map is lfp if its composite is lfp and the target is lft over the same base. On U the given g is lfp and h is lfp, hence lft, so the application is valid. The closed-structure criterion explicitly equates finite presentation of i with finite presentation of i_*O_Y. Etale pushforward restriction explicitly supplies the identification with F restricted to Z_U. Ring finite-presentation base change is cited for the passage to U, via the scheme-chart definition.

Step 3 uses the exact flatness equivalence in the closed-pushforward statement, always with a scheme A as its base, and the etale restriction statement to identify its module. The local-property criterion supplies the chart check of the flat morphism. Thus no theorem whose base is a scheme is silently used with base U.

Step 4 checks all hypotheses of the new module-flattening theorem: T qcqs, U qc, Z qc, h lfp, F finite type, and finite presentation and relative flatness of F_U from steps 2 and 3. The atlas composition and affine-test nodes give Z qc exactly as in step 1. Its conclusion supplies both finite presentation and flatness for the transformed module, as well as a finite-type ideal equal to O on U.

Step 5 uses precisely the space and module equalities of the new localization statement, the etale pushforward restriction identity, and the existing scheme closed-immersion transfer. Over A the spaces D and W are schemes because i is representable closed and W is a scheme chart. The blowup A' is the blowup of the pulled-back finite-type ideal, exactly the scheme transfer's base. The transfer requires only W to A lfp, not a separated ambient or a globally lfp D to A. That lfp follows by base change and etale composition. The transfer gives both the transformed-module identity and the desired flatness/lfp. Its existing statement is substantially stronger than a bare affine-pushforward identity, so no comparison is borrowed from its proof. The scheme-chart criterion explicitly descends flatness and lfp from the resulting surjective charts.

Step 6 is the elementary qcqs argument, not a new lemma: closed immersion over affine Spec R has source Spec(R/I), so is qc; its diagonal is an isomorphism, so is separated and hence qs. The affine-scheme qcqs statement and closed-immersion definition give that calculation, while the qc affine-test criterion and qs calculus explicitly provide base change and composition. Iterating quasi-compact test pullbacks proves the qc composition assertion. Finite presentation here retains the required qs clause, even though some Mathlib conventions package it differently.

I tested the new statements on U=T (identity blowup when the hypotheses already hold), U empty (zero centre gives empty blowup and empty transformed spaces/modules), X empty and the zero module, K=O (identity blowup, empty exceptional divisor, unchanged transform), and K=0 (empty blowup). These cases show that no density or nonempty-atlas hypothesis was added, and that the centre, not just its morphism, must be retained in the transform definition. The non-Noetherian case is preserved: finite-type F need not be finitely presented before blowing up. No step exceeds 2000 characters; no long step hides an unstated comparison. Existing off-unit inputs are generic algebraic-space calculus or the scheme comparison theorem, declared as tool uses. No SGA source is used.

## Unfinished work

None in this one-level split. The two new statement-only inputs remain queued for their own later splits. Remote validation and direct delivery are recorded below.
