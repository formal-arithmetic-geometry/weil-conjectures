# Stage-1 report: lem-coef-operadic-block-incidence-lifting

## Files written

- dag/nodes/sec-six-functors/lem-coef-operadic-block-incidence-lifting.json: existing statement node, now split into six steps; no Mathlib match.
- citations.json: one verbatim statement quotation per step/node citation.
- report.md: this report.

No new nodes and no Mathlib leaves. No unit records changed.

## Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint id, block/incidence lifting and operad/Segal/cocartesian terminology. No declaration states this comparison. The read-only master checkout also has no exact id/block-incidence hit. Neither a sorry declaration nor a partial ordinary-category result was treated as an attachment.

## WANTED

WANTED: Gepner–Haugseng, Enriched infinity-categories via nonsymmetric infinity-operads, arXiv:1312.3178v4, Definitions 2.4.1 and 3.1.13 and Erratum E.0.1 proof, for lem-coef-operadic-block-incidence-lifting. Read online at https://arxiv.org/html/1312.3178v4 on 2026-10-17; no local archive found. The proof is marked agent-written, as required when the reference is not archived. No Stacks tag states this infinity-operadic result; no SGA source used.

## Findings and corrections

The imported statement is correct with its inherited operad convention; no statement correction or STATEMENT-DISPUTED claim is needed. Its proof was empty. The distinction between the fiber Segal equivalence and the mapping-space incidence axiom is essential: the latter supplies the actual fixed-source comparison. The edge terms must be replaced over each particular active base arrow, rather than by claiming precomposition on the entire set of ordinal arrows is injective. The new proof spells this out. It also constructs the coherent comparison of whole incidence diagrams, rather than identifying only their objects.

The historical blueprint ancestor is prop-coef-integral-exceptional-adjoint, proof paragraph 2, and the present item lies below its already existing operadic/localization route. Read the ancestor proof in literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md, its unit and chapter records, and the current parent lem-coef-operadic-operation-segal-product. No change to the unit or chapter route is proposed. Whole-blueprint search for incidence and DAG searches for block comparison/cocartesian mapping criteria found the existing axioms and generic tools used below. No duplicate helper was created.

## Unfinished work

None for this one-level split. All cited nodes already exist; their own proof obligations remain their own items. The reference archive request remains a literature-maintenance request.

## Review by Q13

I read delivery-errors B–E in full and checked the six proof steps against the actual statements of their dependencies. I read the online Gepner–Haugseng definitions and the Erratum proof, while treating the coherent details below as my own expansion. The Mathlib searches were run through msearch.py and their actual logged results are appended to the item's inherited searches. Both LeanFinder phrasings, Loogle, LeanSearch and grep returned ordinary nerves, strict Segal simplicial sets or ordinary-category cocartesian arrows. I read StrictSegal.lean lines 280–322 and FiberedCategory/Cocartesian.lean lines 45–84: unique strict spine reconstruction and ordinary hom lifting do not state this homotopy-coherent operadic comparison.

Step 1 uses lem-coef-operadic-algebra-presentability specifically for its explicit generalized-operadic mapping-space incidence axiom. Its statement quantifies over every source X and every base arrow phi and includes every inert projection to [1] and [0]. I checked that the chosen C diagram and the active alpha satisfy these hypotheses. The ordinal computation identifies rho_i alpha with beta_i r_i and includes singleton input intervals.

Step 2 uses lem-coef-infinity-cocartesian-mapping-criterion specifically for its homotopy-pullback square for every target z. The q_i are cocartesian by hypothesis; Q is a quasicategory since an inner horn first fills in the nerve of the base and then lifts through its inner fibration. The base nerve has discrete mapping spaces. The fiber at beta_i in that square is exactly the required space, without any assumption that all base arrows have distinct composites.

Step 3 uses lem-cbc-simplicial-composition-spine for coherent associativity and its naturality in all simplicial parameters, and lem-cbc-enhanced-functor-cone-calculus for the componentwise-equivalence criterion. I checked that these statements give these assertions, not merely associativity in the homotopy category. The only nonidentity incidence arrows are edge-to-endpoint maps, and the explicit associativity square is exactly their required compatibility. No claim that the source is a strict diagram is made.

Step 4 uses lem-coef-infinity-yoneda-presheaf-limits for the existence of small limits of spaces and lem-cbc-enhanced-functor-cone-calculus for the cone/terminal interpretation and functor quasicategories. The diagram is finite, so there is no universe or large-index-category mismatch. Transport of cones is written by postcomposition with a diagram equivalence and its inverse, including their inverse homotopies; it is a short consequence, not an uncited comparison theorem. The resulting map has the desired restriction/factorization components.

Step 5 again uses the coherent composition and cone calculus statements. I checked the square q_i e = e_i q'_i up to the given coherent witness and the direction of precomposition on edge and vertex mapping spaces. Source and target changes are equivalences of the specified whole diagrams; no theorem about arbitrary unchosen projection diagrams is silently applied. Inverse edges yield the inverse homotopies asserted by the cited composition statement. Inverses of the transformation live in the functor category, so the comparison and all parameter coherences are retained.

Step 6 uses lem-cbc-kan-fibration-fiber-criterion, whose statement explicitly includes the equivalence criterion for homotopy fibers of arbitrary maps of Kan complexes, not only strict fibers of fibrations. I checked k=1, n=0, one zero-length block adjacent to a nonzero block, and all blocks zero. The corresponding opposite ordinal inclusion and constant active arrow exist in every case. If there are no compatible data the claim about their fibers is vacuous; if a compatible datum is specified the equivalence guarantees a contractible homotopy fiber. A non-groupoidal edge fiber is allowed because only actual equivalences, not all its arrows, are inverted.

The three generic results from the compactification unit are declared in split_report.tool_uses with the exact role of each. They are generic foundations and replace no step of that unit's geometric route. I checked their transitive dependencies and those of the two same-unit tools: none reaches this item. Every citation quote is checked literally against the node's statement, and proof_deps is the exact union of step uses. There are no new statements to test or new-node duplicate pairs. All proof steps are under 2000 characters; the longest is the explicit naturality argument (1086 characters), with its general composition facts cited rather than hidden. Only sandbox files were written, and no Lean/compiler/build or live-project git command was run.

## Not duplicates

No new nodes.
