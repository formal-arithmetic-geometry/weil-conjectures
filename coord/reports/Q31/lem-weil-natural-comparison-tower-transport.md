## Worker report

Item: lem-weil-natural-comparison-tower-transport. Group: Q31. Stage 1 only, direct delivery.

### Files written

- dag/nodes/sec-smooth-purity/lem-weil-natural-comparison-tower-transport.json: split, statement unchanged; seven explicit proof steps, no new nodes.
- citations.json: ten verbatim statement quotations covering every use in the seven steps.
- searches.jsonl: the five searches actually run with the prescribed msearch.py command. The item retains its inherited 2026-10-21 searches and appends these 2026-10-23 results.
- report.md: this report and the signed review below.

## New nodes

None. Zero Mathlib leaves added. The existing lem-pur-semilinear-scalar-localization states exactly the generic localization tool needed here; the tower and unit calculations are elementary consequences of naturality, with the substitutions written in full, so they do not merit further nodes.

## Attachments

None. The blueprint-tag search in lean/WeilConjectures had no hit. Searches for tower transport, scalar localization, semilinear functors and conjugation in that library found geometric tower constructions, derived rationalization and adjunction-mate pasting, but no project declaration that proves all the explicit normalization, unit and scalar-localization clauses of this item. The categorical rationalization file does not state the tower calculation. No sorry declaration was treated as a finished proof.

## WANTED

None. The elementary argument is written by the agent and marked as such. The source sentence motivates it rather than supplying its categorical algebra proof.

## What changed and what was wrong

The item had an empty proof. Its mathematical statement needs no correction. In particular, the two normalization equations are correctly typed and the repeated-index unit equations really follow from naturality, without an extra relation among the chosen comparison isomorphisms. I filled the proof, proof dependencies, agent origin, blueprint proof place and split report. No definition, target statement, unit or chapter was changed.

The historical source place mentions a scalar-extension-composition document and a longer extraction. In the current blueprint, read through literature/blueprint/latest, prop-weil-twist-preserves has only the final levelwise/common-finite-stage sentence. I used that precise current sentence as the blueprint place and retained the historical source record. The detailed scalar-extension source now available is sec-smooth-purity/sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.proof.md, clause (4), which explains the associator and identity normalization. The categorical calculation here is a below-unit auxiliary making that normalization explicit, not a claim that the current blueprint sentence already proves these formulas.

## Searches and Mathlib verdict

The whole DAG was searched by scalar-localization, natural-transformation, semilinear, conjugation and tower-transport concepts, including full statement inspection for the candidates. Blueprint searches through tools/blueprint_refs.py included scalar localization, semilinear functor, tower transport, tower squares, comparison conjugation and conjugation preserves. The broad scalar search found 22 blueprint nodes; the geometric rationalization and twist statements are not this abstract theorem. The conjugation-preserves hit concerns geometric monodromy. The ancestor command gives prop-weil-twist-preserves. The existing generic lem-pur-semilinear-scalar-localization, despite not being a blueprint node, eliminates the need for a new node. I also inspected lem-fd-raw-localization-scalar-coherence, which has geometric coefficient systems and additional normalized comparisons rather than this arbitrary category theorem; it is not used.

The five actual msearch calls are recorded verbatim in the node and searches.jsonl: LeanFinder with two different phrasings, Loogle with NatTrans.naturality and Iso, grep of categorical conjugation and transport, and LeanSearch with tower transport and scalar localization. All services answered successfully. The hits are not a one-line specialization of the entire item. I read Mathlib/CategoryTheory/CatCommSq.lean (naturality and horizontal/vertical composition), Localization/Predicate.lean around liftNatIso (line 357), Localization/Linear.lean (same-ring linearity of localization/lifts), and Monoidal/Functor.lean around coreMonoidalTransport (line 1336). CatCommSq supplies individual naturality squares, not the specified comparison-conjugation equation; liftNatIso assumes categorical localization and existing lifting functors, not a construction of semilinear raw Hom-module localization; monoidal transport assumes monoidal structure. These are useful ingredients, not an exact match for the whole statement. No new node and no claimed Mathlib leaf result from them.

## Tool use

lem-pur-semilinear-scalar-localization is a generic tool from sk-thm-purity-transport, declared only in split_report.tool_uses. Its first two paragraphs and equation-preservation assertion apply without the optional triangulated hypotheses. It gives extensions of additive semilinear functors across different scalar rings, localization of natural transformations with their actual components, preservation of inverse/unit/composition/whiskering equations, and hence exactly the scalar part needed here. No node of the item's unit replaces this general tool. It does not replace the twist/tensor argument of the unit. A dependency-closure inspection found 55 nodes below this tool and no path back to the item.

## Not duplicates

No new nodes, so no new/existing-node pairs require comparison.

## Review by Q31

I read the complete item statement and its parent lem-weil-integral-twist-scalar-coherence, the chapter record sec-smooth-purity, the unit record sk-prop-sf-existence, the three-level route rule of SETUP.md and GOAL.md. I read both current prop-weil-twist-preserves files under literature/blueprint/latest (the current commit is recorded in COMMITS.txt), including the final sentence about integral levelwise and common finite stages. I also read the current scalar-extension-functor proof, clause (4). This is an auxiliary calculation below the unit, and no geometric route, coefficient category or adjunction was changed. The inherited item's source is agent-written; proof_origin.by is agent, not document. There are no new-node source statements to audit.

I checked delivery-errors B through E against the actual seven steps and opened every cited statement. B: there are no newly created nodes, no hidden proof inside a new statement, no Mathlib matches without source inspection, and no new notions lacking a definition. The existing statement defines functors and natural isomorphisms inline and cites category, linearity and raw localization definitions. The unchanged node has TeX formulas and all its existing metadata; the blueprint place and same_as are now explicit. D: no clause has been moved into a new node; Steps 2 through 5 themselves contain the transport algebra. Step 6 uses a pre-existing, genuinely more general scalar-localization tool. All steps are shorter than 2000 characters; none conceals a long proof behind 'transport' or 'same calculation'.

Step 1 uses def-nagata-category, whose statement includes associative composition and identities. I checked the corresponding Stacks 0014 label categories-definition-category in categories.tex. The step explicitly derives composition, inverse and whiskering naturality from the statement's definition of natural transformation. Invertibility follows by applying a functor to the two inverse equations and by reversing composite factors. No theorem on functor categories is silently used.

Step 2 uses only those category laws and the given naturalities. I checked the object types: beta_10,K is an arrow B_10(W_0 K) to W_1(B_10 K), so naturality of chi_21 at exactly that arrow gives the first displayed cancellation. Naturality of alpha_21 is applied at chi_10,K, an arrow T_10 K to B_10 K in D_1. Its direction gives alpha_21,B10K T_21(W_1 chi_10,K) = W_2(T_21 chi_10,K) alpha_21,T10K, which is the desired first normalization. The equation is a direct substitution and cancellation, rather than a cited new lemma.

Step 3 again uses def-nagata-category. I expanded the second path and verified each inverse is adjacent to its own component, with W_0K as index. Multiplying the first normalized path by W_2(a_K) produces W_2(chi_20,K) W_2(mu_K) times the ordinary two-step twist path; the supplied tower hypothesis then gives the same expression as the second path. The cancellation at the end is by the displayed inverse of d_W0K, so no faithfulness assumption enters.

Step 4 substitutes v and beta into the identity-transition compatibility. W_i(chi_ii,K^-1) and W_i(chi_ii,K) cancel before applying the assumed compatibility with u_i. Step 5 verifies both repeated-index associators explicitly: the (j,i,i) case uses naturality of chi_ji at v_i,K, and the (j,j,i) case uses naturality of u_j at chi_ji,K. I checked the sources and targets in both cases, including i=j, and the resulting components are exactly B_ji(v_i) and v_j B_ji. These steps use only the category definition and the item's hypotheses.

Step 6 uses lem-pur-semilinear-scalar-localization and def-weil-linear-functor. I opened both statements and checked that the first supplies unique additive semilinear extensions with unchanged object maps, extensions of all natural transformations with components Q of the original component, and preservation of identity transformations, vertical composition and whiskering. Its last triangulated paragraph is optional and unused. For each i<j the inversion condition is exactly a hypothesis of our item, including the composite coefficient map for 0 to 2; for W_i and identity transitions the coefficient map is the identity and t_i is inverted by its own localization. The definition of a linear functor includes additivity as well as scalar compatibility, so the tool's additive hypothesis is met. The units u and their inverses are transformations between functors over the identity coefficient map. Thus every extended comparison has matching scalar maps on its two endpoints. Applying preservation of composition to a = chi_20 mu d^-1 gives the claimed exact identification of localized transport, not merely an unspecified isomorphism.

Step 7 cites that same tool's explicit semilinear extension and component clauses, def-weil-linear-category for bilinearity, and def-weil-linear-scalar-localization for tensor Hom modules, pure-tensor composition and Q's functor laws. I opened all three statements. Stacks dga-definition-linear-category (09MJ) and dga-definition-functor-linear-categories (09MK) in dga.tex confirm the bilinearity and module-hom meanings. Multiplying the integral naturality square by the common final scalar gives the displayed pure-tensor equality; additivity then handles finite sums, which exhaust the algebraic tensor product. The scalar agrees on the two sides since the compared functors have the same coefficient map, also for the composite transition. Nothing attempts to deduce integral equality from localized equality.

The ten entries of citations.json are verbatim substrings of these actual node statements. In particular the scalar tool's quote states both transformation extension and preservation of equations; a definition is not being used as a replacement for that theorem. Other quotes are precisely the category laws, linear scalar action, and tensor-Hom formula used by the elementary calculations. This checks C1, C3 and C4 concretely.

For E and the small cases I checked: all comparisons and endofunctors identities (every displayed equation reduces to the assumed mu equation); i=j and i=j=k (both unit degeneracies use the same naturality equations and remain valid); arbitrary noncommuting comparison components (the written cancellations never commute arrows); empty categories (the component assertions are vacuous); t_i=1 (localization formulas reduce to ordinary scalars); nilpotent t_i (the localized ring is zero and all equations remain equations in zero Hom modules); torsion Hom modules (Q need not be faithful, but the proof only maps equalities forward). A scalar map not carrying t_i to a unit would invalidate Step 6, which is why that explicit hypothesis was checked for every pair. The first delivery dry run required a longer citation quote for def-weil-linear-functor (at least 40 characters); I replaced that short formula with its complete verbatim statement, which also explicitly includes the additivity used in Step 6. No new statement, counterexample or STATEMENT-DISPUTED correction was required. I corrected no mathematical statement and added no hypothesis.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled, and no git command was run in the shared repository.
