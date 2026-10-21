# Worker report: lem-sfb-bounded-finite-model-generation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bounded-finite-model-generation.json`: statement, split; five proof steps; existing Mathlib leaves supply the short-exact-sequence triangle and truncation cohomology, but Mathlib does not state the whole coefficient-general stratum generation theorem.
- `citations.json`: five verbatim quotations, one for every cited node in every proof step.
- No new DAG nodes; zero new Mathlib leaves. `searches.jsonl` is the search tool's original log. The PDF extraction and `write_split.py` are sandbox working files.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for finite-model, constructible-generation, stratification and devissage language. The closest proved theorem is `AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek` in `WeilConjectures/SixFunctors/Etale/Derived/Stability/Generation.lean:268`. Its finite coefficient ring, etale category, finite Tor amplitude, flat stratum sheaves and retract-stable class differ from this item's arbitrary condensed coefficients, ordinary pro-etale module derived category and merely bounded constructible cohomology. It is not an attachment.

## WANTED

None. All sources needed for the split are available locally.

## Corrections and scope

The item arrived unsplit and the sandbox contained no earlier item, proof, report or search log. I copied the live node and retained its statement, all existing metadata, blueprint ancestry and inherited searches. No statement correction or route change was needed. The chapter and unit were read; the item is not the unit's key statement, so no unit record is changed.

The item's source describes an extraction, rather than a verbatim arbitrary-coefficient theorem of Bhatt–Scholze. I read Proposition 6.8.11(3) (printed pp. 60–61) and Lemma 6.3.14 (printed p. 47). Their bounded and stratified devissage pattern applies here, but the arbitrary-condensed generality is supplied by the existing finite-model filtration plus general derived-category facts, so `proof_origin.by` is `agent`. The split does not use the finite-projective-resolution argument for local models. In particular it does not impose finite Tor amplitude or flatness on integral torsion models.

## Searches and reuse

I searched the whole DAG for Tags 09Y5 and 08J5 and for stratum filtrations, Postnikov arguments and constructible generation. The existing `lem-sfb-finite-model-stratum-filtration` states exactly the finite sheaf filtration needed. Its coefficients and topology assumptions are as general as the item. I reused it, rather than creating a node restating the sheaf case. The existing `lem-weil-pbc-complex-ses-triangle`, `lem-weil-pbc-truncation-cohomology` and `lem-weil-pbc-truncation-triangle` provide the remaining non-elementary facts.

`tools/blueprint_refs.py ancestor` identifies `lem-sfb-dc-hom-preserves`. Blueprint searches for stratification, truncation, finite-model and generated found no exact blueprint equivalent of this coefficient-general result; `same_as` remains empty. The finite devissage serves the ancestor's last-sentence coefficient-continuity argument through `lem-sfb-constructible-internal-hom-continuity`, as recorded in `split_report.blueprint`.

All new searches were run through the required `msearch.py`, including two LeanFinder phrasings, two Loogle patterns, LeanSearch, and two grep searches. I read the returned results. The first LeanFinder query returned condensed-module infrastructure; the second returned bounded representative and fraction lemmas. LeanSearch returned general truncation triangles and the triangle of a short exact sequence. The Loogle patterns returned no hits and `ComplexShape.Embedding.IsTruncLE.mem_prev`, respectively. The constructible grep found constructible-set topology only; the declaration grep located the general triangle and bounded representative results. I read the relevant local Mathlib declarations (`DerivedCategory.triangleOfSES_distinguished`, `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`, and `TStructure.triangleLTGE_distinguished`). None gives the arbitrary-coefficient stratum generation assertion in one specialization. The inherited item searches remain intact and the actual new queries and outcomes are appended.

## Not duplicates

No new nodes are proposed. The existing filtration and derived-category nodes are reused directly. The finite-coefficient generation nodes and rational-coefficient heart-filtration nodes do not cover this item's coefficients and hypotheses.

## Review by Q08

I read the chapter and unit, the current ancestor proof, the complete statements of every node cited by the five proof steps, the definition of finite constant local models, Stacks `topology.tex` Tag 09Y5 (`lemma-noetherian-partition-refined-by-stratification`), `derived.tex` Tags 0152 (`lemma-derived-canonical-delta-functor`) and 08J5 (`remark-truncation-distinguished-triangle`), and `homology.tex` Tag 0118 (`section-truncations`). I also read the Bhatt–Scholze passages identified above. The statement is kept exactly as received.

Step 1 uses the statement of `lem-sfb-finite-model-stratum-filtration`, including the increasing open filtration, reduced closed strata, finite constant local models, and quotient formula. It assumes topological Noetherianity, not local Noetherianity of the structure sheaf. Its ordinary quotient sheaf is exactly the generator in our hypothesis after placing it in degree zero; no derived closed pushforward comparison is smuggled in. The localization sequence and reduced-stratum refinement are conclusions of that existing node, rather than additional facts proved inline.

Step 2 uses `lem-weil-pbc-complex-ses-triangle` in the abelian category of B_X-module sheaves. Concentrating a sheaf short exact sequence in degree zero is visibly degreewise short exact, meeting its hypothesis. The proof writes the base case and successor case of induction on the filtration length. Extension closure is applied with first and third terms already in the class, as the item requires.

Step 3 uses the exact cohomology formula and inclusion-map isomorphisms stated in `lem-weil-pbc-truncation-cohomology`. Below the lower bound all cohomology of the starting truncation vanishes; above the upper bound both source and target of the final inclusion have zero cohomology. The definition in `def-weil-abstract-derived-category` then directly makes these two maps quasi-isomorphisms and hence invertible in the localization. This is the elementary endpoint check; it invokes no infinite-limit or left-completion theorem. Boundedness is only cohomological, so the representative need not be termwise bounded.

Step 4 uses precisely the existence and three terms of the distinguished triangle in `lem-weil-pbc-truncation-triangle`. Its arbitrary abelian-category hypothesis covers our module sheaves. I use no uniqueness, naturality or etale-only clause. The shift is [-q], consistent with the convention that H^q is placed in cohomological degree q. The base case, finite index range and induction successor are all explicit. This generic truncation theorem is the only non-leaf off-unit theorem used and is declared as a tool in `split_report.tool_uses`; it implements the unit's bounded devissage rather than replacing its route.

Step 5 counts the two finite inductions and shifts. This is elementary bookkeeping from earlier steps, not an extra generation lemma. No step exceeds 2000 characters (lengths 789, 632, 781, 716 and 647), and no independent comparison lemma is hidden in them.

I checked the empty scheme, zero sheaf, acyclic complex, single-degree complex, a nontrivial two-step sheaf extension and an integral torsion local model such as O_E/varpi. Length-zero filtrations and the zero object handle the first cases; one truncation step handles a single-degree sheaf; the sheaf triangle and the Postnikov triangle have the needed first and third terms in every successor case. Torsion never needs to be free, and arbitrary coefficient rings never need to be coherent or of finite global dimension. Nothing requires the class to be closed under retracts or infinite sums.

Against delivery-errors B–E: no new statement-only node or duplicate is introduced; every non-elementary input has an existing node; quotations in citations.json are verbatim substrings of the actual statements; no source proof is substituted for a missing statement; neither induction is circular; the proof does the assembly rather than renaming its clauses. All statement dependencies are retained because their notions occur explicitly in the unchanged statement. There is no SGA citation in the delivery. No repository files, Lean files, launcher scripts or build tools were changed or run.

## Unfinished work

None at stage 1. This report and split are submitted to the required server dry run before pushing.
