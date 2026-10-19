# Stage-1 report: lem-coef-accessible-pie-closure

Group NE; 2026-10-17. Sandbox: `/home/ubuntu/weil-newtargets-sandbox/NE/lem-coef-accessible-pie-closure/`.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-accessible-pie-closure.json`: item, split into twelve proof steps; statement unchanged.
- `dag/nodes/sec-six-functors/lem-coef-accessible-system-ranks.json`: statement-only uniformization/rank lemma; unsplit, no match in the installed Mathlib.
- `dag/nodes/sec-six-functors/lem-coef-accessible-presentable-density.json`: statement; Mathlib leaf for accessible categories, `Presentable/Dense.lean:60-72`.
- `dag/nodes/sec-six-functors/lem-coef-accessible-set-functor-limits.json`: statement; Mathlib leaf, `Functor.isCardinalAccessible_of_isLimit`, `Presentable/Limits.lean:158`.
- `citations.json`: twenty-one verbatim statement quotations for all node citations in the item's proof.

`write_split.py` is sandbox-only scratch work. `searches.jsonl` was written by the required search command. No repository, launcher, Lean source, unit or chapter file was changed. No compiler or build tool was run.

## Attachments

None. I searched `WeilConjectures/` in the supplied slopmaster2 source by the item tag, accessible, inserter, equifier, uniformization and the supporting declaration concepts, and checked the exact upstream master for the item tag and PIE terminology. There is no project declaration giving all three clauses. The project addition `WeilConjectures/Mathlib/CategoryTheory/Presentable/Limits.lean` concerns limits of set-valued functors; it does not assert closure of accessible categories under PIE constructions.

## WANTED

WANTED: Adamek--Rosicky, *Locally Presentable and Accessible Categories*, Theorem 2.11 and Uniformization Theorem 2.19 (including their cardinal-enlargement proofs), for lem-coef-accessible-system-ranks. The full book was not available in the permitted literature tree. I read the single-functor theorem and sharp-rank stability in Beke--Rosicky, *Abstract elementary classes and accessible categories*, section 3, printed p. 5, and the sharp-cardinal discussion in Brooke-Taylor--Rosicky, *Accessible images revisited*, section 2, printed p. 3. The small-system statement bounds a small family of the generator and image ranks; it is labelled agent-formulated rather than falsely presented as a verbatim quotation.

WANTED: archive of Positselski, *Notes on limits of accessible categories*, sections 1-4, printed pp. 395-407, for the item proof. I read the publisher's PDF online at https://cahierstgdc.com/wp-content/uploads/2024/10/Positetski-LXV-4.pdf, especially Lemma 1.1, Proposition 2.1, Proposition 3.2, Proposition 4.2, Lemma 4.5 and the proofs of Propositions 4.3-4.4. I did not download it into the shared tree. The proof_origin is therefore agent, with the permitted blueprint document as its primary provenance and the online comparison stated explicitly.

WANTED: local archive of Ching--Riehl, *Coalgebraic models for combinatorial model categories*, Appendix A. I read https://math.jhu.edu/~eriehl/coalgebraic.pdf, printed pp. 9-11, to verify the inherited source. It cites Makkai--Pare 5.1.6 for the theorem; citing this assertion alone would not split the item.

There is no identified Stacks tag for ordinary accessible-category uniformization or PIE closure. I did not invent a tag or cite SGA.

## Findings and corrections

The imported statement is mathematically sound and is unchanged. Its empty proof was the missing content. The source's phrase “ACC has PIE limits” is the item itself, so I did not introduce an identically worded child or one child for each clause. The new rank node only supplies cardinals; the existing density node and new set-functor leaf supply canonical ambient presentations and a Hom calculation. The item's twelve steps contain the product, inserter and equifier arguments.

The unit binding inherited from the repository is `sk-prop-sf-biduality-general`, whereas the nearest blueprint ancestor and current source path run through `prop-coef-integral-exceptional-adjoint` in `sk-thm-sf-package`. I read both the inherited unit record and the current main-20261015 ancestor proof. This is a categorical auxiliary below the units, and I did not change maintainer-owned metadata or unit realizations. None of the new proof citations changes the geometric or coefficient route. The item is not the statement node of the inherited unit.

The phrase “no fixed common accessibility cardinal” is respected: each application chooses a suitable rank; no claim at the original input ranks is made. The original inputs are accessible ordinary categories, not assumed locally presentable. In particular the neighboring locally-presentable inverse-image and rank lemmas cannot be substituted for their accessible analogues.

Online Loogle finds newer Mathlib declarations `IsCardinalAccessibleCategory.uniformization_of_small`, `uniformization_pair`, and `uniformization`. Their module `Presentable/Uniformization.lean` is absent from the supplied installed Mathlib; the required grep confirms this. Furthermore their displayed conclusions do not by themselves contain the present statement's small varying family of categories together with a prescribed lower bound and a separate lower colimit rank. I recorded them as candidates in the search results, not as locally verified Mathlib leaves. All searches recorded on new nodes were actually run with msearch.py; the recorded top-hit summaries come from its log. Semantic services were available during these searches.

## Not duplicates

- lem-coef-accessible-presentable-density vs lem-coef-presentable-canonical-density: the existing statement assumes all small colimits and local presentability; this leaf works in any kappa-accessible ordinary category and does not assume cocompleteness.

- lem-coef-accessible-system-ranks vs lem-coef-accessible-functor-presentability-ranks: the existing node requires two locally presentable categories and a single functor; the new statement handles a small system of merely accessible categories, without cocompleteness, and supplies a lower filtered-colimit rank strictly below a prescribed large strong rank.
- lem-coef-accessible-system-ranks vs lem-coef-presentable-cardinal-enlargement: the existing node is for a presentable infinity category and compact endpoints; the new statement is ordinary categorical uniformization for functors and merely accessible categories.
- lem-coef-accessible-system-ranks vs lem-coef-infinity-compact-approximation: the latter concerns infinity-category compact approximations, not common ordinary strong ranks.
- lem-coef-accessible-presentable-density vs det-ind-heart-canonical-presentation: the latter concerns the particular coefficient heart and constructible objects; the new Mathlib leaf is the ordinary general canonical presentation for any cardinal-accessible category.
- lem-coef-accessible-presentable-density vs lem-coef-accessible-diagram-presentations: the latter is an infinity-category functor-diagram assertion with additional cardinal hypotheses; it does not state the ordinary canonical costructured-arrow cocone and its filteredness.
- lem-coef-accessible-set-functor-limits vs lem-weil-pbc-filtered-colimits-commute-finite-limits: the existing node covers finite limits and ordinary filtered colimits; the new leaf allows arbitrary fewer-than-kappa morphisms and kappa-filtered colimits, needed for a small product and the lambda-chain Hom calculation.
- lem-coef-accessible-set-functor-limits vs lem-coef-spaces-kappa-limit-filtered-colimit: the latter states the coherent infinity-categorical spaces theorem, with its enhanced-diagram definitions; the new node is the installed ordinary set-valued functor theorem with no enhancement or infinity-category hypotheses.
- lem-coef-accessible-set-functor-limits vs lem-weil-pbc-finite-colimit-finitely-presentable: the latter is the finite/aleph-zero specialization and concerns objects; the new node is the general functor-limit theorem at any regular cardinal.

I searched the whole DAG by these keywords, literature places and expected declarations, and ran blueprint_refs.py searches for accessibility, uniformization, canonical diagrams, presentable functors and small limits. No blueprint node states either new fact. Each has nearest ancestor `prop-coef-integral-exceptional-adjoint`, the inherited exact proof place, and via list beginning with this item. `same_as` is empty after those searches.

## Review by NE

I reviewed this split against delivery-errors B-E with the node statements and source text open. The rank node has only its statement and searches, no hidden proof sketch. The live DAG also contains a locally presentable density node; the accessible density node in this split has the weaker hypotheses needed here and was checked against the accessible Mathlib instances. Every new statement introduces its universe, objects, relevant cardinal notions and hypotheses; none depends on the item, so there is no proof cycle through the parent. Its ordinary colimit notion cites the existing definition. TeX strings use single mathematical backslashes after JSON decoding.

For step 1, I checked that the rank node explicitly supplies both the lower colimit rank and the upper accessibility/presentability rank; mere existence of an accessible-functor rank in Mathlib Basic would not suffice. A regular ordinal lambda is lambda-filtered, which accounts for exactly the chain colimits used later. There is no use of arbitrary small colimits. The source for this auxiliary is the uniformization material described in WANTED; its small-system extension is an unsplit lemma rather than an unproved assertion hidden in this step.

For step 2, I read `Functor.isCardinalAccessible_of_isLimit` at installed `Presentable/Limits.lean:158-168`. Its bound is on all arrows of the index category; a lambda-chain has lambda arrows for infinite lambda and lambda is strictly below kappa. Taking the opposite shape for the Hom-of-colimit calculation preserves that bound. Discrete products and equalizers satisfy the same bound. The stage factorization/equality assertion is explicitly derived from the Hom comparison and the elementary disjoint-union quotient description of filtered colimits of sets; simultaneous requirements are fewer than kappa, not merely finitely many.

For step 3, I read both exact instances in installed `Presentable/Dense.lean:60-72`, and the meaning of density in `Functor/KanExtension/DenseAt.lean:45-58`. The cited node gives both filteredness and the specific colimiting cocone, not just full faithfulness of Yoneda. I supplied the separate retract/idempotent argument giving a small representative set. This avoids taking a colimit over the possibly large collection of all presentable objects. The small-family witnesses in every subsequent use are these representatives with small Hom sets.

For step 4, the cited colimit definition gives coordinatewise universality and the functor-limit leaf gives presentability only after choosing kappa greater than the product's index size. Density supplies the coordinate presentations. Product index categories are small and nonempty; cones are chosen coordinatewise. A projection has connected nonempty fibers because the other indices are filtered, so its cocones reduce to the coordinate cocones. I checked the empty product separately and the product with an empty factor separately; no nonempty category was assumed silently.

For step 5, the inserter colimit construction uses preservation by F to define the structure and the universal property to verify the morphism equation. The equalizer calculation uses FP being kappa-presentable and preservation by G, both supplied in step 1. The cited functor-limit node states exactly the equalizer preservation needed. I checked the types of both equalizer arrows: they start at Hom_A(P,X) and end at Hom_B(FP,GX).

For steps 6-7, I compared the explicit chain construction to Positselski Lemma 4.5 and the proof of Proposition 4.3. The initial family of structures is arbitrary of cardinality below kappa, so it covers all the objects in a small diagram, not just one map. All equations have source FP_a or FT_j, which are presentable by step 1; equality is enforced at a successor after it holds in GX. At proper limits, a cone is taken in the canonical filtered category from the density node; this does not assume colimits at ordinals below lambda. Only the final lambda-chain colimit is taken in A. The functor-limit node proves its underlying object presentable, and preservation by F permits the structure on the colimit. The argument explicitly retains the original cone equations and verifies the resulting structure maps.

For steps 8-9, I checked that the small objects of the inserter form a small family because their structures are in small Hom sets. The density node supplies the underlying cone; the already proved extension construction makes all its legs structure morphisms. The empty diagram proves nonemptiness. The colimit argument is written via descent of arbitrary cocones: two choices are joined after equalizing the underlying P-arrows and then extending the structure while retaining that equality. Thus no uncited cofinality theorem is doing work, and the cited definition and canonical-density statement give exactly the final universal property. This also proves the accessibility of the projection by the colimits already constructed.

For steps 10-12, I checked the source's equation-killing chain against Proposition 3.2 and Theorem 3.1. The inclusion is full; preservation by F alone makes a colimit satisfy the equifier equation, while preservation by G and presentability of FT_i provide the eventual equality used in the chain. The lower-chain and upper-presentability hypotheses are the same two ranks from step 1. The density and functor-limit nodes have precisely these hypotheses. The resulting small full subcategory of equifier objects has a filtered canonical arrow diagram; its colimit follows by the explicit cocone argument already written, not by claiming an arbitrary full subcategory inherits accessibility. An empty equifier is allowed.

Small-case checks: terminal and empty categories; the empty and singleton product; a product containing an empty category; inserters of identity functors on Set (ordinary endomorphism objects) and of functors between discrete categories with disjoint values (empty inserter); equal natural transformations (the whole source) and an equifier with no objects; finite kappa-small limits when kappa=aleph-zero; lambda-chains only after passing to the uncountable upper rank kappa. These examples expose no missing nonemptiness or cocompleteness assumption. I specifically avoided the false shortcut that arbitrary accessible categories are accessible at every larger regular cardinal.

## What remains unfinished

The item's one-level split is complete. The new rank lemma remains unsplit by design for its own later worker; its full book proof remains WANTED. No project Lean proof or stage-2/3 work is claimed. No delivery has been pushed; this sandbox is for the independent second reader.

## Dry run

`python3 /home/ubuntu/weil-launcher-nt/deliver.py NE lem-coef-accessible-pie-closure --no-push` printed `OK (not pushed) ... preflight passed` on 2026-10-17 (first accepted check commit `d668cd24ed`). The server preflight includes check_dag and review_split. No delivery was pushed. This report records that observed pass; a final identical command is run after this report update so the handed-over report is checked too.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against the blueprint paragraph named in `source` and the accessible-category hypotheses; the three PIE clauses and the no-common-rank qualification are retained.
- Step 1: checked against `lem-coef-accessible-system-ranks`; its separate lower chain rank, upper accessibility rank, functor preservation, presentable-image, and $|S|<\kappa$ consequences are used exactly.
- Step 2: checked against `lem-coef-accessible-set-functor-limits` and the colimit definition; the Hom-limit calculation, stage factorization/equality, and fewer-than-$\kappa$ simultaneous refinement are stated explicitly.
- Step 3: checked against `lem-coef-accessible-presentable-density`; the retract/idempotent argument and transport to a small representative family supply the extra smallness used later.
- Step 4: checked against the colimit definition and both supporting leaves; coordinatewise products, empty products, empty factors, filteredness, and presentability use the stated bounds.
- Step 5: checked against the colimit definition, the set-functor limit leaf, and the rank node; inserter colimits, the Hom equalizer, and preservation of the two chain ranks have the needed hypotheses.
- Step 6: checked against canonical density and the rank bounds; the successor factorization, simultaneous eventual equalities, and limit-stage cone are written without assuming unprovided intermediate colimits.
- Step 7: checked against the colimit definition and set-functor limit leaf; the chain colimit, induced inserter structure, presentability, and retention of prescribed equalities follow from steps 2 and 6.
- Step 8: checked against canonical density and the preceding extension construction; representative transport is now explicit so the filtered cone really lies in the small structured category.
- Step 9: checked the direct cocone descent against canonical density and the colimit definition; representative transport is explicit in both extension and equalization stages.
- Step 10: checked the equifier argument against the colimit definition and the rank node; it is no longer marked elementary because preservation of both ranks is a cited non-elementary hypothesis.
- Step 11: checked against canonical density, the set-functor limit leaf, the colimit definition, and the rank node used earlier; successor equality killing and the final equifier structure are typed at $FT_i$.
- Step 12: checked against canonical density and the colimit definition; representative transport is explicit, and the filteredness and cocone descent arguments apply to the full equifier.
- `lem-coef-accessible-system-ranks`: statement-only unsplit auxiliary; checked its universe, small-family, lower-rank, upper-rank, functor, and presentable-image clauses against the cited uniformization sources and small edge cases.
- `lem-coef-accessible-presentable-density`: Mathlib leaf; checked the accessible-category costructured-arrow orientation, filteredness instance, and canonical colimit instance at `Dense.lean:60-72`. The preflight-found existing node is the distinct locally-presentable theorem, so this node was renamed to make the hypothesis difference explicit.
- `lem-coef-accessible-set-functor-limits`: Mathlib leaf; checked the pointwise limit statement and the `<\kappa` arrow bound against `Limits.lean:158-168`, including the empty index case.

Changes made in this second reading:

- Renamed the density leaf after preflight found the existing ID reserved for the stronger locally-presentable theorem; the new accessible-category statement remains distinct and its Mathlib instances are exact.
- Added explicit transport from each newly constructed presentable object to the selected small representative in inserter steps 8-9 and equifier step 12; without this, the claimed filtered categories were not closed under the constructed cones.
- Added the common-rank node citation to step 10 and changed its flag to `elementary: false`, because the proof uses preservation of both $\kappa$-filtered colimits and $\lambda$-chains.
- Added the corresponding verbatim citation entry for step 10 in `citations.json`.

## Continuation audit by NE

I reread all twelve proof steps and the three supporting statements against delivery-errors B-E. The actual text of steps 3, 4, 8, 9 and 12 still named the older locally-presentable density node although their uses lists and citations.json named the accessible density leaf. I corrected all five textual labels and rebuilt proof_deps from the uses lists, removing the same stale density ID there. The mathematical statements are unchanged. The density leaf was checked at installed Mathlib Dense.lean:60-73, including its canonical cocone through DenseAt.lean:45-58. The limit leaf was checked at installed Limits.lean:158-168; it assumes no accessibility or cocompleteness of the source.

I read the current ancestor proof, both relevant unit records, and the chapter record. The inherited unit discrepancy remains reported above, with no metadata edit. I independently reread Positselski sections 1-4 online and the cited uniformization passages of Beke--Rosicky and Brooke-Taylor--Rosicky. The approximation chains use a lower colimit rank strictly below the presentability rank; successor stages impose fewer than kappa equations, and proper limit stages use filtered cones, not nonexistent intermediate colimits. I also checked the small representative transports and the direct cocone descent in steps 8-9 and 12. The empty cases in the earlier review remain valid.

I repeated the whole-blueprint accessibility, uniformization and presentability searches, read the current locally-presentable density and rank nodes, and confirmed their stronger hypotheses do not replace these accessible-category inputs. Searches in the project Lean source still give no attachment of the item. I reran the rank semantic, Loogle and installed-source grep searches with the required msearch command; Loogle's newer uniformization candidates remain absent from the installed checkout. The existing logged queries for all three new nodes are retained, without inventing a search.

Seven inherited item search queries were not in this sandbox's search log. I replayed those exact queries through msearch.py and replaced their result fields with the literal current command output. They give no PIE-closure theorem; the Inserter/Equifier grep also matches unrelated InsertErase section names, which I excluded after reading the hits. Every recorded item and new-node query now has a matching local log entry.

The continuation dry run printed `OK (not pushed) deliver/NE/lem-coef-accessible-pie-closure at d5210cce8f: preflight passed` on 2026-10-17. It includes the corrected citation labels, proof_deps and authenticated searches. The required final no-push check is repeated after this report update; the sandbox is then left unchanged for the next reader.

## Second reading by NE

- Item statement: checked the current blueprint ancestor paragraph (which does not itself state PIE closure) and Ching--Riehl Appendix A, printed pp. 9–11; its general accessible-PIE assertion and explicit constructions agree with all three clauses and the projections. Positselski Proposition 2.1 supplies the small-product form. The no-common-rank qualification is respected. PASS.
- Step 1: checked against `lem-coef-accessible-system-ranks`; the separate lower chain rank, upper accessibility rank, functor preservation, presentable-image condition, and small-family bound are all supplied. PASS.
- Step 2: checked against `lem-coef-accessible-set-functor-limits`; the opposite-index Hom calculation, stage factorization, eventual equality, and fewer-than-κ simultaneous refinements are stated explicitly. PASS.
- Step 3: checked against `lem-coef-accessible-presentable-density`; canonical filtered density, retract representatives, small idempotent choices, and transport along representatives support the later small diagrams. PASS.
- Step 4: checked against the colimit definition and both supporting leaves; coordinatewise products, empty products, empty factors, filteredness, and presentability have the required bounds. PASS.
- Step 5: checked against the colimit definition and the set-functor limit leaf; inserter colimits and the Hom equalizer use exactly the preservation and presentability hypotheses in force. PASS.
- Step 6: checked against canonical density and the rank node; the successor factorization, simultaneous equations, and limit-stage cones are explicit and do not assume intermediate colimits. PASS.
- Step 7: checked against the colimit definition and set-functor limit leaf; the chain colimit, induced inserter structure, presentability, and retention of prescribed equalities follow from prior steps. PASS.
- Step 8: checked against canonical density and steps 6–7; the structured cone and transport to the selected representative make the small inserter diagram κ-filtered, including the empty diagram. PASS.
- Step 9: checked against canonical density and the colimit definition; the joining and equalization argument gives the underlying colimit and hence the inserter accessibility claim. PASS.
- Step 10: checked against the colimit definition and the rank node; preservation by F makes the equifier closed under the relevant filtered colimits and chains, and fullness gives the inclusion claim. PASS.
- Step 11: checked against canonical density, the set-functor limit leaf, and the colimit definition; the equation-killing chain reaches an E-object while preserving κ-presentability. PASS.
- Step 12: checked against canonical density and the colimit definition; representative transport, filtered cones, and cocone descent establish accessibility of the equifier and its inclusion. PASS.
- `lem-coef-accessible-system-ranks`: statement-only unsplit node; checked self-containment, separate λ and κ roles, edge cases, and all three recorded Mathlib searches. PASS.
- `lem-coef-accessible-presentable-density`: Mathlib leaf; checked the exact density and filtered costructured-arrow instances in `Presentable/Dense.lean:60–72` and the DenseAt meaning. PASS.
- `lem-coef-accessible-set-functor-limits`: Mathlib leaf; checked the exact pointwise limit preservation declaration in `Presentable/Limits.lean:158–168`, including the empty index case. PASS.

Changes made in this second reading:

- Expanded the chain-colimit arguments in steps 5 and 10, replacing “the identical/same argument” with the colimit legs and the equation being checked (E5).
- Wrote the representative conjugation formulas in step 8 and the naturality calculation showing the equifier is closed under representative isomorphisms in step 12 (E5).
- Expanded step 12’s appeal to step 9 into the cocone descent, independence, compatibility, recovery, and uniqueness argument (E5).
- Independently searched with new CostructuredArrow, strong-accessibility, and limit-declaration wording through msearch.py; appended the actual log records and verdicts to the three nodes. The density and limit statements remain exact Mathlib leaves; the simultaneous merely-accessible rank statement remains unsplit.
- Checked all 21 citation quotations against the current statements; the statements and uses lists did not change, so `citations.json` remains correct.

The first worker’s sections, all node statements, all new-node statuses, and the earlier repairs remain in place. I read the online Positselski sections 1–4 and the Beke–Rosicky section 3 and Brooke-Taylor–Rosicky section 2 uniformization passages, the installed Mathlib sources named above, and the Stacks colimit definition in categories.tex. The rank node is neither an elementary reformulation nor a clause of PIE closure; the two leaves are ordinary accessibility results with no extra cocompleteness hypothesis. Empty and terminal categories, empty/singleton products, empty inserters and equifiers, and the finite-limit case expose no additional hypothesis defect. No statement dispute was found.

Final validation is recorded in `second-reading-dry-run.log`; delivery is run only after that command prints OK.
