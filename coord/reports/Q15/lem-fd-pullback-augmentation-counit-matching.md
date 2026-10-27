# Stage-1 delivery: lem-fd-pullback-augmentation-counit-matching

## Files written

- dag/nodes/sec-fourier-transform/lem-fd-pullback-augmentation-counit-matching.json: statement, split into seven proof steps; not a Mathlib leaf. Statement preserved; added the explicit raw-rationalization notion dependency.
- citations.json: 16 statement excerpts, one for each step/node citation, checked as literal substrings of the live statements.
- report.md: this report. searches.jsonl contains the command-generated Mathlib search record. write_split.py is sandbox-only preparation, not a delivered project file.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the actual Lean source under lean/WeilConjectures for the exact blueprint id, quotient augmentation/counit combinations, strict Roos names and completed pullback terminology. No project declaration states every clause of this item. Generic Roos and derived-adjunction declarations do not identify the completed pro-etale comparison with the specified chain map and simultaneous system.

## WANTED

None. The source material needed for this split is present locally.

## Corrections and scope

The imported item was statement-only. Its statement is retained, including all noetherian/finite-dimensional/invertibility hypotheses, the coefficient identity transports, the actual quotient transitions, the whole-tower counit, and the simultaneous finite-word domain. The proof does not replace a whole-tower equation by its separate reductions. I added a statement dependency on def-weil-rationalization-karoubi because the item explicitly promises raw rationalization. No mathematical statement dispute was found.

The source of the item is an agent extraction of the final sentence of def-fd-trace-function, rather than a theorem proved in that blueprint paragraph. Accordingly proof_origin.by is agent. I read the current main-20261015 paragraph, the unit sk-def-trace and the fixed chapter sec-fourier-transform, and supported the calculation by reading Stacks Tag 099N (proetale.tex, lemma-pushforward-Noetherian-case, clauses (2),(5) and proof) and Tag 0941 (sites-cohomology.tex, lemma-derived-limit-is-ok and proof). The former describes completed pullback as ordinary pullback followed by completion and as the quotient derived limit; the latter computes that derived limit on a K-injective whole tower and gives the product-cone comparison. Neither source alone asserts the extra chain normalization; the proof records that calculation explicitly using the existing normalized Roos theorem. No SGA source is used.

## Mathlib search results

Preserved the item's six inherited search records. Ran five further searches through the required msearch.py command and read their results: LeanFinder on strict augmentation/Roos normalization, Loogle on CategoryTheory.Adjunction.derived_counit, grep on Roos and quotient-augmentation words, LeanSearch on a strict augmentation into the cone, and a second LeanFinder phrasing on the K-injective counit. All services answered. The first semantic searches returned Dold--Kan, truncation and ordinary limit facts. The counit phrasing returned constLimAdj, coneOfAdj and ordinary cone adjunction lemmas. None states this item or a one-line specialization. Read Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean, especially derivedε and derivedε_fac_app at lines 114–132; its generic derived-counit factorization needs the present site, quotient system, comparison and normalization work. Thus the item remains split, with no Mathlib match.

## Not duplicates

No nodes are created, so there are no new/existing-node pairs requiring a distinction. Whole-blueprint searches for Roos, quotient augmentation and limit counit did not identify an imported node stating this whole item. Reused lem-weil-strict-roos-comparison, lem-fd-pullback-common-strict-tower-models and the existing trace-formula realization and substitution nodes; did not create augmentation, product, counit or finite-word restatements. In particular the common-tower node is used only for its actual shared model, naturality and restriction assertion; it does not assert this item's matching equation.

## Tool uses

The split_report declares the five nonlocal statement tools: exact countable pro-etale module products; normalized strict Roos comparison; effective simultaneous realization models; the specified integral pullback realization system; and whole-system counit substitution. These are the generic coefficient/homological tools explicitly required by this extraction. They do not replace any step of the trace-function unit (whose record has no proof steps). The common strict-tower node is in the same unit. Definitions used for raw localization and the specified operations are notions.

## Review by Q15

I checked delivery-errors B–E with the item, cited statements and the above local sources open. There are no new unsplit nodes carrying hidden proofs, duplicate lemmas or repackaged clauses. The original statement has not been weakened, and the chapter and unit records are untouched. Every non-elementary result is explicitly named; the only elementary step is the quotient-generator and cone-differential computation.

Step 1 uses the statement of lem-fd-pullback-common-strict-tower-models: it explicitly identifies the two realizations of the identical tower, gives the normalized comparison on ambient categories, independence and naturality, and the integral restriction. Its hypotheses are exactly the allowed schemes, scheme isomorphism and flat-term K-flat representative already fixed in the item. I checked that it has no dependency path back to this item.

Step 2 uses the definitions of integral derived operations and PBC completed pullback. The former gives reductions of a single representative with their actual quotient transitions and termwise finite inverse image; the latter explicitly constructs the completion map from the strict quotient augmentation. The tensor-unit formula is written out, then reduction sends 1 to 1, giving strict transition compatibility. Since each component is a chain map and (1-s)a=0, the shifted-cone differential gives the chain equation with zero shifted coordinate. This is an elementary computation from those definitions, not a new lemma about arbitrary completion.

Step 3 checks the exact-product hypothesis of lem-weil-strict-roos-comparison using lem-weil-proetale-countable-products-exact with the completed coefficient ring on the small pro-etale site. The Roos statement explicitly concerns a strict augmentation, not merely its finite evaluations. The factorization through lim I and equality H(q)Gamma=iota_I bargamma are given on both cone coordinates. The PBC definition identifies this same derived strict-augmentation map as its actual completion unit. This verifies the matching equation with the recorded ordinary derived-pullback factors; no presumed uniqueness of maps from their quotient components is used.

Step 4 reads def-fd-finite-pullback-comparison-datum literally: its comparison goes from PBC to framework. Hence it is the inverse of b that is required. Left multiplication by that inverse yields exactly the requested normalization. The common-tower statement supplies the restriction to constructible objects and its ambient lift; def-fd-coefficient-comparison-datum fixes the identity transports. The raw-localization definition gives the integral Hom tensor E formula, so sending f and its inverse to f tensor 1 and f inverse tensor 1 preserves the equality and inverse laws. I restricted this datum to representatives with constructible derived image as required in its definition.

Step 5 uses the explicit statement of lem-trf-effective-comparison-realization-models, which supplies the entire-tower formula [q] inverse composed with the ordinary limit cone and identifies its derived-change-of-rings adjunct. I wrote the source change by Delta(rho) and cancellation explicitly, so the counit formula is correctly typed before and after Roos transport. The statement of lem-trf-integral-pullback-comparison-realization uses this same whole-tower counit and then quotient action counits and tensor associators. Thus it really supplies the desired quotient-system identification; a definition of completion or the existence of finite projections alone would not have sufficed.

Step 6 uses the simultaneous-existence assertion of the effective-model node, including its flat-term K-flat representative normalization, actual transitions and zero shifted coordinate. The strict Roos comparison statement supplies the unique specified formula and resolution independence used here. The integral-realization statement specifies the comparison families formed with those counits. These are compatible choices for every index, rather than independently chosen finite-level comparison arrows.

Step 7 applies lem-trf-counit-realization-substitution only on its stated domain: normalized systems, with constructible-complete intermediate realizations. It explicitly gives r_O, the concatenation identity r_vw, independence of parenthesization, and equalities for morphisms of entire derived quotient diagrams. The proof specifies the empty-word base and concatenation step. Its scalar-completion compatibility includes equality of fields and successive extensions, matching the supplied coefficient data. The finite-word restriction in the item is retained, and no finite Tor-amplitude or flatness of coefficient quotients is assumed.

I tested the normalization at the zero complex (all maps zero), h the identity (gamma is the ordinary quotient unit), n=1 and a constant tower with identity transitions ((1-s)a=0 and zero shifted coordinate still hold), and the empty operation word and repeated coefficient fields (identity comparisons). These tests also check the inverse-comparison orientation. All proof steps are under 1000 characters; none hides a lemma in a long step. A read-only dependency traversal confirmed that the common-tower, strict-Roos, integral-realization, effective-model and substitution tools have no path back to this item. citations.json quotes were verified against statement fields, not proofs.

## Unfinished work

None in the stage-1 split. Lean writing, compilation and global builds were neither performed nor requested.
