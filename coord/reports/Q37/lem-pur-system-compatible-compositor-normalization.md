# Stage-1 delivery: lem-pur-system-compatible-compositor-normalization

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-system-compatible-compositor-normalization.json: statement, split into six proof steps; not a Mathlib match.
- citations.json: 22 step/node entries containing verbatim statement excerpts.
- searches.jsonl: actual additional Mathlib searches, retaining their returned names and service status.
- report.md: this report.

There are **0 new nodes and 0 Mathlib leaves**. The existing item statement and its statement dependencies are unchanged. Its existing blueprint ancestry and specific old-Step-5 place are retained, and same_as is confirmed as empty. No unit realization is edited: this item is not its unit's key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for compositor, proper/open, compactification composition and normalization. The finite etale LowerShriekComposition source describes the compatible compactification word, but does not state this assertion about actual derived semilinear systems with arbitrary levelwise bounds. An etale compositor alone is not an attachment for this item.

## WANTED

None. The proof's sources are available locally. No SGA source is used.

## Corrections and scope

The incoming item had no proof. I supplied the assembly rather than transferring its clauses into new nodes. Existing lem-pur-system-proper-open-invertibility already states the nontrivial invertibility and finite normalization needed here; lem-sf-semilinear-compositor-coherence supplies actual system compositors, where the incoming fixed-ring composition reference alone would not justify a transformation on systems. These facts are cited in the proof without changing their nodes.

The semilinear extension is an agent deduction from the existing system-calculus statements, not a theorem claimed verbatim from Stacks 0F7J. Stacks supplies the compatible compactification construction and its proper/open word. Finite identification uses the existing finite-site word and coherence equations, rather than an inference that evaluations are faithful. The domain remains all systems whose individual levels have bounded constructible cohomology; no normalization, uniform bound, finite Tor amplitude or flat quotient transitions are added.

The blueprint search covered the whole DAG via blueprint_refs search for compositor, semilinear, proper and open, and compactification, and DAG searches by Tag 0F7J and proper/open terminology. The ordinary finite composition theorem, constant-ring strict-tower calculus and uniform finite-Tor tower composition nodes have different domains from this item. Their existing smaller inputs suffice, so no duplicate node was made.

Mathlib was searched using msearch.py only: two semantic phrasings with LeanFinder, one LeanSearch phrasing, Loogle CategoryTheory.Adjunction.comp, and a CategoryTheory grep for semilinear systems, shriek and compactification. Semantic hits concerned compactly supported functions or ordinary sheaf pullback/pushforward; Loogle concerned ordinary composition of adjunctions; grep found no hit. None supplies the specified geometric derived-system composition word. All five queries are recorded exactly as run; the item's earlier search records are retained.

## Not duplicates

No new node is proposed. In particular I reused the compatible compactification triangle, system proper/open invertibility, semilinear compositor coherence, finite-site tower paste, and finite compact-site coherence rather than creating versions of them.

## Review by Q37

I read AGENTS.md, the worker role and stage-1 brief, the three levels in SETUP.md, GOAL.md, the open-stage information, stages/1-dag.md and tools/README.md, and delivery-errors B through E. I read this item's chapter and sk-thm-sf-compatibility unit record and the main-20261015 ancestor statement/proof. The ancestor concerns adic transport of coherence; its parent split's old Step 5 isolates precisely the compatible-triangle word proved here. I read Stacks more-etale.tex, Tag 0F7J (lemma-shriek-composition), including its actual compatible diagram and four displayed identifications, and Tag 0F7B (lemma-shriek-proper-and-open), and the main-20261015 finite composition construction. No new node needs an independent source.

For Step 1 I checked the statements of def-weil-finite-type-morphism and lem-wf-affine-noetherian-components: the first gives finite affine covers over the field and the second gives Noetherian coordinate rings. The statement of lem-weil-pbc-locally-noetherian-quasi-separated supplies quasi-separatedness, so the triangle lemma's qcqs hypotheses hold. I read lem-weil-pbc-compatible-compactification-triangle, whose statement explicitly supplies the Cartesian square, both quasi-compact opens, both proper verticals, and the two compactifications. The renaming in the step is literal. The statements of lem-weil-pbc-proper-fp-permanence and lem-weil-pbc-qcqs-morphism-permanence check separatedness, local finite type and quasi-compactness for the ambient schemes; thus finite-site Noetherian hypotheses are not silently imposed.

For Step 2 I checked lem-coef-semilinear-derived-sections for existence of transformations on the whole ordinary derived system categories, including quotient transitions and adjunction words. I read lem-sf-semilinear-proper-open-mate-pasting in full: it defines the intrinsic clopen-projection mate used in the item. Cartesianity makes the induced clopen map an isomorphism to the whole fibre product, so its projector is the identity under that identification. The statement of lem-sf-semilinear-compositor-coherence gives the exact normalized right-adjoint direct-image compositor and open-adjoint compositor. I checked all four sources and targets in the displayed word: the first goes to R_s R_p1 J_b1 J_j, the second contracts the proper maps, and the third contracts the opens. This proves a construction in D(S), not a putative lift of evaluated arrows.

For Step 3 I checked lem-sf-open-finite-constructibility-interval, whose statement explicitly preserves the same cohomological interval and finite-stratified constructibility for exact extension by zero. Its finite-torsion notion agrees with the intrinsic definition here (I opened def-weil-finite-torsion-constructibility and def-weil-proetale-constructible-sheaf). Its Noetherian and invertibility-of-ell hypotheses follow from Step 1 and ell different from char(k). Evaluation/open compatibility is in lem-coef-semilinear-derived-sections. I read the full statement of lem-pur-system-proper-open-invertibility; it applies to H=J_j M on V, states invertibility of this precise mate, and expressly requires no uniform interval. Applying a functor to an isomorphism and composing isomorphisms are the remaining elementary operations.

For Step 4 I checked clause (ii) of lem-sf-proetale-constructible-origin: it supplies bounded etale witnesses, not merely fully faithful sheaf comparison. The finite normalization clause of lem-pur-system-proper-open-invertibility identifies the specified evaluated mate. I also read lem-cbc-finite-clopen-mate-site-transport, including its displayed equation, which specifies the canonical counit and open comparisons and says that these give exactly the finite etale proper/open normalization. The system sections statement explicitly says evaluation, composition and specified adjunction transposes agree with the level constructions. These statements support the named-map identification, without a faithfulness claim about evaluation.

For Step 5 I read the entire statements of lem-sp-finite-site-tower-paste, lem-sp-finite-compact-site-coherence and thm-sf-comp-composition. The former defines A^p by the same three factors, identifies A^e with the normalized etale compositor, and states the displayed transported word equation; the latter coherence node identifies computed pro-etale proper/open pastes with that transport. The finite theorem names alpha on bounded-below etale-origin objects and states preservation of the intermediate origin class. I verified the substitution (a,b,p,q,s,i)=(j,b1,p1,s,q,i), all properness and quasi-compact-open assumptions, finite coefficient ring A_n, and individual bounded-below witnesses. Thus the cited statements give the comparison of actual named arrows, rather than only existence of an isomorphism. Its naturality in witnesses handles their choice.

For Step 6 I checked identity-square normalization in the semilinear mate node and unitality in the semilinear compositor node. I wrote the two compatible diagrams explicitly for f=1 and g=1 and checked the remaining factors are unit comparisons. For an empty open the exact open functor in the section model is the zero functor, so the word is the unique zero-object isomorphism; when the target open is empty the existence of f forces X empty too. The argument also works for the zero complex and n=1. As a test of the absence of a common-bound assumption, nothing in the proof fails if the support interval of M_n is shifted by n: only its individual finite interval is used. No Tor condition appears in any application.

I checked each used node's statement directly, selected the quoted excerpt from that statement, and verified the citations are literal substrings. I checked that none of the proposed proof dependencies has a dependency path back to this item. Each non-elementary step is shorter than 2000 characters; none conceals a new comparison lemma. I corrected the initial assembly to cite locally-Noetherian quasi-separatedness and morphism permanence explicitly, and to use the existing finite-site word equation for the final normalization instead of citing the finite composition theorem's existence clause alone. The item uses only existing smaller results; no clause is relabelled as a new lemma. The necessary off-unit inputs are declared as generic tools in split_report.tool_uses.

## Unfinished work

None in this one-level split. The proof leaves the cited existing unsplit results as their own DAG items, as required by stage 1. Delivery validation and its result are recorded by the required delivery command.
