## Worker report

Item: lem-trf-resolving-roof-ambient-compatibility. Group: Q92. Stage: 1.

Files written: dag/nodes/sec-trace-formula/lem-trf-resolving-roof-ambient-compatibility.json (unchanged statement, five proof steps, existing dependencies only); citations.json (one verbatim statement quote per step/node citation); this report. The sandbox also contains prepare.py and the genuine msearch searches.jsonl. No repository file, Lean source, launcher script, compiler, or build was modified or run.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. Existing Mathlib leaves provide the quasi-isomorphism fraction calculus, roof representation and common refinement; the existing same-unit lem-trf-resolving-class-derived-descent supplies the bounded-cohomology resolution clause.

## Attachments

None. Searched lean/WeilConjectures for the exact id/docstring tag and resolving/roof/augmentation-compatibility notions. No declaration states every clause. I also read CategoryTheory/DerivedCategory/CommutativeSquareLift.lean: its private homotopy-square lemma and public square-realization theorem allow the representatives to vary; they do not impose the arbitrary covering class, keep E and G fixed, or give the specified S/rho identities. They therefore do not attach this item. The source library contains general resolving-class derived-functor constructions, which likewise do not state this item.

## WANTED

None. The sources used are already present.

## Source and route

Read GOAL.md, the worker brief, stages/1-dag.md, the three levels of SETUP.md, roles/worker.md, tools/README.md, and delivery-errors.md B--E. Read the chapter record sec-trace-formula and unit sk-i-curve-zero. The latest blueprint's sk-i-curve-zero/_section.md and lem-trf-local-term-locality.md/.proof.md were read; the latter's (1)--(2) specialization route is the ancestor through the inherited support chain. This item is a generic homological supporting lemma in that chain, not a new local-term proof or change to the unit. No SGA source is used.

For the mathematical proof I read Stacks derived.tex, proposition-left-derived-exists (0794), including the common roof and resolving replacement and its displayed compatibility square; lemma-subcategory-left-resolution (05T7), including both parts and the good-truncation proof of (2); lemma-acyclic (05RT); and categories.tex, lemma-morphisms-right-localization (04VI) and lemma-equality-morphisms-right-localization (04VJ). The item's formula is a derived strengthening/expansion of the square, with its additional supplied S/rho data used only through the stated naturality. Thus proof_origin is agent, not a claim that 0794 literally states this whole lemma. The source's right exactness and sequential-colimit assumptions concern its larger existence theorem; this roof argument uses none of them. The orientation of the roof is fixed throughout by a = Q(t) Q(s)^{-1}.

## Searches and reuse

Searched the whole DAG for 0794, 05T7, 04VI, 04VJ, resolving, common roof and common refinement. Opened and read the statements of lem-trf-resolving-class-derived-descent, lem-trf-bounded-stage-roof-comparison, lem-trf-right-fraction-dense-subcategory, lem-sfb-subcategory-left-resolution, lem-sfb-functorial-bounded-above-class-resolution, lem-trf-good-truncation-stage-naturality, lem-trf-truncation-colimit-resolving-cover, lem-pc-quasi-isomorphisms-multiplicative-system, lem-pc-right-fraction-representation and lem-pc-right-fraction-common-refinement. The existing resolution clause avoids creating the cohomologically bounded version of 05T7(2) as a duplicate. No off-unit non-Mathlib tool is used.

Ran tools/blueprint_refs.py ancestor for this item and whole-blueprint searches for roof, resolving, and common refinement. None states this combination of a resolving roof, fixed augmentations into an arbitrary target, and the given S/rho comparison. Retained the inherited exact ancestor/via/place and set same_as to []. The split_report explains the immediate 0794 support and the latest ancestor route. This is not the unit's key statement; no unit record is changed.

Ran the prescribed msearch command with LeanFinder, Loogle, LeanSearch and grep; all seven calls succeeded and their returned metadata are retained verbatim in mathlib_searches. Two semantic phrasings were tried. The first broad grep returned unrelated map_eq_iff hits, so subsequent greps restricted DerivedCategory and Localization. Read the actual candidate declarations: DerivedCategory/Fractions.lean 43--88 gives right_fac and right_fac_of_isStrictlyLE, but does not prescribe terms in the arbitrary class or equalize augmentations; Localization/CalculusOfFractions.lean gives the common-refinement relation, already represented by the existing leaf; DerivedCategory/ExactFunctor.lean assumes preservation of finite limits and colimits and hence is not the additive-only assertion. LeanSearch's Q_map_eq_of_homotopy gives one elementary consequence, not the item. The pre-existing Q75 searches are retained as history. No search is recorded that was not executed.

## Not duplicates

No new nodes. The item is not a restatement of lem-trf-resolving-class-derived-descent: only the latter's objectwise resolution clause is used, and the ambient equality into Y, actual homotopy and arbitrary S/rho compatibilities are proved here. The parent lem-trf-bounded-stage-roof-comparison depends on this item and is not cited, so there is no cycle through it.

## Corrections and unfinished work

The imported statement and its statement dependencies are unchanged. It had no proof; the five steps now supply it. During self-review I renamed the auxiliary upper bound to N so it does not shadow the augmentation b. The original source and the current blueprint do not require a statement correction here. No mathematical part remains unfinished. Independent maintainer review remains part of the delivery process.

## Review by Q92

I checked the item's hypotheses and conclusions against the Stacks places above, not just its dependency list. In 05T7(2) P need only contain zero and cover every object by an epimorphism; the item's isomorphism and biproduct closure are extra available hypotheses, not projectivity assumptions. The existing descent node's resolution sentence explicitly applies to cohomologically bounded above U, not only a termwise bounded complex. It has no proof dependency on this item. I did not create a replacement lemma for this sentence or for any clause of the item.

Step 1 uses lem-pc-quasi-isomorphisms-multiplicative-system for the right calculus in the entire K(A), and lem-pc-right-fraction-representation for the precise denominator-to-source/numerator-to-target factorization. Both statements were opened. The definition def-weil-abstract-derived-category explicitly states cohomology factorization through Q; applying these functors to Q(t) = a Q(s) proves t is a quasi-isomorphism. Hence T has the same upper cohomology bound as E. I did not infer quasi-isomorphism preservation from additivity.

Step 2 uses the statement of lem-pc-right-fraction-common-refinement with both denominators equal to 1_T. Its actual conclusion is equality of the composites with the denominators and membership of that common composite in the multiplicative system; here this says u_1 = u_2 is itself a quasi-isomorphism. Its numerator equality is in K(A), hence gives the written homotopy after choosing chain representatives. The calculus node applies to all complexes; Y is allowed to be unbounded. This avoids applying the bounded-subcategory theorem to a sink outside that subcategory.

Step 3 uses exactly the quoted resolution sentence in lem-trf-resolving-class-derived-descent, after transferring the bound along u. Its hypotheses match the item's class P and abelian A (the auxiliary B is already supplied by the item). Cohomology and composite quasi-isomorphism assertions use the definition node. The term bound on L and membership of its terms in P put L in R. The text writes the roof cancellation and writes h^j = k^j r^j and the chain-map equation for r, so augmentation compatibility is an actual precomposed homotopy, not an unidentified transport.

Step 4 is elementary substitution of the two naturality equations already assumed in the statement. Q_A(p) and Q_A(q) are maps between the bounded above P-complexes L,E,G; the full subcategory D^-(A) therefore contains all their objects and the given a. Applying the arbitrary functor S is consequently well typed. Invertibility of the localized F(p), F(q) follows from precisely the preservation hypothesis. The displayed calculation proves Theta P = R for the supplied S and rho, without replacing them by a specially constructed derived functor.

Step 5 writes every component of the mapped homotopy using F's additivity, including the difference and the sum. This is a direct two-line identity from the homotopy in step 3, so elementary is justified. The cited derived-category definition explicitly allows localization through the homotopy category; homotopic maps have equal images. Cancelling only P yields the ambient target identity. F is never applied to an equality in D(A), never assumed exact, and F(u), F(r) are never inverted.

For B--E I checked that no new-node statement or hidden clause is being substituted for the argument; all uses are existing statements, their exact phrases are copied into citations.json, and proof_deps is precisely their union. None of the five steps exceeds 2000 characters or hides a separate comparison theorem. All TeX is encoded once. The only non-elementary inputs are the fraction representation/refinement and bounded-cohomology resolution, each cited. No unrecorded tag supplies a theorem.

I tested the boundaries of the reasoning: E or G zero (the other is then acyclic if a is invertible); Y = 0; Y with nonzero cohomology in arbitrarily large degrees; negative upper bounds N; P equal to all objects, or a quotient-generating nonprojective class; and an additive F with no exactness away from R. The bound is always on the refinement source because it is quasi-isomorphic to E, never on Y. The zero functor and any given natural comparison satisfying the hypothesis also cause no exception: only the explicit naturality equations are used. These checks found no missing hypothesis. The sole correction made during this review was eliminating the bound/augmentation name collision.
