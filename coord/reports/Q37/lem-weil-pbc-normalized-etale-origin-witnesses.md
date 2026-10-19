# Q37: lem-weil-pbc-normalized-etale-origin-witnesses

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-normalized-etale-origin-witnesses.json: statement, split into six proof steps, no Mathlib match.
- citations.json: verbatim support for each cited node in every proof step; the tensor-pullback and sheaf-unit statements are additionally quoted in full.
- searches.jsonl: actual msearch.py records, including two semantic phrasings and categorical lifting candidates.
- report.md: this report and the author's self-review.

No new nodes, no Mathlib leaves, no unit/chapter modifications. The statement and stmt_deps are unchanged from the repository item. The inherited Q92 source, provenance, blueprint ancestry, and Mathlib search records were retained. The initial sandbox contained only dispatcher .brief files, with no split, report, searches, or interrupted delivery to resume.

## Attachments

None. Searches for the exact blueprint tag and item id in WeilConjectures found no declaration. Searches by etale-origin, normalized towers, and their Lean naming variants found generic site-comparison/etale-origin functors, including SixFunctors/ProEtale/Derived/UpperShriekComposition.lean; none states the normalized coefficient-reduction tower conclusion. In particular those results do not supply boundedness of each derived quotient, its quotient coefficient action, and all normalization equations. No upstream master sorry declaration was treated as a proof.

## WANTED

None. All sources used are archived in literature/.

## Problems and changes

The item was an unsplit statement with a mathematically valid intended proof. A tempting but invalid ordering would invoke D+ full faithfulness on L_m tensor^L P_n before showing this derived tensor belongs to D+. A quotient P_m -> P_n need not have finite Tor dimension. Step 3 instead reflects the lower bound of M_n using exact inverse image and the underived sheaf unit. This does not introduce a finite-Tor, constructibility, Noetherian-scheme, or uniform-bound hypothesis.

The canonical tensor-pullback lemma states bifunctoriality but does not separately state a three-coefficient coherence theorem. I did not assume such an extra clause: Step 2 writes the balancing formula, checks the quotient action, units and associativity, and gives the K-flat scalar-extension calculation needed to compute iterated derived quotients. Step 6 then writes the cocycle calculation itself.

The blueprint source sentence is the compatible-witness sentence in main-20261015 prop-weil-pbc-preservation-constructible.proof.md. Stacks 09B1, proetale.tex lemma-compare-derived, establishes the bounded-below comparison; it does not literally state this tower lemma. Accordingly the proof is marked agent-written, refining that blueprint sentence using the existing Stacks-based tools. No SGA source is used.

## Unfinished work

None in this stage-1 item. This delivery supplies a natural-language split, not Lean code or a compiler check.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. Whole-DAG and blueprint searches by 09B1, normalized, witness, normalization maps, compatible witnesses and origin witnesses were read. The bounded constructible-complete, tower-preservation and witness-compatibility nodes define stronger structured settings or properties of four geometric functors; they do not state this general finite-coefficient tower lifting theorem. The existing site-comparison theorem supplies the needed black box and is cited rather than duplicated. The same_as field remains empty.

## Review by Q37

I read the worker brief, delivery-errors B through E, the stage-1 contract, the three levels in SETUP, GOAL, dag-sync, and the chapter and unit records. The item serves the proper-base-change unit's existing coefficient-comparison route; it is not a unit key node, so the unit realization fields need no change. I read the current blueprint proof of preservation of constructibility and checked the item against its actual compatible-witness use.

For the literature I read Stacks proetale.tex Tag 09B1 (lemma-compare-derived), including both clauses and its proof, and sites-cohomology.tex Tags 0G7E (lemma-pullback-K-flat), 07A4 (lemma-pullback-tensor-product), 06YT (lemma-derived-tor-quasi-isomorphism-other-side), and 06YY (lemma-derived-base-change). These support the cited existing comparison and K-flat tools, rather than a new citation-only proof. The coefficient-tower and cocycle refinement is written out by the author. No new node requires a further literature source.

Step 1 uses the datum for finite P_n, proetale-modules for the exact termwise comparison functor and coefficient conventions, tensor-pullback for the unbounded tensor comparison and preservation of flat-term K-flat models, and derived-change-of-rings for quotient tensors. I opened each statement: the tensor theorem is genuinely unbounded, not just D+, so there is no boundedness circularity. Its ringed-topoi hypotheses hold for the comparison with constant coefficient sheaves, on the fixed small skeletons in the larger universe. The quotient action is checked on the last tensor factor. No completed integral sheaf is identified with a constant A sheaf.

Step 2 uses derived-change-of-rings for its resolution computation and descent to derived categories. The K-flat preservation under scalar extension is proved in the text by testing against an arbitrary acyclic target-ring complex; restriction of scalars changes no underlying differential or sheaf. The two-stage balancing formula, the identity quotient and its naturality are elementary calculations on these models. This is one direct computation, not a new standalone lemma left implicit.

Step 3 uses precisely the exactness and unit assertions of site-comparison-finite-level; the whole statement is copied into citations.json. Exactness identifies kernels, images and their quotient, hence cohomology. The unit for the individual cohomology sheaf reflects its vanishing, so the bound may depend on n and no unbounded derived full faithfulness is asserted. Every P_n is finite, as required by that cited node.

Step 4 uses exactly the fully faithful D+ functor in thm-weil-pbc-site-comparison. Step 3 supplies its source bound and the original witness supplies its target bound. Lifting the isomorphism and its inverse and applying faithfulness to the two composites proves invertibility directly; uniqueness is the same injectivity of the Hom map. The alpha conjugations have the types displayed in the item.

Steps 5 and 6 use the same theorem's faithfulness, together with the explicit comparisons already checked in Step 2 and the assumed rho identities. The triple source is bounded below because its associativity identification is C_{k,n}, not because tensor by P_n is presumed left t-exact. Expanding the two beta equations gives rho_{m,n}(rho_{k,m} tensor P_n)(alpha_k tensor P_n); the assumed cocycle is exactly what turns this into rho_{k,n}(alpha_k tensor P_n). Cancelling alpha_n and applying faithfulness proves the equation. This checks the actual maps, not merely existence of some abstract isomorphisms.

I tested the edge cases: zero objects, an empty scheme, m=n, k=m or m=n, constant quotients (I=0), and the zero quotient ring. They yield the asserted identity/zero witness data. For a nonflat quotient such as Z/ell^2 -> Z/ell, a general bounded-below input can acquire an unbounded-below derived tensor, so one cannot remove the normalized bounded-below M_n hypothesis; the proof uses that hypothesis exactly where needed. The statement has no source discrepancy and needed no STATEMENT-DISPUTED correction.

All cited nodes were opened and their statements checked, proof_deps is the union of uses, and citations.json contains literal substrings. No new statement-only node, duplicate, restated item clause, or Mathlib leaf was manufactured. The off-unit derived-change-of-rings tool is declared in split_report.tool_uses as generic coefficient calculus. All proof steps are shorter than 2000 characters, and I checked each for hidden non-elementary subclaims nevertheless. The only additional calculations are explicitly written balanced-tensor and full-faithfulness arguments. All writes are confined to the assigned sandbox; no Lean, compiler, Lake, live project or live launcher mutation was performed.
