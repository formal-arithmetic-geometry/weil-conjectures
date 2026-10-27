# Q67 stage-1 delivery

## Files written
- `dag/nodes/sec-six-functors-basics/lem-sfb-dvr-normal-generic-reduced-special.json`: item, split; Mathlib searches found no full match.
- `citations.json`: one verbatim statement quote per cited node per step.
- `report.md`: this report. The search command maintains `searches.jsonl`.

There are 0 new nodes and 0 new Mathlib leaves. The elementary denominator argument belongs in the item, not a new clause restating it. The normality tools already exist.

## Attachments
None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and for normal generic/reduced special fibre terminology. RelativeComponentGeneralization and SmoothTraitSectionComponents discuss related idempotent/component arguments, not every clause of this item. No finished declaration stating the item was found.

## Wanted literature
WANTED: Prasad--Yu, On quasi-reductive group schemes, Appendix by Brian Conrad, Remark A.3, printed p.27, for lem-sfb-dvr-normal-generic-reduced-special. Its archive path in the item is absent locally. I read https://arxiv.org/pdf/math/0405381 online at Remark A.3: the paragraph beginning with Serre criteria states the finite-type flat normal-generic/reduced-other-fibres normality assertion. No download or repository write was made.

## Issues found
The item had no proof and no Lean attachment. Its statement is correct; no statement change or dispute is needed. I retained its inherited source, citations, Mathlib searches and ancestry. The blueprint ancestor command returns `None` for this pre-existing long created-node chain; I retain its original null ancestor and precise inherited place rather than inventing an imported ancestor. Searching the whole blueprint for normality, discrete valuation and integral closedness found no duplicate full statement. The latest six-functors unit and its direct-image proof were read; the old inherited det-node citation differs in file naming, but this is only a lower commutative-algebra prerequisite, so no unit route is replaced.

The source gives the normality assertion by Serre criteria. I instead write an agent proof below the unit level, generalizing the explicit least-denominator calculation in Stacks 055J and applying existing normality criteria. This is honestly marked `proof_origin.by = agent`; no missing Serre argument is asserted to be elementary.

## Not duplicates
No new nodes were created. Reused the existing nodes for Stacks 00FN, 00FR, 00HN, 034M and 030C. In particular, neither the monic-equation step nor a specialization of 030C was made a new node.

## Review by Q67
I read delivery-errors B through E in full and checked the actual statements of all cited nodes, not their proofs or titles. The local sources read are algebra.tex at Section 00CM (localization), Definition 00GV and the following reducedness paragraph, Lemma 034M (normal-ring integral closedness), Lemma 030C (reduced finite-minimal-prime normality equivalence), Lemmas 00FN and 00FR (Noetherian finite type and finite minimal primes), and Lemma 00HN (joint injection into prime localizations). I also read more-morphisms.tex Tag 055J and its proof, and more-algebra.tex at the flat torsion-free lemma. For the item's original assertion I read Conrad Remark A.3 online as described above. There are no new-node sources to audit.

Step 1 uses the DVR definition only for the domain and nonzero uniformizer, the flat-map definition precisely for preservation of an injection after tensoring, and the localization definition for its zero criterion. The tensor-unit identification is written explicitly; flatness is not silently assumed faithful. Step 2 uses only the displayed definition of integral element and localization fractions. Multiplication by t^(nd) produces the written formula; all lower-degree terms vanish modulo t. Reducedness then divides the numerator by t and contradicts the minimum n. This is an elementary computation, including a degree-one equation; it is not a new lemma hidden behind a tag.

Step 3 takes exactly joint injectivity/reducedness from the 00HN node. Normality supplies domains at every prime by its definition, and an element nilpotent in a domain is zero. The injection of T into B then detects its nilpotents. Step 4 checks the base-ring hypothesis for 00FN: the DVR definition makes every ideal principal, hence finitely generated under the Noetherian definition. Finite generation of the R-algebra T is in the item's hypotheses. The resulting Noetherian T is exactly the hypothesis of 00FR; no finiteness of normalization is needed.

Step 5 uses 034M only for B, which is normal by hypothesis. The fraction map Q(T) to Q(B) is not assumed without verification: the text checks that every regular denominator of T stays regular in B by clearing a power of t, and checks injectivity by its numerator. All localization maps at regular elements are injective by the recorded zero criterion. The same monic equation makes the image integral over B. Its image therefore belongs to B by the cited statement, and that element remains integral over T because B embeds into Q(B). Step 2 puts it in T. Injectivity identifies the original total fraction with this element. This comparison is a short fraction calculation, not an unproved change-of-total-fractions theorem.

Step 6 uses precisely implication (2) to (1) of 030C, with reducedness from step 3 and finite minimal primes from step 4. The normality conclusion is local normal domains, not merely integral closedness in a chosen larger ring. The extra membership clause was already proved in step 2. Both 034M and 030C are declared off-unit generic tool uses in split_report; they do not replace a step of the unit route.

Small cases checked: T=0 has no primes and all maps and conclusions are compatible with zero rings. For T=R[1/pi], the special quotient is zero and t is a unit; the minimum denominator is automatically zero. Products such as R times R are allowed: the proof never supposes T or B to be a domain. Singular but reduced special fibres are allowed: only the no-nonzero-nilpotents property is used. The nonreduced model R[x]/(x^2-pi^2) explains why that hypothesis cannot be dropped: x/pi is an integral generic element outside the model. R[x]/(pi*x) explains why the injection cannot be inferred without flatness. No excellence, perfectness, geometric normality, special-fibre normality or finite normalization is introduced.

I checked B1--B10: no statement-only new files need review, all existing notions are defined or explained inline, TeX is singly escaped in JSON, all search entries are actual command records, and no incorrect Mathlib leaf is claimed. I checked C1--C8: every non-elementary use is a cited statement; quotes in citations.json are exact; the two off-unit tools are declared; the server checks will detect cycles. I checked D1--D5: the proof performs the denominator reduction rather than moving the item into a new node. I checked E1--E7: each hypothesis is discharged as above, objects and fraction maps are explicit, and no source error was found. All six steps are under 2000 characters.

## Unfinished work
None in the authorized stage-1 split. No Lean was written and no compiler or Lake tool was run. Mechanical dry-run and push results are recorded after they complete.
