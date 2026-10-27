## Worker report

Files written:

- dag/nodes/sec-poincare-duality/lem-pod-verdier-composition-mate-normalization.json: statement, split into six steps. No exact Mathlib match for the complete rational/common-stage Weil statement. The existing Mathlib leaves def-weil-pbc-composite-adjunction and def-weil-pbc-adjunction-conjugate supply the general categorical construction.
- citations.json: six entries, one for every step/dependency pair, checked verbatim against the live statements.
- report.md: this report and review.

New nodes: none. New Mathlib leaves: none. Attachments: none. WANTED: none. Unfinished work: none within this one-level split.

The interrupted attempt had already written the item, citation file and search log, but no report. I retained its statement, proof route, original searches and metadata; the server review_split check passed before further edits. Compared the sandbox with the current live unsplit item: its statement and statement dependencies agree. No released repair note or open Q12 return names this item. The item is a subsidiary lemma of prop-weil-operations, not the unit's key finiteness statement; no unit realization fields were changed.

Searches: the live item already records a first phrasing. The sandbox searches.jsonl records the second phrasing, including LeanFinder, LeanSearch, Loogle and grep. I read those logged results without repeating the requests, and read Mathlib/CategoryTheory/Adjunction/Mates.lean conjugateEquiv and conjugateIsoEquiv (lines 275 and 425), Basic.lean homEquiv (line 160), comp and comp_counit_app (lines 567 and 580). The general facts are present and already have DAG leaves; the full specified Weil construction is not an exact match or a one-line specialization. No unrun query was added. Searched the project source for the blueprint id, composition-mate normalization, conjugation and Verdier exchange. WeilConjectures/WeilSheaf/VerdierDual.lean has nonempty_verdierDual_derivedLowerShriek_iso, but its proof is sorry and it states existence rather than these component formulas. It is not an attachment. The upstream generic conjugation lemmas do not state the full item.

Searched the DAG for composition mate, transposition normalization and internal adjunction, and ran blueprint_refs.py search Verdier and ancestor for the item. The ancestor is prop-weil-operations. Existing fix-lem-tensor-adjunction and fix-cor-verdier-exchange give the stage isomorphisms, not the entire conditional normalization statement. Reused the existing categorical leaves and the exchange definition; created no duplicate and no node restating a clause. The item's blueprint.from.place already names sentence 4 and the returned Steps 5--7; same_as remains empty.

## Source and corrections

Read the current main-20261015 prop-weil-operations.proof.md sentence 4, fix-cor-verdier-exchange.proof.md Steps 1--3, and fix-lem-tensor-adjunction.proof.md Steps 1--2. Also read the recorded chapter and unit. This follows the specified formal-duality route, with no SGA source. The proof is marked agent-written because the detailed unit calculations expand the blueprint's formal assertion.

No statement correction was required. The source's word canonical is made precise by the normalization already in the item's statement. Crucially the statement of fix-lem-tensor-adjunction supplies the isomorphism only; its proof is not used as an additional unstated normalization theorem. The five Hom bijections are explicitly stipulated in this item. The split computes their composite on s_M. No construction of an ambient exceptional adjoint, integral Weil representative, or new coefficient comparison is asserted.

I clarified the inverse-Weil-arrow calculation with separate source and target subscripts. I added the existing field-stage finite-Tor definition to Step 6 to justify taking B=A in the stipulated normalization, and expanded the corresponding citation of internal adjunction to include its actual displayed isomorphism rather than just its introductory words. All steps are under 2000 characters (longest 958); none hides a new standalone comparison lemma.

## Review by Q12

I checked the sources above against the unchanged statement: f and the structure maps have the stated separated finite-type setting, coefficients are E or the common-stage algebraic closure, and the exceptional adjunctions and their lifts are supplied on their actual domains. Additional admissibility and finite-Tor hypotheses are invoked only for the final internal-adjunction clause. The projection map is assumed invertible where used; this split does not infer its invertibility from a definition.

Step 1 uses the statement of def-weil-pbc-composite-adjunction for exactly the pasted counit epsilon^H composed with H(epsilon^F). Substituting L1=HF, R1=GJ, L2=U, R2=W and tau=alpha inverse in def-weil-pbc-adjunction-conjugate gives precisely the displayed formula for c_Z. That same cited statement, rather than a general assertion about arbitrary square mates, supplies naturality and preservation of isomorphisms. Setting Z to the coefficient unit gives exactly the two dualizing objects by their definitions. Read Stacks categories.tex lemma-compose-counits (0DV0) and the Mathlib implementations for the counit convention.

Step 2 uses the defining arrow equation in def-weil-weil-sheaf-complex. Multiplying that equation by the inverse on each side proves that alpha inverse is Weil. The elementary equation for composition, and the supplied Weil functor/adjunction lifts, then prove c_Z is Weil. No theorem constructing those lifts is smuggled in: their existence and equivariance are hypotheses of this item.

Steps 3 and 4 are elementary expansions of transposition as right-adjoint image followed by its unit. For the supplied tensor adjunction, r=H_M(t) composed with nu_PA, so replacing t by ct gives H_M(c)r. For P adjoint Q, s_M=Q(r) composed with eta_A, so the next transpose is QH_M(c)s_M. The intermediate targets are H_M(G omega_Y) and QH_M(G omega_Y), and the final target is QH_M(omega_X)=QD_XM; both substitutions are type-correct without a finite-Tor inference.

Step 5 uses precisely the arrow-construction sentence of def-sf-verdier-exchange-data, which says projection/evaluation, exceptional transposition, substitution, tensor-Hom transposition and ordinary transposition, in that order. This identifies epsilon_M, rather than an unspecified isomorphism with the same endpoints. Step 2 and the stipulated lifted functors make QH_M(c) a Weil arrow. Functoriality and composition here are elementary.

Step 6 uses the actual isomorphism stated by fix-lem-tensor-adjunction, with M and N=omega_Y in its stipulated additional domain. Its use as an off-unit generic tool is declared in split_report.tool_uses: it is the very internal-adjunction result named by this item and the blueprint's exchange route, not a replacement route. The statement of def-weil-finite-tor-amplitude explicitly identifies the rational/common-stage finite-Tor categories with the bounded constructible categories, so the supplied A is an allowed B. The normalization comes from the item's own hypothesis: inverse ordinary, tensor and exceptional transposition send s_M back to b; precomposing b with pi cancels pi inverse; tensor transposition sends evaluation to 1_A. Thus I s_M=1_A, and I invertible implies s_M=I inverse. This proves the last two identities and invertibility without citing the proof of another node. No separate assertion about shifts or coefficient comparisons is being claimed by this component-normalization lemma.

I checked the B--E return reasons explicitly: no new statement-only files or new leaf metadata require auditing; all notions in the statement retain their existing definition dependencies; every non-elementary proof assertion has a cited statement, not just a source tag; all six citation entries are verbatim. The new proof dependencies are categorical leaves, the exchange definition, field-stage definition and the existing internal-adjunction theorem, with no dependency on this item. No clause is moved into a fresh node. There is no division by a scalar, nonempty-space assumption, or additional ambient-domain assumption. On f=identity with identity compositor the mate is identity, and the transpose chain sends evaluation to identity as required. On zero M or empty X the arrows are arrows between zero objects and the same adjunction cancellations apply. At a point, including shifted complexes, the categorical counit/transpose equations apply without an added sign; the signed conventions are those of the supplied closed structure. At the common-stage coefficients all calculations take place in the stipulated category itself, so they do not require choosing integral models for Frobenius arrows.

## Not duplicates

No new nodes were created, hence no new/existing pairs need distinction.

## Resumption validation

The resumed dry run rejected only the finite-Tor citation as shorter than its 40-character minimum. I replaced that fragment with the complete displayed definition, including both rational and common-stage equalities, copied verbatim from def-weil-finite-tor-amplitude. This directly covers the two coefficient cases used in Step 6. The item statement and proof were retained unchanged.
