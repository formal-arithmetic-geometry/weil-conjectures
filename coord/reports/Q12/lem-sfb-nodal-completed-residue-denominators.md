# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-completed-residue-denominators.json`: statement unchanged; six-step complete proof, existing dependencies only, status split. Mathlib searches find ingredients rather than the whole assertion.
- `citations.json`: verbatim statement quotes for all 14 step/dependency citations.
- `searches.jsonl`: actual search-command log; new queries appended to the item's inherited Q36 search records without replacing them.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves are reused rather than duplicated. No Lean was written or compiled.

## Attachments

None. Searched the current `lean/WeilConjectures/` for the exact blueprint id and for nodal/completed-residue terminology. The related completion declarations do not give every clause of this item; there is no exact attachment.

## WANTED

None. Read the available Stacks source, not an external reconstruction of its omitted proof.

## What was wrong or missing

The imported item had no proof. Its statement is correct as written, including the unit hypothesis. No statement correction or STATEMENT-DISPUTED is required. The source, Stacks 0CBT (remark-quadratic-extension), explicitly omits comparison (2)/(3); this delivery supplies the algebraic subargument rather than citing the omission as a proof. No additional finiteness hypothesis on B and no field/domain hypothesis on L is used. The proof is marked agent-written, since the omitted argument was supplied here.

The current latest blueprint in `sec-six-functors-basics/sk-thm-sf-ctf-stability/` was read, including its unit and direct-images proof (3). The latter now gives proper/open/compactification assembly. This item remains an algebraic ingredient under its already existing alteration branch; this delivery changes no chapter, unit, target, or route. Its inherited nearest blueprint ancestor is null (confirmed with blueprint_refs ancestor); the inherited precise provenance and via chain are retained. Whole-blueprint searches for denominator, constant coefficient and faithfully flat found no second statement of this item; same_as stays empty.

## What could not be finished

Nothing remains in the stage-1 split. The proof uses nine existing nodes and creates none. Formal Lean implementation is outside this task.

## Not duplicates

No new nodes were created. In particular the faithful-flatness, contraction and power-series-unit ingredients already have nodes and were cited directly.

## Review by Q12

I read Stacks `curves.tex`, Remark 0CBT, with its three constructions and explicit sentence omitting comparison with (3). I also read `algebra.tex` at 00MC (lemma-completion-faithfully-flat) and 05CK (lemma-faithfully-flat-universally-injective), including the ideal-contraction sentence and its proof. I checked the recorded Mathlib declarations in FaithfullyFlat/Algebra.lean and AdicCompletion/LocalRing.lean and the series inverse/unit criterion. There are no new-node sources to review.

For step 1 I opened each of local-completion-faithfully-flat, faithfully-flat-base-change and faithfully-flat-ideal-contraction and read its statement. The first assumes exactly Noetherian locality; the second accepts arbitrary base change, so B need not be finite or Noetherian; the third supplies both contraction and injectivity of B into C. The injection of A into B is explicitly a hypothesis of the item.

For step 2 I opened local-completion-local-ring and tensor-over-quotient-ring, as well as the tensor, algebra/quotient and series definitions. They give the same-residue-field assertion, quotient tensor comparison, and the coefficient and tensor relations actually used. I checked the ring structure separately by writing the formula b tensor r maps to bar(b) bar(r); I did not treat a module isomorphism as automatically an algebra isomorphism. The inverse takes bar(b) to b tensor 1, so the comparison really is the canonical map specified in the statement. The second quotient has kernel t exactly by coefficient shifting; constants supply surjectivity, and the assumed residue action verifies F-linearity. No coefficient field in A or R is selected.

For step 3 I opened power-series-unit-constant-coefficient and the series definition. The former explicitly allows arbitrary commutative coefficient rings, so it applies to L without assuming it is a field. The remaining injectivity is literally the shift of coefficients under multiplication by t. Composing with the injections proved in step 1 gives regularity in both rings.

For step 4 I reopened faithfully-flat-ideal-contraction for ideals of B, not just ideals of A. Since tU generates the same ideal as t, the two extended ideals agree in C and contract to the desired equality in B. I read the ideal product/power definition and wrote the common-generator argument proving extension commutes with products; induction includes exponent zero.

Step 5 uses only the ideal/power and series definitions plus earlier proved steps. Existence of d/f^n is actual ideal membership; uniqueness is repeated cancellation of f. Comparing the coefficient of degree n, not an unspecified order function over a possibly non-domain L, gives u^n H(0)=r. This is exactly the residue map proved in step 2. Step 6 uses no further node: substituting g=fb and f=gc gives f(bc-1)=0 and cancellation proves bc=1. This checks the two-denominator compatibility without assuming either ratio in advance.

I checked small cases n=0, d=0, g=f, arbitrary n with vanishing leading coefficient r, split coefficient algebra L=F x F, and L with nilpotents. Unit multiplication and t-shifting still work in all of them. If there is no qualifying f, only the quotient comparison is asserted and remains valid. The warning about nonzero coefficients is justified by the complete split node A=F[[x,y]]/(xy), B=F[[x]] x F[[y]], and L=F x F. Embed A in B by the two branch restrictions and identify B with L[[t]] by sending (x,y) to t. The image of mB is tL[[t]], the diagonal constants give the required residue action, and R=A because A is complete. The element f=x has series t(1,0), with nonzero nonunit leading coefficient (1,0). It is killed by y in A and by (0,1) in B, and fB is strictly smaller than mB. Thus weakening unit to nonzero would fail under all the other hypotheses of the item.

Checked delivery-errors B--E: no new statements or duplicates, no restatement nodes, no hidden non-elementary assertions beyond cited statements, no unproved transport or denominator-clearing step, no added hypotheses, and no dependency on the item through its ingredients (all substantive tools are existing Mathlib leaves). Each step is under 2000 characters. All quotes in citations.json are exact statements from the opened dependency nodes. The initial Loogle query had an unknown identifier and is recorded honestly as an unsuccessful query; its corrected query found the existing contraction lemma. Both semantic searches found Weierstrass-division statements with extra/local hypotheses rather than the combined descent result. LeanSearch's completion/DVR hits likewise do not prove this item. No search was fabricated.
