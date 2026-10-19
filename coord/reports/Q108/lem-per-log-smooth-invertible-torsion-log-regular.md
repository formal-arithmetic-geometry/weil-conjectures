# Q108: lem-per-log-smooth-invertible-torsion-log-regular

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-log-smooth-invertible-torsion-log-regular.json: item, statement unchanged, split into four steps.
- dag/nodes/sec-deligne-laumon-a1/lem-per-fs-chart-torsion-factorization.json: new statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, Loogle, grep and LeanSearch.
- citations.json: verbatim statement quotations for every node cited in every step.
- report.md and searches.jsonl: report and actual Mathlib search log.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 tree by the exact blueprint id and logSmooth/LogSmooth/log-smooth/log-regular notions, then Kummer and saturated-monoid terminology. No project declaration states this item or the new monoid factorization. The Kummer declarations found concern ordinary etale unit-root covers and sheaf sequences, not fs log schemes or the factorization.

## WANTED

WANTED: Kato, Toric singularities (1994), Theorem 8.2, for the proof cited by ILO VI 1.8. It is not in the local literature list; no download was made. The delivered proof is marked agent-origin and reduces to existing independently stated preservation lemmas, rather than claiming to have read Kato's argument.

## Corrections and scope

The imported item has a correct statement and no proof. No STATEMENT-DISPUTED or statement change is needed. Its distinction from lem-trf-log-smooth-log-regular is essential: that theorem requires torsion-free group cokernel. Applying it directly here would omit the finite invertible torsion case. Conversely the existing Kummer theorem requires every target monoid element to have a positive multiple in the image, which is not assumed for the whole original chart map. The factorization separates exactly these two conditions; neither existing theorem alone proves the item.

The source VI 1.8 states the general theorem but only refers to Kato for its proof. I read ILO VI 1.1--1.8, VI 2.1--2.3, VIII 3.1.1--3.1.17 and XVI 3.6.1--3.6.5. The chart interpretation follows the item's source and agrees with XVI 3.6.3. The new algebraic lemma is an agent-supplied refinement of root saturation (VIII 3.1.17) and the Kummer condition (VI 2.1); no Stacks tag is invented for a logarithmic result not stated there. The one commutative-algebra source used in the item is Stacks 00FN, lemma-Noetherian-permanence, carried by lem-weil-pbc-finite-type-algebra-noetherian.

The chapter and unit records were read. This item is not their key statement, so no unit record was changed. The recorded historical regular finite-torsion local-model ancestry is retained. Using the generic torsion-free chart theorem and affine fibre-product formula from other units is declared in split_report.tool_uses; these are inputs to this branch, not replacements for the Fourier unit's steps.

## Not duplicates

lem-per-fs-chart-torsion-factorization vs lem-trf-fs-chart-free-factorization: the existing node assumes the cokernel is already torsion free and chooses free generators; the new lemma permits torsion and constructs an intermediate Kummer monoid that removes it. Neither statement contains the other.

lem-per-fs-chart-torsion-factorization vs lem-trf-fine-monoid-finite-saturation: the existing saturation node saturates a fine monoid in its own group completion. The new node saturates the image of P in the larger group Q^gp and identifies the two group cokernels; its group completion can strictly exceed P^gp. The existing saturation theorem is an input to the intended future proof below, not a direct specialization of the new statement.

lem-per-fs-chart-torsion-factorization vs lem-per-invertible-kummer-chart-log-regular: the existing node is a geometric preservation theorem for Kummer charts; the new lemma is purely a monoid construction with no schemes and no log-regularity conclusion.

The whole DAG was searched by logarithmic regularity, log smoothness, Kummer, cokernel and saturation, and candidate statements were opened. Whole-blueprint searches for log regular, Kummer factorization, saturation and torsion-free cokernel found no duplicate; saturation returned only an unrelated scheme-image saturation lemma. The new id and its concept were also searched in the whole blueprint and project Lean tree.

## Intended independent proof of the new algebraic input

Identify P^gp with its image in Q^gp. Let H be its group saturation. Then H/P^gp is precisely the torsion subgroup of C=Q^gp/P^gp, and Q^gp/H is torsion free: if ng lies in H, some mng lies in P^gp, so g lies in H. Define R by the displayed positive-multiple condition in Q. It is a submonoid. If g lies in H, write ng=p_1-p_2 with p_i in P. Then n(g+p_2)=p_1+(n-1)p_2 lies in P and hence in Q. Saturation of Q gives g+p_2 in Q, so g+p_2 lies in R. It follows that R^gp=H. This also works when these groups have torsion and when P has units.

For finite generation, choose one representative of each of the finitely many classes of H/P^gp, adjusting each by a P element as above to get representatives r_i in R. Let S be the submonoid generated by h(P) and the finitely many r_i. It is fine, has group completion H, and lies in R. Its saturation in H is R: every r in R already has a positive multiple in h(P), while if ng lies in S then a further positive multiple lies in h(P), and saturation of Q gives g in Q. Now lem-trf-fine-monoid-finite-saturation, whose full statement I read, makes R fine saturated. Both inclusions and the group quotient identifications then give every assertion of the new node. This proof is recorded here only: the new node remains statement-only as required for a one-level split. It is a genuine algebraic sublemma, not a restatement of the item's geometric conclusion.

## Review by Q108

I checked the mathematical source and each cited statement against the four actual proof steps, rather than treating imported dependencies as accepted proofs.

Step 1 uses the fs log and log-regularity definition. I read its geometric-stalk formulation: the quotient by the ideal of nonunits must be regular, with the stated dimension-rank equality. This makes the pointwise etale reduction legitimate. The elementary invertibility argument uses the residue-field map at the chosen point, so source invertibility of the positive torsion order implies invertibility in a neighbourhood of its image. It does not assume invertibility on all of the original target. This resolves the discrepancy between the item's source-invertibility hypothesis and the Kummer lemma's target-invertibility hypothesis.

Step 2 uses the new factorization's statement exactly as written: R is fs, the first group cokernel is the original finite torsion subgroup, its order annihilates it, and the second group cokernel is torsion free. I checked those claims by the independent argument above. No claim of sharpness, free Q^gp, or injectivity on characteristic monoids is used.

Step 3 uses def-trf-fs-log-blowup for the associated R-log structure, lem-weil-pbc-fibre-product-affine-spectra for the exact tensor-product coordinate ring, and lem-weil-pbc-finite-type-algebra-noetherian for local Noetherianity. I opened all three statements. The monomial-generator argument proves finite type in two lines and is not made a new node. The last citation is lem-per-invertible-kummer-chart-log-regular: I checked each of its assumptions explicitly, including compatible fs charts, injectivity, the positive-multiple condition, finite group cokernel annihilated by an integer invertible on the target, and an etale comparison. The comparison is the identity on the defined chart fibre product. The item does not assume that Y_R's ordinary scheme is regular, and that lemma does not require it.

Step 4 uses the associated-chart definition to produce the log morphism to Y_R and the torsion-free preservation theorem lem-trf-log-smooth-log-regular. I read that theorem's entire statement: it applies to locally Noetherian fs log schemes, requires log regularity of the base, an injective torsion-free group chart cokernel and a smooth or etale comparison, and concludes log regularity. The step checks all those conditions after the factorization, and explicitly identifies the two comparison targets by their universal properties. Thus no smoothness under an unproved map identification is hidden. Only the theorem's log-regularity conclusion is used, not its additional divisorial conclusions. citations.json contains verbatim statements supporting these uses.

I tested the new monoid statement on h:N->N, 1 maps to n: R=Q, the first quotient is Z/nZ and the second is zero. For the inclusion N->N^2 into the first factor, R=N in that factor, the first quotient is zero and the second is Z. For 1 maps to (n,0) these combine into finite torsion followed by a free quotient. For a pure finite group Q and P={0}, R=Q, so group torsion is retained rather than incorrectly excluded. Identity maps give R=P; groups and unit faces satisfy the same positive-multiple definition. These cases explain why no sharpness hypothesis can be silently added. The item also permits empty source and n=1; step 4 is vacuous in the former case and the Kummer factor is the identity in the latter.

For B1--B10, the new node is self-contained, has no proof or proof dependencies, defines H,R,C and the Kummer condition explicitly, cites the existing fs-monoid definition, has actual recorded searches and filled blueprint ancestry, and claims neither an attachment nor a Mathlib leaf. Loogle's saturation hits were inspected: divisor-closed saturation is a different meaning; NSMulSaturated is the relevant closure condition but provides neither this finite generation nor factorization. For C1--C8 and D1--D5, every non-elementary input is a cited node, the elementary tensor-generation and universal-property arguments stay in the steps, and the one new node contains no log-regularity clause of the item. I checked that the reused preservation lemmas do not depend on this item. For E1--E7, the proof verifies every invertibility, fs and Noetherian hypothesis at its point of application, keeps the original comparison map, and assumes neither excellence nor ordinary regularity of intermediate schemes. No non-elementary proof step exceeds 2000 characters, and none hides a separate comparison lemma beyond the displayed two-line universal-property calculation.

## Unfinished work

No unfinished work in this one-level split. The new monoid input remains unsplit for a future worker by design. Dry-run and delivery outcomes are reported by the delivery command.
