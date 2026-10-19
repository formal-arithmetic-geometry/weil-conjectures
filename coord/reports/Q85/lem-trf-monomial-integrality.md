# lem-trf-monomial-integrality — Q85

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-monomial-integrality.json`: statement, split into three complete proof steps; no Mathlib match for the whole criterion. No new nodes, no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the three step citations.
- `report.md`: this report. Search provenance is in the automatically maintained `searches.jsonl`; `prepare.py` is sandbox preparation only.

## Attachments

None. I searched the slopmaster2 project under WeilConjectures and Comparator by the exact item id, blueprint tag, monomial/integrality keywords and monoid-algebra terminology. No declaration states the criterion, and no exact project attachment was found. The upstream master is not treated as evidence of a finished proof. No Lean was written or compiled.

## WANTED

None. The needed ILO PDF and Stacks source are present and were read.

## Corrections and scope

The mathematical assertion is true as imported. I retained all hypotheses and both conclusions. I made its objects explicit: k[Q] is the finite-support monomial algebra, P^sat is the root saturation in the specified ambient G, and the integral extension means elementwise integrality. When G=P^gp this is the usual saturation of the referenced monoid convention. No finite-generation, torsion-freeness, or domain assumption on k[G] was added. For example P=N in G=Q has 1/2 in its ambient saturation, even though 1/2 is outside P^gp=Z; the ambient formula now removes any ambiguity.

I added the existing `def-weil-pbc-integral-closure` to statement dependencies and as the sole proof dependency. Its statement explicitly includes the integral-elements subring theorem, not merely a name for integral closure. Its Mathlib match is a leaf, so no additional node for closure under addition or scalar multiplication is appropriate.

The imported source phrase “monomial-basis normalization argument, printed p.104” was inaccurate: I read ILO VIII 3.1.17 (printed p.101; PDF p.107) and 3.2.9 (printed p.104; PDF p.110). The former defines saturation; the latter proves the scheme normalization comparison using normal fibres and a finite birational morphism. Neither states this general monomial criterion or the coefficient argument. I now identify the criterion honestly as an agent-proved algebraic supporting lemma for that comparison, and use Stacks 00GI/00GO/00GP for integrality and its closure operations. This is an attribution correction, not a disputed mathematical statement and not a replacement of a unit-level step.

The fixed chapter and assigned `sk-i-curve-zero` unit remain as inherited. I read their records and the ancestor `lem-trf-local-term-locality` in the current and historical blueprint context. This supporting monoid-algebra item lies on the recorded historical alteration/toric branch; I have not altered the chapter route or tried to replace the contracting-correspondence theorem.

## Mathlib and duplicate searches

I read the existing DAG nodes for affine monoid-algebra normalization, monomial integrality, integral support saturation, saturated monoid-algebra normality, fine-monoid finite saturation, and the integral-closure definition leaf. The support theorem has extra finite-generation and torsion-free hypotheses and treats arbitrary finite-support elements; it cannot establish this criterion for arbitrary G. The normalization parent uses this item, so it cannot be used to prove the item. No sibling was cited in a circular way.

Whole-blueprint searches used `tools/blueprint_refs.py search` for “monomial integrality”, “monomial”, “monoid”, and “integral closure”, alongside DAG/blueprint keyword searches. No blueprint node states this exact criterion. The existing ancestry and `same_as: []` are retained. No new node is needed, so there is no duplicate pair to justify.

The logged leanfinder searches used both monomial/exponent language and basis-element/group-ring language. LeanSearch returned subalgebra saturation (localization-type, not root saturation), multivariate polynomial coefficient integrality, and general integrality criteria. The valid quoted-name Loogle query returned `instIsIntegralAddMonoidAlgebraOfIsPushout`; I queried its own type and checked that it changes coefficients from integral R to S while retaining the exponent monoid. It gives no criterion for a submonoid P of G. `IsIntegral.of_pow` is only the easy implication here; its type and grep line (IsIntegral/Basic.lean:127) were read. Neither is a match for the equivalence. Two logged regex searches for monoid-algebra integrality returned no matching lines. The initial malformed Loogle pattern is recorded as unavailable because it produced an application-type error, then replaced by a valid query. All newly recorded queries are verbatim copies of the command log, with the actual returned names and notes. The inherited searches were preserved as inherited records.

## Review by Q85

I read the full statement of the item, the unit/chapter records, its blueprint ancestry, ILO VIII 3.1.17 and 3.2.9, and Stacks algebra.tex Tag 00GO (`lemma-integral-closure-is-ring`) with the tag mappings for 00GI (`definition-integral-ring-map`) and 00GP (`definition-integral-closure`). For the one node actually cited, I read `def-weil-pbc-integral-closure` in full. Its exact statement gives both a positive-degree monic relation and that the integral elements form a subring containing the coefficient ring. I also read the Mathlib source at IsIntegral/Defs.lean:53 and IntegralClosure/Algebra/Basic.lean:216: integralClosure is a Subalgebra with carrier IsIntegral, addition/multiplication closure, and algebraMap membership. Thus the subring claim is present in the cited leaf's statement and match, rather than borrowed from an uncited theorem hidden in its proof.

Step 1 uses the cited definition to choose a degree d>=1 monic relation. I checked the coefficient formula explicitly: translating a monomial of a_i by ig contributes to degree dg exactly when its exponent is (d-i)g. If every such exponent is outside P, the coefficient of e^(dg) is 1, contradicting the zero relation and the field's 1!=0. Choosing i<d gives the positive witness d-i. This uses only the basis definition and group cancellation, including in torsion groups; it neither assumes a domain nor assumes distinct powers of e^g. The calculation is elementary and remains in the proof step instead of becoming a restatement node.

Step 2 again uses the integrality sentence of the same node: T^n-e^(ng) is a monic polynomial over k[P] with positive degree and its evaluation at e^g is exactly zero. I verified that e^(ng) is a coefficient in k[P] by the supplied witness ng in P, and that n=1 is allowed. There is no invocation of a minpoly, fraction field, normalization, or grading theorem.

Step 3 first writes out that ambient root saturation is a submonoid: common multiple ab works for witnesses a,b. It then uses Step 2 for the monomials. Its non-elementary input is exactly the cited node's sentence that the integral elements form a subring containing the base ring. Scalars c e^0 belong to k[P]; products with the integral monomials and finite repeated sums therefore belong to that subring. This proves integrality of every element, rather than merely integrality of the generators. I marked this step non-elementary because the subring theorem is a substantive theorem, even though it is already included in a Mathlib definition leaf. No source tag stands in place of a DAG citation. `citations.json` contains a verbatim substring of that statement for each step and I checked each quote against the current file.

For the small cases I checked g=0 (witness n=1), P={0} in G=Z (only g=0 qualifies), P=2N in G=Z with g=1 (T^2-e^2) and g=-1 (no positive multiple in P), P=N in G=Q with g=1/2, P=G (every monomial is already in the base), and an arbitrary infinitely generated submonoid (only the finite supports of the relation occur). For G=Z/2 and P={0}, both monomials satisfy a positive-power relation; in characteristic 2 the group algebra has nilpotents, yet the coefficient calculation still holds because its group-indexed basis is unchanged. Units in P likewise cause no problem. These cases specifically check all hypotheses that the nearby normalization lemmas would have imposed but this item does not have.

I audited delivery-errors B through E against the files: the statement introduces its objects; TeX has ordinary JSON escaping; the source labels are exact; all three citations are to the full node statement; every other inference is a written basis or monic-polynomial calculation; there are no missing non-elementary inputs, new nodes, duplicate clause nodes, relabelled conclusions, or hidden comparison lemmas. The only dependency is a pre-existing Mathlib leaf, so there is no off-unit theorem replacing a unit step. Proof dependencies equal the union of uses. Step lengths are 684, 282 and 734 characters, below the 2000-character threshold; none hides a general lemma. I did not weaken the item to obtain a proof, cite SGA, or use any compiler/build tool.

## Not duplicates

No new nodes. The existing integral-closure subring leaf is reused; neither the monomial coefficient calculation nor the closure-of-finite-sums application was made into a node.

## Unfinished work

None in the split. Server dry run and direct delivery are the final required checks/actions.
