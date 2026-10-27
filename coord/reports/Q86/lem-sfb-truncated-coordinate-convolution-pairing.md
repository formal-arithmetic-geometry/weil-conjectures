# Worker report: lem-sfb-truncated-coordinate-convolution-pairing

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-truncated-coordinate-convolution-pairing.json`: statement, split; no exact Mathlib match. The statement is unchanged. Six complete proof steps replace the empty proof, using existing nodes only.
- `citations.json`: every step/node citation, with its verbatim statement as the quote.
- `searches.jsonl`: unedited results logged by the authorized search command; the item retains its inherited searches and records all searches from this session with their actual queries/results.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the exact blueprint id and for truncated polynomial, top-coordinate, and convolution/nondegeneracy notions. The hits concern other truncated-polynomial constructions, not this pairing. No project declaration states all clauses. The Mathlib convolution declarations construct the algebra and give its product formula, but do not prove this nondegeneracy assertion.

## WANTED

No additional source is required for this agent-written algebra proof. The inherited reference to Jantzen I.8–I.9 is background for the parent distribution-socle item; I did not read that book or claim its results as a source here.

## What was wrong and what changed

The imported item is a true, self-contained algebra lemma, but had no proof and only a note referring to a highest-total-degree argument in its creator's report. I wrote that argument into the item itself. The source and proof_origin now explicitly distinguish this agent argument from the convolution convention in Milne; no exact Milne theorem is claimed. I retained the statement, statement dependencies, inherited blueprint ancestry/via list, and all earlier searches. The existing simultaneous-root-algebra-api node already gives the bounded-monomial basis, so I did not create a duplicate polynomial-basis node. The prime-power binomial identity needs just a coefficient recurrence from existing Frobenius and binomial-expansion nodes, so I kept that short calculation as a proof step.

The important direction is *maximal* support degree for a functional. Coproduct corrections have strictly greater combined degree, and are discarded because they would require a larger support degree in the other factor. There is no assumption that the actual coproduct preserves the polynomial grading. Quotient monomials vanish when an exponent reaches q; they never reduce to lower degree. These distinctions are explicit in steps 2, 5 and 6.

## Not duplicates

No new nodes. I read the statements of `lem-sfb-simultaneous-root-algebra-api`, `lem-weil-pbc-monic-quotient-free`, `lem-sfb-hopf-augmentation-monomial-pairing`, `lem-sfb-restricted-pbw-top-pairing`, `lem-sfb-bounded-monomial-straightening`, and `lem-sfb-borel-graded-bialgebra-monomial-basis`. The simultaneous-root node supplies exactly the needed quotient basis. The Hopf augmentation pairing is a low-degree factorial assertion for an arbitrary augmented Hopf algebra, with an antipode and n! nonzero; it does not cover all degrees of the present height-r truncated algebra. The restricted PBW pairing is for a different algebra and root-system hypotheses. The graded bialgebra theorem assumes degree preservation and perfection, neither available here. None is a replacement statement for this item.

Whole-blueprint searches with blueprint_refs for `truncated`, `convolution`, and `monomial basis` found no identical blueprint node. I read the latest blueprint unit and direct-images proof (3); this computation remains a supporting input below its inherited distribution-socle route. The ancestry command reports None, as already recorded in the live item; I retained that value and the detailed inherited place/via chain.

## Review by Q86

I read Milne, Algebraic Groups (2017), §9(d), printed pp.174–175, for the dual convolution product, and Proposition 10.38's proof, printed p.205, for its binomial coefficient calculation. Neither states this item; the new proof is explicitly agent-written. I also read Stacks varieties.tex, section-frobenius (0CC6), definition-absolute-frobenius (03SM) and the following paragraph, which explicitly asserts that the power map is a ring homomorphism; algebra.tex, lemma-tensor-product (00CX); and the monic-quotient passage in lemma-characterize-henselian (04GG), proof of (10) implies (1). All five cited node statements were opened and read. There are no new nodes needing separate source checks.

Step 1 uses the actual statement of `lem-sfb-simultaneous-root-algebra-api`: quotient by X_i^q minus a prescribed tuple and its bounded-monomial basis, including an empty tuple. I specialized the tuple to zero, the variable count to n and exponent to q. F is a commutative ring and q=p^r is positive. The coefficient functionals then come directly from uniqueness of basis coordinates. I also inspected the recorded ParameterRootAlgebra Lean source as reference material; it is not used as evidence that the present item is finished.

Step 2 cites `def-weil-pbc-module-tensor-product`, whose statement gives both generation by pure tensors and the universal property for bilinear coefficient maps. Spanning follows by expansion and independence by applying each coordinate map. I wrote both arguments instead of citing an unnamed tensor-basis comparison. The multiplication rule is a hypothesis of the item, and the zero-power relations show exactly why degrees cannot decrease. This is an elementary step, not an additional lemma.

Step 3 needs only the hypotheses and the coordinates already established: evaluation of the counit kills all nonconstant basis monomials, and its two identities determine both boundary rows of Delta(t_i). The remainder has positive exponent in each tensor factor. This is a coefficient comparison; it does not assume cocommutativity or invoke an antipode.

Step 4 cites `def-weil-ring-frobenius` for its explicitly stated *ring homomorphism* and iterated-power assertions, not merely a name for a power map. F[Z] satisfies p·1=0. It cites `lem-sfb-commuting-binomial-expansion` for the full expansion with commuting inputs; 1 and Z commute. The recurrence c_0=1 and c_j=-c_(j-1) is written out from multiplication by 1+Z, so the prime-power extension of Milne's p-case is proved here. This avoids division by factorials and works for p=2 and r>1.

Step 5 cites that same binomial-expansion statement in the commutative tensor algebra. Multiplicativity of Delta is a hypothesis. Choosing N linear factors gives degree N, while any remainder choice has degree at least N+1. Step 2 guarantees the quotient cannot lower it. I checked the zero coefficients below N and the precise complement condition at N independently; there is no claim about higher coefficients. The product of c_alpha_i is nonzero by step 4. The step contains its entire distributive argument and is under 1000 characters, not a hidden filtered-algebra lemma.

Step 6 cites `lem-sfb-convolution-linear-map-algebra` for the stated formula f*g=mu(f tensor g)Delta, specialized to B=F. C has both coalgebra identities by hypothesis. For a nonzero functional a highest support degree exists because the bounded index set is finite. I checked each of the three degree cases in the sum and wrote the witness separately in both tensor factors. No symmetry of D is used. Thus both implications, including n=0, follow. Bilinearity is also immediate from the cited convolution formula and linearity of evaluation.

For small cases I checked n=0, characteristic two with q=2, and r=2 with q=4. I additionally computed the coefficient matrix of Delta(omega) and its rank using finite polynomial arithmetic over F_p for n=0, the multiplicative one-variable coproduct x+y+xy at (p,q)=(2,2),(3,3),(2,4), and the noncocommutative three-variable Heisenberg coproduct with Delta(z)=z+z'+xy' at p=q=2. The ranks were respectively 1/1, 2/2, 3/3, 4/4, and 8/8. The Heisenberg test checks a genuine mixed correction without cocommutativity. The proof only uses coefficient arithmetic in F and therefore also works over nonperfect fields such as F_p(s). All these tests concern the unchanged hypotheses.

Against delivery-errors B–E: there are no new statement-only objects, no moved clauses, no new duplicate and no omitted definition node; every cited fact is present verbatim in citations.json and its hypotheses were checked above. Every nontrivial argument is carried by the item's steps. I checked all step lengths (574, 705, 559, 481, 844, 973 characters), so there is no step above the 2000-character threshold. No target statement changes, SGA route, new unit route, compiler invocation or repository writes occur. No mathematical correction was necessary.

## Unfinished work

None in this stage-1 split. Dry run and push are performed with the authorized delivery tool after this report is written.
