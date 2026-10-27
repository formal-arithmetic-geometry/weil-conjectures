# Stage-1 report: lem-sfb-unit-binomial-derivative-presentation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-unit-binomial-derivative-presentation.json`: statement, split into six explicit elementary steps; no full Mathlib match. Added the existing multivariate-polynomial definition to statement dependencies and to the definition references in the statement.
- `citations.json`: nine verbatim statement excerpts, one for each step/node pair.
- `searches.jsonl`: unmodified output of the prescribed Mathlib search command.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. The mathematical statement is unchanged.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for the inverse derivative/unit-binomial notions. `StandardEtalePair.ofXPowSubC` and `StandardEtalePair.ofXPowSubCRingEquiv` in `WeilConjectures/Mathlib/RingTheory/Etale/StandardEtale.lean:200,219` use the pair with g=1. They do not state this explicit derivative-inverse presentation or all its displayed formulas. The related theorem in `lean/Sheaf/AlgebraicGeometry/UnitBinomialFiniteEtale.lean` has `sorry` and states the parent finite-etale conclusion, not this item. No attachment claimed.

## Wanted literature

None. Both sources needed for this elementary algebra calculation are present locally.

## Corrections and searches

The original source description attributed a derivative-inverse presentation to Tag 00UB. I read `literature/stacks-project/algebra.tex`, definition-standard-etale, Tag 00UB: it defines the localized monic quotient with invertible derivative, rather than explicitly stating the two-variable quotient. I corrected the source description and marked the detailed proof agent-written. I also read `literature/stacks-project/etale-cohomology.tex`, lemma-kummer-sequence, Tag 03PL, especially the affine paragraph stating invertibility of n and T^(n-1). That paragraph motivates the explicit calculations here; it does not supply the map computations by itself.

Existing Mathlib search records were retained as provenance. All six searches actually run for Q79 are additionally recorded from this sandbox's searches.jsonl with their exact tool and query text. Both semantic phrasings were read. The relevant StandardEtalePair localization and inverse-generator declarations were read in Mathlib/RingTheory/Etale/StandardEtale.lean; their hypotheses still require constructing the pair and their conclusions omit the displayed binomial certificate. root_X_pow_sub_C_pow is only the root equation over a field; root_isInv concerns a linear inverse polynomial. The other hits concern power-series quotients, primitive roots, or Kummer field extensions, and do not state this result over an arbitrary commutative ring. No full Mathlib leaf was claimed.

Blueprint searches: `tools/blueprint_refs.py search` for derivative, binomial, inverse derivative, and polynomial quotient; DAG searches for quotient universal properties and polynomial evaluation; Lean searches by exact item tag and by inverse derivative, ofXPowSubC, and unit-binomial concepts. Reused `def-weil-pbc-mv-polynomial-ring` rather than introducing an evaluation lemma. No new node is justified: all identities and well-definedness checks are written out in a few lines each. The inherited blueprint.from.place already identifies det-thm-sf-ctf-stability-direct-images, proof (3), and the algebraic steps 6 and 7 of the unit-binomial input. The ancestor command reports None along the inherited ancestry; the existing null from.node and via chain are retained, not silently redirected. same_as remains [] after the searches. No chapter or unit record changed.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to compare.

## Review by Q79

I checked the split against delivery-errors B through E with the source paragraphs and all three cited definition statements open. The full argument is in the item, rather than moved to new nodes restating its clauses. Each of its six steps is below 500 characters and gives a direct computation or a representative calculation; no long step hides a non-elementary lemma.

Step 1 uses exactly the kernel assertion of def-weil-pbc-algebra-hom-quotient to obtain t^n=u, then writes the inverse of t by commutativity and n>=1. Step 2 uses the finite coefficient description in def-weil-polynomial-ring and explicitly defines the formal differentiation formula, then calculates the inverse derivative using an=1 and (ts)^(n-1)=1. It does not infer derivative identities from a definition that omits them. These are finite coefficient and commutative-ring identities.

Step 3 uses the existence of evaluation stated in def-weil-pbc-mv-polynomial-ring, and the quotient algebra and kernel statement of def-weil-pbc-algebra-hom-quotient. Both defining generators map to zero; a general element Pf+Q(Yf'-1) of the ideal consequently does too. This explicitly proves independence of representatives and preservation of algebra operations, rather than citing a quotient universal property missing from the definition node. Step 4 repeats the single-variable representative calculation for beta. The multivariate definition allows an arbitrary variable set, so its one-variable specialization has all the hypotheses needed.

Step 5 uses the quotient surjectivity and finite polynomial expansions supplied by the same two definitions. I checked the often-missed Y-generator: d beta(h)=1 and yd=1 imply y=y(d beta(h))=(yd)beta(h)=beta(h). It uses neither cancellation nor an unproved inverse-uniqueness lemma. Thus the second composite fixes every monomial as well as constants. Step 6 uses precisely the definition of an R-algebra homomorphism to identify structure maps.

All coefficient rings and targets are commutative R-algebras, as required for evaluation. The image of the integer n and the chosen a commute, and an=1 is preserved by both structure maps. No domain, field, reducedness, or nonzero assumption occurs. For n=1, n-1=0, a=1, h=1 and f'=1, including the zero ring convention z^0=1. For the zero ring, both polynomial quotients are zero and all equations remain valid with 0=1. As a nonreduced check, R=Z/4, n=3, a=3 and u=1 satisfy the same symbolic inverse calculation; there is no illicit cancellation. In positive characteristic dividing n the hypothesis an=1 cannot hold unless R=0, so the proof is not making a false inseparability claim.

The nine citations were generated only after confirming each selected excerpt is literally part of that cited node's statement. The item introduces every object, its mathematical hypotheses and conclusions are retained, and no new statement-only nodes or off-route statement tools were added. The existing definitions and Mathlib leaves are permitted generic notions. The detailed proof is honestly marked agent-written because Stacks compresses these computations into its invertibility assertion.

## Unfinished work

None in the split. Required server dry run and push follow this report.
