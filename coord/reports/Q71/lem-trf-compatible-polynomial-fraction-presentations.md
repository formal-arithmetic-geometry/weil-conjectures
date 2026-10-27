# Q71 stage-1 delivery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-compatible-polynomial-fraction-presentations.json`: item, statement, split; no exact Mathlib match. Four elementary steps, 2325 proof-text characters in total.
- `citations.json`: seven statement quotations, one for every step/node citation.
- `report.md`: this report.
- `searches.jsonl`: actual msearch output records; retained as search evidence.

New nodes: 0. New Mathlib leaves: 0. No Lean or repository files were written, and no compiler was invoked.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id, compatible polynomial/fraction terminology, and essential-finite-type constructions. The id has no declaration there. The compatible maps in `RingTheory/PopescuLiftMaps.lean` concern a specific prepared quotient modulo powers of an element and do not state this item.

## WANTED

None. The needed sources are present in `literature/stacks-project/algebra.tex`.

## Findings and changes

The statement is unchanged. The previous item was statement-only, so there was no previous argument or report to overwrite. I retained its provenance, blueprint ancestry and earlier Mathlib search records. Its existing source calls this an agent refinement of Tag 00SF, correctly: the simultaneous generator-lifting argument is not printed verbatim in that lemma. The new proof_origin explicitly records that distinction.

I read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`. The inherited long ancestry places this algebra fact under the affine-local complete-intersection input to the nodal chart. The split supplies that existing input and changes neither the unit nor the chapter route. The item is not the key node of its unit, so no unit realization record is edited.

I searched the imported blueprint with `tools/blueprint_refs.py search` for `polynomial`, `essentially of finite type`, `unit-denominator`, and `finite type algebra`, and the DAG for 00SF, localization/finite-type/fraction terminology and the item terminology. The broad polynomial search returned 79 blueprint nodes; none states the simultaneous two-surjection construction. The narrower searches returned none. Existing definition nodes give the exact three interfaces used here: localization models and their fractions, finite-type polynomial surjections, and the polynomial universal property. Therefore creating either a one-algebra fraction lemma or a lifting lemma would merely package a few elementary lines as a new node. I created none.

The item searches were run through msearch in all four modes, including two different LeanFinder phrasings, and are recorded literally. The services were available. The relevant Mathlib hits were individual finite-type polynomial presentations (`Algebra.FiniteType.iff_quotient_mvPolynomial''`, `FiniteType.lean:174`) and the single-algebra criterion (`Algebra.essFiniteType_iff`, `EssentialFiniteness.lean:88`), whose source I read. The second search returned localization-away generator constructions and `Algebra.Generators.ofSurjective`; these concern one algebra presentation/localization, not compatible maps to both sources of the two given surjections. The item is not a one-line specialization of any returned declaration.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish.

## Review by Q71

I read all of delivery-errors B through E, including the merged copy, against the written split. For the item I read Stacks Tag 00SF (`lemma-lci-local`) and its proof in algebra.tex, then the actual elementary inputs: Tag 00QM (`definition-essentially-finite-p-t`), Tag 00F3 (`definition-finite-type`), and the explicit multiplication and equivalence relation of fractions immediately before Tag 00CO (`definition-localization`). I verified these tags against `tags/tags`. There are no new nodes requiring separate sources.

Step 1 cites `def-weil-pbc-essentially-finite-type-algebra`, whose statement actually supplies a finite-type algebra B, a multiplicative set W and an algebra isomorphism with W^{-1}B; it also explicitly describes the fractions. It cites `def-weil-pbc-finite-type-algebra`, whose statement supplies a finite-variable polynomial surjection, including zero variables. Applying those definitions separately to P and Q yields exactly the data named in the step, without assuming the localization map is injective.

Step 2 cites `def-weil-pbc-mv-polynomial-ring`. Its statement includes existence of evaluation for any variable family and uniqueness for homomorphisms agreeing on variables. I checked both requirements: the chosen values lie in P and Q, the lifts exist by the stated surjectivity of u and v, and the two composite values agree separately for every x_i and y_j. Both composites are k-algebra homomorphisms because all given and constructed maps are. The embeddings of the two variable blocks are justified directly by their distinct monomials; no theorem on polynomial decomposition or tensor products is being used.

Step 3 cites the essential-finite-type definition for the fraction representation and the polynomial node for equality of the restricted evaluations. It uses the surjection e selected in step 1 to lift both b and w to polynomials a,t in the x-block. I checked the denominator has an actual inverse theta(1/w), and computed p f(t) = theta(b/1); this does not assume b or w has a unique representative and does not cancel a potentially zero-divisor in B. The identities hold by the explicit fraction relation, with cross-product difference zero. The same check in step 4 uses d, eta and the y-block and gives the separately required Q-clause. Its cited nodes have exactly the same applicable statements; no property of the opposite-block lifts is needed for either fraction calculation.

The only choices are finite generators, localization models, and finitely many set-theoretic lifts. They require no new structural lemma. Each step is 471 to 666 characters and is an elementary unpacking of definitions, variable evaluation, or a fraction identity, so no step exceeds 2000 characters or hides a separate comparison theorem. Although the full Stacks 00SF proof uses complete-intersection results, none is used to establish this auxiliary polynomial construction, and importing such results would add unjustified dependencies.

I tested r=s=0 with P=Q=k, taking constant polynomials and denominator 1. For a non-finite-type example P=Q=k(t), use the one generator t; all denominators are nonzero polynomials and the identity maps are compatible. For distinct sources P=k[t], Q=k with both surjecting onto A=k by evaluation at zero and the identity, the opposite lift of t is zero and the Q-block may be empty. For A=0 the lifts still exist and composite equality is automatic. If P or Q is the zero algebra, a localization model may invert 0; the fraction computations still hold and 0=1 is a unit in that algebra. Finally, arbitrary zero divisors in the finite-type models cause no cancellation problem because all displayed identities are identities of fraction equivalence classes. No locality, regularity, nonzero-ring, or finite-generation assumption on A was added.

Every node used in every proof step was opened and read. citations.json quotes their statements verbatim. All three are existing Mathlib definition leaves, so there is no off-unit proof-theorem tool use or dependency cycle. The proof_deps list is exactly the union of the seven step citations. Statement dependencies and every inherited blueprint field were retained; blueprint.same_as is the confirmed empty list. I found no statement dispute or source error requiring correction.

## Unfinished work

None in the requested stage-1 split. Maintainer independent review remains part of the normal delivery process.
