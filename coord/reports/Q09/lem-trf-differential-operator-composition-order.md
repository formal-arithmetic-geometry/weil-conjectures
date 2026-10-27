## Files written

- `dag/nodes/sec-trace-formula/lem-trf-differential-operator-composition-order.json`: statement item, now split; no Mathlib match. The statement is unchanged.
- `citations.json`: empty list, because no proof step cites another node.
- No new nodes and no Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for differential-operator terminology, including `DifferentialOperator`, `DiffOp` and the prose notion. No corresponding declaration was found, so there is no completed project proof to attach.

## WANTED

None. The source required for the full proof is present locally.

## Findings and changes

The imported item was statement-only. Read Stacks `algebra.tex`, Tag 09CI (`definition-differential-operators`, lines 34657–34680) and Tag 09CJ (`lemma-composition-differential-operators`, lines 34683–34698). The source's short induction leaves its zero-order boundary and closure under addition implicit. These are now explicit. In particular, no negative order is used when one of k and l is zero, and no assumption that the displayed bounds are minimal orders is made.

Read the chapter record, the unit record `sk-i-curve-zero`, and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` unit and locality lemma/proof. This algebraic item is a supporting lemma on the already recorded historical resolution/localization branch. The latest locality proof uses contracting correspondences and does not itself state a differential-operator lemma. Preserved the existing blueprint ancestry/place/via information; no change to the unit's or chapter's route is proposed. `blueprint_refs.py ancestor` confirms `lem-trf-local-term-locality` as nearest blueprint ancestor. Whole-blueprint search for “differential operator” gives zero matches. Whole-DAG tag and concept searches find this item, its localization parent and more distant applications, but no node stating a different required auxiliary result. No new node is needed.

The item includes the recursive differential-order definition in full, so it needs no new definition node. Its existing statement dependency `def-weil-pbc-algebra-hom-quotient` was read: its opening sentence defines a commutative R-algebra by its structure map, exactly what the statement cites. Its quotient-ideal clauses are not used. The proof uses only the inline differential-order definition and elementary module arithmetic; it does not cite that node as a theorem about operators.

Ran the prescribed Mathlib search command with LeanFinder (two different phrasings), Loogle, LeanSearch, and two grep patterns; read the returned names, types and documentation. The first semantic search returns `LinearMap.compDer` and derivation functoriality, whose inputs are derivations on an algebra composed with an algebra-linear map, not arbitrary finite-order operators between modules. The second returns analytic iterated-derivative operations. LeanSearch returns power-series order/product bounds and an analytic derivative bound. Neither grep pattern finds an operator predicate, and Loogle reports the identifier `DifferentialOperator` unknown. These are recorded verbatim with no-match verdicts; no unavailable response is described as evidence of absence. Retained all earlier item searches and added the logged Q09 searches.

## Not duplicates

No new nodes were created. No duplicate pairs require comparison.

## Review by Q09

I checked the statement clause by clause against Tag 09CJ and the recursive convention in Tag 09CI. The ring map, three modules, R-linearity, nonnegative bounds, direction of composition and sum of bounds agree. “At most” expresses the source's increasing filtration, rather than an assertion of exact minimal order. No hypotheses or conclusions were changed.

For step 1, I checked the elementary identities directly: scalar multiplication by c is R-linear because both actions factor through the commutative ring C; zero and sums preserve C-linearity at bound zero. At each successor bound, the commutator identities reduce closure under zero and addition to the immediately preceding bound. This is the two-line induction implicit in the paragraph immediately after Tag 09CI, rather than an appeal to an uncited module-of-operators theorem.

For step 2, the induction is quantified over every pair of bounds with the given sum (and every triple of modules), so both applications in step 4 are legitimate. The base sum zero forces both bounds zero, and the displayed equality proves C-linearity of the composite from C-linearity of its two factors. For step 3, I expanded both summands pointwise and checked cancellation and additivity of E; the types are L to M to N and both resulting terms land in N. This is precisely the identity printed in the proof of Tag 09CJ.

For step 4, I checked separately k positive, k zero, l positive and l zero. The positive cases lower the total by exactly one, and the zero cases give the zero map instead of a fictitious order minus one. The previously proved additive closure applies to the two maps with the same nonnegative bound s minus one, and the recursive definition then gives the conclusion. These are elementary induction-hypothesis and definition applications with their arguments written out, so no non-elementary black box is hidden by an elementary flag. Each step is under 700 characters; none meets the 2000-character long-step threshold. Every proof-step uses list is empty and `proof_deps` and `citations.json` therefore both correctly remain empty.

As small-case checks, k=l=0 reduces to composition of module homomorphisms; k=0,l=1 and k=1,l=0 each retain exactly one nonzero commutator summand; for k=l=1 the two summands have bound one before the composite is assigned bound two. Zero modules, zero maps, a zero algebra and non-faithful structure maps also satisfy every displayed identity. Nothing assumes a field, finite generation, characteristic zero, injectivity of the structure map, or faithful modules.

Checked delivery-errors B–E: no statement-only child is polluted with proof text because there are no children; all objects and the differential predicate are explicit; the source includes exact Stacks tags and labels; no source tag is used as a substitute for a node citation; no cyclic dependency is added; and the proof carries the induction rather than moving the composition conclusion into a new node. There is no statement dispute. No SGA source is used.

## Unfinished work

None in the mathematical split. Delivery checks and push are performed with the required delivery tool.
