# Worker report: cor-mg-det-weight-exterior

## Files written

- dag/nodes/sec-purity-real-sheaves/cor-mg-det-weight-exterior.json: existing statement, now split into four proof steps. No Mathlib match.
- citations.json: verbatim statement quotes for every dependency of every proof step.
- searches.jsonl: actual searches retained, including both semantic phrasings and both Loogle patterns.

New nodes: 0. Mathlib leaves: 0. No unit record changed. Statement unchanged.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 checkout for the exact blueprint id, determinant weights, and exterior-power weights. The closest declaration is Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower in WeilConjectures/AlgebraicGeometry/LinearAlgebraicGroup/Weights.lean:740. Its source explicitly restricts it to a semisimple Weil representation and supplies only the forward direction (see the module documentation at lines 107–110). Geometric semisimplicity in this item's hypothesis is not Weil semisimplicity, and the converse is required. AlgebraicGeometry.WeilGroup.detWeight_weightCharacter at Operations.lean:118 is only the numerical comparison formula. Neither is a complete attachment. The exact item id has no declaration hit. The current DAG's conditional proposition is reused by its full natural-language statement, including the converse; its existing audit fields are not edited.

## WANTED

None. The current blueprint statement and separate proof, comparison lemma, conditional proposition, and all cited node statements are available locally. No SGA source was used.

## Findings and changes

The original one-paragraph reduction is mathematically sound; it left the lisse-factor justification and the identification of weights, capacities and the converse implicit. The split spells them out using existing statements. The geometric-semisimplicity hypothesis is retained although the argument does not use it. Its definition and the determinantal-weight definition are now explicit statement dependencies rather than proof-only mentions.

The main-20261015 statement agrees with the imported statement. I read the current unit definition and chapter route, and the imported unit record: this corollary is not the key definition and does not require editing realized fields. The proof follows the unit's rank-one comparison route. The conditional exterior proposition and the exact tensor equivalence are generic tools, recorded in split_report.tool_uses for review. Blueprint searches for exterior and determinant weight found the conditional proposition, tensor analogue and related definitions; none is a second unconditional iota-weight exterior corollary. No node was created to repeat a clause of this item.

The Mathlib search command ran LeanSearch, LeanFinder twice, Loogle twice, and three grep patterns. All services returned responses. Loogle specifically reported unknown identifiers for the representation exterior-power pattern and for exteriorPower; these are recorded as such, not as a statement match. Semantic hits concern exterior pairings/constructions, finite-group character theory, and Lie-algebra trace forms. I read the finite-group simplicity criterion in Mathlib/RepresentationTheory/FinGroupCharZero.lean:121 and LieModule.traceForm_eq_sum_finrank_nsmul in Mathlib/Algebra/Lie/TraceForm.lean:452: they do not give this theorem or a one-line specialization. Grep found no determinant-weight/Weil-sheaf theorem. The log contains exactly the queries recorded on the item.

## Unfinished work

None for the stage-1 split. Existing dependencies remain responsible for their own proofs. No Lean file was written and no compiler, Lake command, or local DAG/preflight checker was run.

## Review by Q37

I read cor-mg-det-weight-exterior.md and cor-mg-det-weight-exterior.proof.md in the current main-20261015 blueprint, compared the statement with the master import, and read the statements of every cited node. For the two substantive inputs I read the current main comparison lemma lem-rp-determinant-weights-agree.md and conditional theorem prop-ag-det-weight-exterior.md as well. The comparison states finite geometric determinant for every nonzero lisse Weil sheaf and equality of the two normalized weights for irreducible ones. The conditional proposition states both weight inclusion and existence for each admissible tuple, with the same capacity bounds as this item. Thus the reduction does not borrow anything from a dependency's proof.

Step 1 uses def-real-weil-representation-operations for the exterior action and the meaning of constituent; prop-wf-weil-sheaf-representation-equivalence explicitly gives an exact tensor equivalence and matching subobjects, quotients and subquotients in both directions. These supply the lisse sheaves to which step 2 applies. def-mg-weil-composition-series explicitly makes simple factors nonzero and Weil-simple. def-mg-determinantal-weight-multiset retains every occurrence; the current source definition and its updated DAG statement agree on this. No assertion about semisimple geometric restriction is used here.

Step 2 uses d-weights for the real logarithmic character and lem-rp-determinant-weights-agree for both its clauses. Normality, geometric connectedness, the same finite field and the same fixed iota are present in the item and the lemma. The factors supplied by step 1 are nonzero and irreducible. Consequently finite geometric determinant holds for every input and output factor separately, and their iota and lambda-iota weights agree. No assertion that finite determinant is automatically preserved by arbitrary subquotients is smuggled in: the lemma is applied anew to each factor.

Step 3 uses exactly prop-ag-det-weight-exterior's statement. Its nonzero original sheaf, composition series and degree range are those fixed in the item; every additional finite-determinant hypothesis was discharged in step 2. Replacing input weights by equal numbers leaves R and every r(gamma) literally unchanged. The proposition expressly supplies both directions and does not require Weil semisimplicity. Step 4 is elementary substitution of the equality from step 2 in each conclusion, with no new lemma or external citation. Each step is below 2000 characters.

I checked r=0: the sole admissible tuple is all zero and the unit exterior power has weight zero. At r=dim V, all capacities are filled and the determinant line has the total rank-counted weight. In rank one these are the two endpoint cases. Equal input weights aggregate their ranks rather than losing repeated factors. For weights 0,1,2 in three rank-one factors and r=2, the possible sums 1,2,3 follow the capacities; for four factors of weights 0,1,1,2 the sums arising from selecting 0+2 and 1+1 coincide, and the statement correctly requires existence without prescribing multiplicity. Nonsemisimple Weil extensions are not replaced by direct sums in this proof. There are no new statements requiring additional edge-case tests.

Against delivery-errors B–E: no statement-only child with a hidden proof, no duplicate, no new-node relabelling, no tags without a cited node, no added hypotheses or weakened clause, and all cited material is available in the cited statements. The repair from the import is expansion of the proof and addition of two notion dependencies, with all import and audit metadata retained. The full quoted statements in citations.json let the mechanical checker verify C4 without altered wording.
