## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-geometric-integrality-finite-field-test.json: statement, now split; no exact Mathlib match. No new nodes and no new Mathlib leaves.
- citations.json records verbatim statement quotations for each proof-step citation. searches.jsonl retains the searches actually run.

## Attachments

None. I searched the project sources under WeilConjectures/ for the blueprint id, geometric integrality, GeometricallyIntegral and the finite-extension/tensor/domain notions. The occurrences concern geometric integrality assumed as a hypothesis, particular curves or abelian varieties, and descent of existing geometric-integrality structures; none gives the finite-extension criterion for an arbitrary algebra. The exact upstream master was also searched as reference, not as proof evidence. The item has no recorded Lean audit or declaration.

## Wanted literature

None. WANTED: none.

## Findings and changes

The item statement is unchanged and agrees with Stacks Tag 0FWF, algebra-lemma-characterize-geometrically-integral, implication (2) to (1), and algebra-definition-geometrically-integral. In particular the algebra is arbitrary, and domain includes nonzero. I read Stacks' actual proof: it invokes the reducedness and irreducibility criteria. Below the unit level I use a different, explicit coefficient-specialization proof, recorded honestly with proof_origin.by = agent. The ingredients are basis existence and the weak Nullstellensatz, not a new node restating either the item or one of its clauses.

The fixed chapter and sk-p-dl-a1-perverse unit were read, as were the main-20261015 ancestor statement and proof. This is an algebra tool underneath the strict-local integral-fibre argument. It still proves precisely that argument's finite-extension-to-arbitrary-geometric-field input. No chapter, unit, target, or inherited blueprint metadata was changed.

Mathlib searches were run with msearch.py: leansearch, leanfinder, loogle and grep, with a second semantic phrasing and a second grep in AlgebraicGeometry/Geometrically. I read the logged first interrupted leanfinder result, whose process handle was lost, before continuing; it completed and is in searches.jsonl. The reducedness hits do not prove the domain property, and the pinned source of RingTheory/Nilpotent/GeometricallyReduced.lean in fact has a TODO for arbitrary extensions. The external service's informal descriptions are therefore insufficient evidence. I opened AlgebraicGeometry/Geometrically/Integral.lean: its class assumes all field base changes; it has no finite-extension testing criterion. I also read the LinearDisjoint.isDomain declaration, which needs a linear-disjointness hypothesis. These are not exact matches or one-line specializations.

## Not duplicates

There are no new nodes. Whole-DAG searches for 0FWF and the finite-extension criterion found this item and its existing parent. Blueprint searches for geometric integrality and finite-field-extension tensor-domain terminology found no equivalent algebra criterion. Existing basis, maximal-ideal, quotient-field and Zariski-lemma nodes are reused rather than duplicated.

## Unfinished work

None in the stage-1 split. No Lean was written and no compiler or build tool was run.

## Review by Q27

I read algebra.tex at algebra-definition-geometrically-integral and algebra-lemma-characterize-geometrically-integral (0FWF), its actual three cited ingredients, and algebra-theorem-nullstellensatz (00FV). The latter expressly applies to every finite type algebra over any field. For the elementary algebra facts I read algebra-item-exists-maximal-ideal (00BN), algebra-item-characterize-maximal-ideal (00BS), and fields-lemma-vector-space-is-free (09FN). I opened every cited DAG node and used its statement rather than its proof. There are no new node statements to check.

Step 1 cites lem-weil-pbc-vector-space-basis-through-vector, which states that every independent set extends to a basis and specifically gives a basis containing any nonzero vector. The hypothesis for applying it to 1_S is first proved using the degree-one extension and the displayed mutually inverse tensor maps. No restriction on the dimension of S is needed. The step uses the existence clause, not an unstated assertion about extension of tensor bases.

Step 2 proves the tensor-coordinate assertion directly: expansion of the first factor gives existence, and each coefficient map is induced by the balanced bilinear map (s,t) ↦ lambda_i(s)t. These coordinate maps prove uniqueness, injectivity for coefficient inclusions and nontriviality. Multiplicativity is verified on pure tensors and by finite distributivity. Thus it does not silently appeal to an uncited tensor-flatness or scalar-extension-of-basis theorem. The argument works for infinite I since each expansion has finite support.

Step 3 uses those explicit coordinates to form a genuinely finite type algebra A inside the given field K; it imposes no finite type condition on S or K. The two chosen inverse coefficients are included in the generators. Injectivity established in Step 2 makes the product zero already over A. The preservation of this equation is not inferred merely from its image under a noninjective map.

Step 4 uses exactly the statements of lem-weil-common-extension-fields-maximal-ideal (a nontrivial commutative ring has a maximal ideal) and lem-weil-common-extension-fields-quotient-field (its quotient is a field). The algebra A is a unital subalgebra of K, hence nontrivial. def-pc-field-extension gives the injectivity of a field homomorphism into a field and identifies the resulting L/k extension. The residue classes of the explicit finite generators generate L as a k-algebra, which is the precise hypothesis of lem-weil-pbc-zariski-lemma; its conclusion is finite vector-space dimension. I also opened the pinned Mathlib Zariski-lemma declaration to confirm the recorded leaf's content. All four cited statements give the facts claimed, and their complete sentences are copied in citations.json.

Step 5 uses the elementary coordinate computations of Step 2. Adjoining both chosen inverses is essential: arbitrary specialization could kill both factors. A unit cannot have zero image in the nonzero quotient field, so one coordinate of each factor survives. Both specialized factors are therefore nonzero and their product remains zero, contradicting the actual finite-extension hypothesis. Nontriviality of the arbitrary tensor algebra was established separately, so the zero-ring edge case is not overlooked.

I tested the hypotheses on S=0 (excluded already at L=k), S=k and polynomial algebras in arbitrarily many variables (the argument uses only finitely many coefficients), dual numbers (fail at L=k), a nontrivial finite separable field extension (splits after a finite extension), and a finite purely inseparable extension (acquires nilpotents after a finite extension). The proof makes no perfectness, separability, algebraic-closedness, Noetherianity, finite-generation, or finite-field-cardinality assumption. The term finite means finite extension degree, never finite cardinality. Positive characteristic and finite k cause no issue because Nullstellensatz uses residue fields, not rational points over k.

I checked B1–B10: no new unsplit node with a concealed proof, no extra notion, no fabricated search, no duplicate, no improper attachment; all formulas are delimited. C1–C8: every non-elementary ingredient is an existing cited leaf, the remaining tensor calculations are written out, the cited statements are sufficient, and the only off-unit proof facts are Mathlib leaves. D1–D5: the proof is carried by the five steps, not shifted into a replacement node or an unproved specialization assertion. E1–E7: all hypotheses checked as above. No step exceeds 2000 characters (maximum 791), and no SGA source is used. During self-review I specifically retained both inverse coefficients and the separate nonzero-tensor argument to close the two potential gaps. No statement dispute or source correction is needed.
