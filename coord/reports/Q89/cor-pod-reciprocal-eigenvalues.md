# Worker report: cor-pod-reciprocal-eigenvalues

## Files written

- dag/nodes/sec-poincare-duality/cor-pod-reciprocal-eigenvalues.json: statement split into five proof steps; no Mathlib match for the cohomological statement.
- citations.json: one verbatim statement quotation for each of the nine step/node citations.
- report.md: this report. searches.jsonl retains the exact searches run by msearch.py.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. I searched WeilConjectures by the blueprint id and by reciprocal/eigenvalue/similitude keywords. In WeilConjectures/EtaleCohomology/PoincareDuality/Frobenius/Reciprocity.lean, the two tagged declarations are AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap (line 61) and AlgebraicGeometry.Etale.TateOrientation.roots_map_charpoly_frobeniusOperator (line 96). Their section variables require [Finite Λ], and their own hypotheses require IsField Λ, a TateOrientation, Weil pairing and trace compatibilities, and an assumed perfect pairing. They thus address finite coefficient fields, not the E or algebraically closed characteristic-zero coefficient stages in this item. Their sorry-free bodies do not make the item an attachment. I did not treat upstream master sorry declarations as completed proofs.

## WANTED

None. The proof follows the available current blueprint and reuses an existing abstract linear-algebra node; it is marked agent-written. No SGA source is used.

## Corrections and deficiencies in the import

I read the main-20261015 corollary .md and .proof.md, the chapter _section.md, the sk-thm-frobenius unit _section.md and its DAG record. The imported statement is missing the explicit (K, φ_K) wording now in blueprint_update and names obsolete Theorem 9.23. I used the current statement, named the conventions node, and clarified the implicit algebraic-closure convention and the necessary choice of a trivialization of Λ(-d). These clarify the source's objects and keep the same hypotheses and conclusions. There is no false statement requiring a STATEMENT-DISPUTED repair.

The imported single proof paragraph concealed the inverse/transposition multiplicity theorem and treated the line-valued pairing as scalar-valued without a trivialization. It also cited def-weil-finite-coefficient-point as if it stated a theorem identifying cohomological duals, although its current statement defines coefficient evaluation. I removed that proof citation: the statement of thm-pod-degreewise-perfectness-over-a-field itself explicitly supplies the ordinary finite-dimensional dual. The optional proper clause now spells out compatibility with Frobenius, not just a vector-space comparison.

I searched the whole DAG for inverse-transpose, characteristic-polynomial, algebraic-multiplicity and similitude terminology. tools/blueprint_refs.py searches for characteristic polynomial, reciprocal eigenvalues, similitude and reciprocity found no second blueprint node stating this exact general-K, mixed-support corollary. The full sk-thm-frobenius theorem includes equivariance and similitude clauses, and prop-duality-reciprocity and thm-weil-poincare-duality concern the constant smooth-proper situation; none is the same statement. The existing lem-weil-similitude-pairing-reciprocity is the generic vector-space result, and is cited instead of duplicated. Its proof/statement dependencies contain no dependence on this corollary. I also reused lem-pod-proper-coincidence-frobenius rather than manufacturing a second compatibility lemma.

Mathlib searches were run exclusively through the mandated msearch.py command, with both natural-language phrasings, Loogle and source grep; all exact queries and actual hit names are in the item and searches.jsonl. The first LeanFinder query returned finrank/generalized eigenspace and finite-field Frobenius results; the second returned eigenvalue/spectrum lemmas. LeanSearch returned perfect-pairing definitions and transport lemmas. The first grep found no similitude theorem; the second found IsPerfPair, Matrix.charpoly_inv (Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean:315), and LinearEquiv.charpoly_conj (Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean:76). I read the perfect-pairing source at Basic.lean:30-85, the inverse-characteristic-polynomial source at Coeff.lean:300-330, and charpoly_conj at ToMatrix.lean:65-85. These are algebraic ingredients, not a one-line specialization proving the geometric corollary. No service failure was recorded as absence.

## Unfinished work

None in the one-level split. Existing cited unsplit nodes remain their own items. No new node is proposed, no Lean file was written, and no compiler, Lake or build command was run. The item is not the key node of sk-thm-frobenius, so no unit record is edited.

## Not duplicates

No new nodes. The general similitude and proper-comparison statements already exist and are reused.

## Review by Q89

I checked the main-20261015 corollary statement against clause (b) and Step 4 of sk-thm-frobenius. The field-stage restriction Λ∈{E, Q̄_l}, K perfect, strict Weil datum, dimension d and compact-support/ordinary distinction are all retained. Properness enters only step 5. The inherited geometric setting is now a real statement dependency through def-pod-conventions, and strict Weil data, perfectness, coefficient duals and multiplicities have their existing definition dependencies. I read def-pur-tate-datum in full for the field-stage data and its explicit assertion that q is a unit, and def-pod-conventions for the actual operator composites. This avoids applying a finite-coefficient-only definition at the rational stages.

For step 1 I opened thm-pod-degreewise-perfectness-over-a-field: its statement gives finite-dimensionality, identifies the right adjoint with the ordinary dual, and explicitly says the untwisted line-valued pairing is perfect. Choosing a basis of the one-dimensional value line and composing both adjoints with the induced linear isomorphisms is the written elementary part. No integral degreewise perfectness is inferred. The scalar adjoint Φ is now correctly typed.

For step 2 I opened cor-pod-untwisted-similitude and used exactly its displayed identity on the line-valued pairing, not its special constant-sheaf clause. Applying the linear trivialization preserves that identity. def-pur-tate-datum explicitly says q is a unit, so q^d is nonzero, including d=0. I opened the entire statement of lem-weil-similitude-pairing-reciprocity and matched its hypotheses: a field, two finite-dimensional spaces, both perfect adjoints, two linear endomorphisms and a nonzero multiplier. This node is a generic tool of another unit; the tool_uses declaration explains that role rather than replacing the geometric route.

For step 3 the cited generic node's clause 2 really states invertibility of both operators. The conjugacy itself is written out: substitute F^{-1}x in the similitude identity and evaluate Φ(Gy) on every x. No uncited characteristic-polynomial invariance or spectral lemma is hidden in this step. The cancellation under a change of line trivialization is explicit.

For step 4 clause 4 of that same node states the eigenvalue multiset transformation with algebraic multiplicity for every embedding into an algebraically closed field. The inclusion E→Q̄_l is allowed, and at Q̄_l it is the identity. Invertibility rules out zero, and the displayed cancellation proves that distinct eigenvalues cannot merge under α↦q^d/α. This gives exactly multiplicity m, without assuming diagonalizability.

For step 5 I read thm-pod-proper-poincare-duality for its canonical RΓ_c≅RΓ comparison and pairing identification, and the entire statement of lem-pod-proper-coincidence-frobenius for its natural κ and equation τκ=κτ_c under the identity compactification. The latter is stronger than a mere proper-space identification and is the reason it is cited. Combining its transport equation with the naturality square for φ_K and the definitions in def-pod-conventions gives the written conjugacy of operators. The source properness hypothesis is imposed here; X_0 proper gives X proper, exactly as thm-pod-proper-poincare-duality states. The comparison lemma applies to every coefficient stage, including both field stages here.

I checked B1-B10 and C1-C8 against the actual files: there are no new statements to be self-contained, no new Stacks tags needing duplicate pairs, no proof-only internal construction used as a statement, and no new axiom or compiler work. All citations.json entries are literal substrings of the current cited statements. The five steps are each shorter than 2000 characters; none hides a comparison or spectral claim beyond the nodes just named. D1-D5 are addressed by the written adjoint calculation and the existing generic tool, rather than a newly relabelled clause. For E1-E7 I checked zero-dimensional spaces, zero K, d=0, arbitrary i, nonproper X_0, and a nonsemisimple Jordan operator: the zero-space assertion is empty, the multiplier is 1 for d=0, and the multiset theorem preserves Jordan algebraic multiplicity without diagonalization. The integral counterexample in the unit (O_E→O_E by a uniformizer) remains excluded by the field hypothesis. The corrections I made were the line trivialization, the obsolete dual citation, the missing abstract multiplicity citation, and the proper Frobenius comparison.
