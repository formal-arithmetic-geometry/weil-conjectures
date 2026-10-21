# Worker report: sk-d-real-weights

## Files written

- dag/nodes/sec-purity-real-sheaves/sk-d-real-weights.json: definition, split; the combined Weil-sheaf definition is not a Mathlib declaration. Added primitive dependencies and five proof steps covering the assertions embedded in the definition.
- dag/nodes/sec-purity-real-sheaves/def-wf-positive-real-logarithm.json: definition, Mathlib leaf Real.log, with Real.log_of_pos, Real.exp_log, Real.log_exp and Real.log_pos for its clauses; no postponed proof.
- dag/units/sk-d-real-weights.json: only realized and realized_by filled, identifying the item as the realization of the unit statement. The unit has no proof steps.
- citations.json: one verbatim statement quotation for every step-node citation.

One new node, one Mathlib leaf. All changes are in the assigned sandbox. No Lean file was written; no compiler, Lake or local review/preflight script was run. searches.jsonl is the search tool's own unchanged log. prepare.py is sandbox scratch work and is not a delivery file.

## Attachments

No exact attachment for the entire item. The project declarations AlgebraicGeometry.WeilGroup.frobeniusWeight (Weights.lean:60), localPolynomial (:77), localEigenvalues (:85), IsPunctuallyPure (:94), HasWeightsAtMost (:102) and IsReal (:110) give the lisse definitions. Operations.lean:280 and :298 prove the two directions of the local conjugation criterion. These declarations do not state the constructible extension in the item's common coefficient framework. WeilConjectures/WeilSheaf/Stalk.lean:330,336,354 defines stalkwise predicates for the older WeilSheaf interface; its purity/bound use a power formula, and it does not itself prove the conjugation criterion. A docstring advertising a criterion is not its proof. Therefore these partial matches are reported, not claimed as an attachment of the entire item. The new logarithm primitive is directly Mathlib, so it is delivered as a Mathlib leaf under the brief's rule rather than a project attachment.

## WANTED

None. The current blueprint provides the definition; the analytic primitive is read in the pinned Mathlib source. The polynomial argument is explicitly agent-written, using existing DAG statements, rather than attributed to a source that does not give it.

## Problems corrected

The imported definition had only the setup and Weil-representation dependencies; its determinant, complex norm, logarithm, characteristic polynomial and root multiplicity were unnamed. It contained a reality equivalence without an argument. I added these notion dependencies and proved the equivalence, together with the inverse-root assertion and independence under Frobenius conjugacy. The mathematical statement is preserved: the extra wording fixes notation, introduces real w, and makes algebraic multiplicities explicit. No statement dispute was found.

The current setup assumes a field embedding, whereas def-weil-punctual-weights and def-wf-iota-real fix an isomorphism. I do not upgrade the embedding. The former is cited only for the constructible stalk and local geometric-Frobenius operator. The latter is not a dependency. The upper bound is a pointwise eigenvalue bound, not the mixed-filtration definition in def-weil-punctual-weights. These are materially different conventions and are not identified.

## Not duplicates

- def-wf-positive-real-logarithm vs def-weil-real-power: the existing node defines real exponentiation using exp and log; it does not define the logarithm by the inverse exponential or state positivity of log for x>1. The new node is the analytic primitive needed by the quotient, not another definition of exponentiation.
- sk-d-real-weights vs def-wf-iota-real: the latter supplies reality and realizability with a coefficient isomorphism; it does not give the logarithmic weight and upper-bound definition, and realizability is not part of this item.
- sk-d-real-weights vs def-weil-punctual-weights: the latter uses the exponential purity formula and defines mixedness by a filtration; the item defines a numeric local weight and a pointwise upper bound and also includes polynomial reality.

The entire DAG and blueprint were searched for the logarithm, local weights, reality and the conjugation criterion before creating the primitive. No blueprint node states the entire new primitive. No Stacks tag is attached to this standard Mathlib definition, so there are no same-tag pairs. The current blueprint main-20261015 is authoritative; master was read to understand the older unit record. No SGA source is used.

## Review by Q17

I read coord/delivery-errors.md B through E, including the repeated imported sections, and checked the actual statement and every proof step, rather than only the dependency lists. I read the main-20261015 sk-d-real-weights source, its unit and chapter records, sk-d-real-weil and sk-d-real-setup. For the new primitive I read Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:39-76 and 181-189. Real.log is defined at 44; log_of_pos at 50 gives its inverse-exponential meaning, exp_log at 59 gives existence, log_exp at 75 gives uniqueness by applying log to exp(t)=x, and log_pos at 188 gives the required denominator positivity. Every search in mathlib_searches was actually run through msearch.py and is in searches.jsonl; I read the returned hits. The two natural-language phrasings of the full item returned arithmetic Frobenius and Witt-vector results, not Weil-sheaf weights. The logarithm searches returned the actual exact matches. I have not recorded unavailable services as negative results.

For step 1 I opened all seven cited node statements. Monicity and degree supply a nonzero polynomial and the correct number of factors; algebraically closed factorization applies over Qlb. Invertibility gives a nonzero determinant and the constant-coefficient identity gives chi_F(0) nonzero. Thus no alpha_j vanishes. The reverse-characteristic-polynomial identity and finite-product reflection clause give exactly the displayed product, without citing a cohomology-specific eigenvalue lemma for an arbitrary Weil representation. The uniqueness clause of reciprocal-root factorization supplies precisely the multiplicities used. All fields and nonzero hypotheses in that lemma are present, including P(0)=1 and full degree n. This is a generic polynomial tool of another unit, declared in split_report.tool_uses.

For step 2 I checked the statement of sk-d-real-weil really specifies local Frobenius up to conjugacy inside the Weil group. The two determinant-definition statements both give basis independence. Writing the matrix in the transported basis gives identical entries, so this step does not assume any uncited theorem about a sheaf fiber comparison.

For step 3 I reread clause 3 of lem-weil-reciprocal-root-factorization. It asserts uniqueness up to reordering with multiplicities, not merely equality of the underlying root sets. Both products here are over C, with nonzero factors, constant coefficient 1 and degree n. Coefficient conjugation commutes with each finite product by its elementary sum/product formulas. A complex number is fixed by conjugation exactly when its imaginary part is zero. This proves both implications and keeps the condition on polynomials. It uses neither surjectivity of iota nor a real form of the representation.

For step 4 I checked the absolute-value node gives positivity from nonvanishing and the setup gives q_x=q^{e_x}>1 at a closed point. The new logarithm leaf gives the positive denominator. This is only an instantiation of the cited scalar definitions and the definition of the universal predicates. In step 5 def-weil-punctual-weights supplies the stalk notation and local operator, and constructibility gives finite-dimensional stalks. Its coefficient-isomorphism and mixed-filtration clauses are not used. All the preceding arguments are pointwise finite-dimensional linear algebra, so variable rank and singular strata pose no new assertion. No new lemma is hidden under “transport” or “standard”.

Small cases checked: V=0 or a zero constructible stalk gives P=1 and an empty spectrum; all weight predicates are vacuous and reality holds. For rank one, alpha=1 has weight zero, alpha=q_x has weight two, and a nonreal scalar is not real. A repeated nonreal eigenvalue remains nonreal; a conjugate pair has a real local polynomial with both multiplicities. A nonsemisimple Jordan block is permitted, because only the characteristic polynomial is used. Negative real weights and closed points of degree greater than one retain the same normalization q_x. The excluded case q_x=1 is impossible for a closed point over this finite field, and alpha=0 is impossible for an automorphism. No semisimplicity, integrality, or global rank constancy was added.

B: the new node is a self-contained definition, with no proof sketch or unsplit proof payload, an exact Mathlib match and file/line data. C: every non-elementary ingredient has a node; quotations in citations.json were checked as literal substrings. I checked the proposed existing dependencies have no path back to the item before writing them. D: the one new node is a standard analytic primitive, not a restatement of any sheaf clause; the proof arguments remain in the item. E: the hypotheses and small cases above are verified. Every proof step is below 2000 characters, so no long step hides an additional comparison lemma. The statement references now name all constituent notions. Nothing outside the permitted node and unit fields is changed.

## Unfinished work

None for this one-level stage-1 split. Existing imported dependencies remain separate items; this delivery makes no claim that the entire transitive library is finished. Maintainer independent review and the required server dry run decide acceptance.

## Dry-run repairs

The first dry run required four longer verbatim citation excerpts; these now quote the whole corresponding statements. The next server preflight required an explicit notion citation and a numeric mathlib_match.line on the logarithm leaf. The leaf now cites def-weil-real-power for the real-exponential convention and records line 44, already read in the pinned source. Its mathematical content and exact Mathlib match are unchanged.
