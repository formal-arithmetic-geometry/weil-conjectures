# Q132: lem-trf-analytic-type23-stability

## Files written

- dag/nodes/sec-trace-formula/lem-trf-analytic-type23-stability.json: item, split; statement unchanged; four proof steps.
- dag/nodes/sec-trace-formula/lem-trf-valued-finite-ramification-calculus.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-valued-tame-prime-tower.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-analytic-critical-polynomial-minimum.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-immediate-prime-polynomial-obstruction.json: statement, unsplit, no Mathlib match.

citations.json contains a verbatim statement quote for every step/use pair. searches.jsonl is the search command's original log. search-results.json retains all twenty new-node search answers, not merely hit counts.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and the analytic stability, defectless, critical-coset, immediate-prime and tame ramification terminology. No matching project declaration was found. The four new statements likewise have no project attachment.

## Sources wanted

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, §§2.1, 6.1–6.3 (especially printed pp. 9, 36–42, 47–49), for lem-trf-analytic-type23-stability and its four new nodes. The named archival PDF is absent in literature/. I read the author's exact v3 PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf using the browser, without downloading into the read-only clone. Thus proof_origin.by is agent, as the standing brief requires for missing archival documents. No SGA source is used.

## Corrections and blueprint route

There was no previous sandbox split or report. The imported item had no proof, so citing Theorem 6.3.1(iii) alone would only restate it. The new proof follows the first paragraph of its proof on printed p. 49. It does not cite analytic-uniformization, the parent which already uses this item; in particular it does not create a cycle by using uniformization to prove stability.

The source proves unramified generators for type 2/3 fields first and then uses that construction for all finite extensions. I expanded both occurrences: choose the residue/value coordinate, isolate the immediate remainder, kill it after tame descent with the polynomial obstruction, then apply the no-immediate-prime criterion. I use the polynomial formulation of Proposition 6.1.1 and Lemma 6.1.2 rather than introduce a separate definition of critical cosets. The critical-polynomial node explicitly includes |pb| < s and positivity of s; these cannot be omitted.

No statement dispute was found. The source's p=0 means residue characteristic zero; it is kept separate from the positive prime p used in exponents and prime-degree towers. The original nontrivial valuation hypothesis remains. All new statements introduce their own fields, residue/value notation, tame and unramified meanings and separability, rather than using the definition of an etale scheme morphism for an analytic claim.

Read the current latest blueprint's lem-trf-local-term-locality.md and .proof.md and the chapter/unit records. Its current proof uses contracting correspondences, rather than the older nearby-cycle/alteration branch recorded in this item's ancestry. This split serves the retained assigned analytic input and preserves that ancestry explicitly; it does not change the chapter, unit or their proof route. There are no off-unit theorem citations.

## Not duplicates

Whole-DAG statement searches for defectless, critical coset, moderately/tamely ramified, immediate degree-p extensions and defect formulas found no existing node supplying the four new assertions. Whole-blueprint searches used defectless, critical coset, moderately ramified, ramification and polynomial minimum; no matching blueprint statement was found. The broad ramification search returned unrelated Kummer/coefficient and weight nodes.

lem-trf-valued-finite-ramification-calculus vs lem-trf-analytic-etale-residue-degree: the existing node characterizes an etale valuation-ring inclusion by finite separable residue degree. It does not give the defect power, tame prime-to-p condition, multiplicativity, tame/immediate base change, or the residue lift inside a given extension used here.

lem-trf-valued-tame-prime-tower vs lem-trf-analytic-type23-stability: the new statement is generic ramification theory for any complete valued field; its criterion needs the absence of immediate prime extensions of every finite extension, and does not assert this hypothesis for our analytic fields. Its prime-tower clause is a reduction, not stability itself.

lem-trf-analytic-critical-polynomial-minimum vs lem-trf-analytic-type23-stability: the new statement concerns a specific polynomial infimum on fields already tame over a single rational parameter. It does not assert the existence of a tame parameter or the degree formula for arbitrary finite extensions. The item supplies the argument establishing such parameters, then applies this polynomial theorem again.

lem-trf-immediate-prime-polynomial-obstruction vs lem-trf-analytic-immediate-rationality: the new node produces coefficients and a nonattained infimum for a finite immediate prime extension over an arbitrary complete field. The existing statement instead gives a topological rational generator for a one-dimensional immediate extension over an algebraically closed ground field.

There are no shared Stacks tags requiring additional pairs: the new facts are from Temkin, not claims of a matching Stacks theorem. Elementary coordinate norm calculations and preservation by taking closures are written inside step 2, not made new nodes.

## Review by Q132

I read Temkin's definitions of defect, unramified and moderately ramified extensions, Lemma 2.1.5 and its proof on p. 9; the stability criterion at the start of §6.1 on p. 36; Proposition 6.1.1 and the precise critical/special coset definitions and Lemma 6.1.2 on pp. 36–38; Proposition 6.1.4's statement and immediate-case argument on pp. 38–40; the opening type classification and Assumption 6.2.1 on pp. 41–42; Proposition 6.2.4 and its type-2/3 proof on pp. 47–48; and Theorem 6.3.1's statement and complete first proof paragraph on pp. 48–49. Each of the four new statement-only nodes records which of these passages supplies it. The finite-ramification node also isolates the tame/immediate base-change consequence of this ramification calculus, so it is not silently assumed in the item.

Step 1 uses finite-ramification-calculus for completeness and finite invariants, for d=1 in residue characteristic zero, and for invariance of residue transcendence degree and rational value rank under a finite extension. The type-alternatives statement is opened and quoted; its hypotheses apply because a finite F/E is also finite over the originally given completed rational field. This is essential before choosing the coordinate anew in F.

Step 2 uses exactly the separating residue coordinate and cyclic value coordinate supplied by type-alternatives, and exactly the finiteness assertion of parameter-finiteness, whose statement I opened. Neither node supplies the Gauss-norm comparison: that argument is written out. Divisibility of the base value group excludes equal norms of distinct monomials in value type. The separating coordinate makes the residue extension separable; the unramified lift clause of finite-ramification-calculus can therefore be applied inside F/J. The equality of value groups and residue fields then gives an immediate F/U, and the defect power gives its p-power degree. I checked the unit approximation calculation on both polynomials and rational functions before passing to the closure.

Step 3 uses tame-prime-tower clause (1) with F/U, not with an arbitrary inseparable extension assumed tame. The tame/immediate base-change clause ensures that the resulting whole tower remains immediate, so its first nonidentity degree-p step is immediate. That step is the hypothesis of immediate-prime-polynomial-obstruction, including purely inseparable cases. Its coefficients satisfy precisely the positive-infimum and |pb|<s hypotheses of critical-polynomial-minimum. The base U'/J is tame by composition and J has the rational type computed in step 2. Thus the two cited statements genuinely contradict each other here. If the tower is empty then F embeds in U'; the tame intermediate-field clause and the immediate equality e=f=1 force F=U. No theorem about stability or the parent uniformization is hidden in this step.

Step 4 runs that same obstruction/minimum contradiction over an arbitrary finite F/E, for which step 3 has already constructed the tame parameter. Only then does it invoke tame-prime-tower clause (2). The resulting defect-one equality and finite e,f in finite-ramification-calculus are exactly the two clauses requested by the item. All cited nodes have verbatim statement quotes in citations.json, and proof_deps is exactly their union. Each step is below 2000 characters (the whole assembly below 3000); none hides a separate comparison lemma.

For small cases, H=E gives e=f=d=1; the ramification statements handle identity tame extensions and an empty prime tower. Residue characteristic zero is not substituted into x^p. The polynomial-minimum statement excludes s=0, so b=0 and a=0 gives no spurious positive minimum claim. Immediate-prime-obstruction covers separable and purely inseparable prime extensions, as the source's proof explicitly does. The analytic-minimum hypothesis retains algebraic closedness of k and the tame-parameter condition; neither is relaxed to mere completeness. The type-3 ratio has rational rank one rather than assuming a discrete absolute valuation. This avoids confusing local fields with these nondiscrete analytic fields.

I inspected the twenty search answers from msearch.py, with two semantic phrasings per new node plus Loogle and grep. Polynomial.exists_forall_norm_le (Mathlib/Topology/Algebra/Polynomial.lean:136) requires ProperSpace, which is unavailable; the value group contains the nontrivial divisible base group, so the fields here are not discretely valued local fields. Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (Mathlib/NumberTheory/RamificationInertia/Basic.lean:670) is the DVR/Dedekind finite-ring setting, not arbitrary complete rank-one valuation rings. I opened both sources and their hypotheses. The other hits concern residue maps of formally unramified rings, generic finite-field/separability results, spectral norm extensions or unrelated analysis; none states all clauses of a new node or a one-line specialization. Consequently all four new nodes remain unsplit and there are zero Mathlib leaves. Searches were made through the required command and retained verbatim; no failed service was called a no-match result.

## Remaining work

No stage-1 argument of the item remains open. The four new supporting statements remain unsplit by design; their later splits will prove the ramification and polynomial inputs. No Lean file was written and no compiler, Lake or build tool was invoked. Only the named sandbox was written.
