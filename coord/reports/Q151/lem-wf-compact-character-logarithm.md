## Worker report

Files written: `dag/nodes/sec-purity-real-sheaves/lem-wf-compact-character-logarithm.json` (statement, split; no exact Mathlib match). The sandbox also contains `citations.json` and the actual search log. No new DAG nodes or Mathlib leaves.

Attachments: none. Searched the whole read-only `WeilConjectures/` tree for the blueprint tag, Weil-group names, compact characters and character/logarithm combinations. `PadicAlgCl.smallLog_mul` and `PadicAlgCl.injOn_smallLog` in `NumberTheory/Padics/Logarithm.lean` supply only the logarithm properties, not the existence of a uniform exponent for this Weil-group character, its continuity as an additive character, and both conjugation identities. Hence they are not attachments for this item. The item's audit is `none`.

WANTED: none. This is an agent proof following the supplied blueprint, not a claim of a newly obtained human reference.

The imported first paragraph used the exact sequence as if it supplied profiniteness; its statement only supplies the kernel identification. It also left the valuation's continuity and the compact-to-finite argument implicit. I cited the existing fibre-functor definition, automorphism profiniteness theorem, local-field absolute-value theorem and DVR theorem for exactly those interfaces and wrote the elementary intermediate arguments. The last imported step had no elementary verdict and did not check that the conjugates lie in the geometric subgroup; both are repaired.

Nothing remains unfinished in this one-level split. The cited deep-principal-unit logarithm remains an existing dependency to be split separately, not a result re-proved or renamed here.

## Statement corrected

STATEMENT-DISPUTED: as literally imported, chi was only required to be continuous, with no homomorphism hypothesis. Take E = Q_3 and the constant map chi(w) = 10 on W, for any admissible scheme (even Spec F_q). For every positive N, 10^N belongs to 1 + 9 Z_3 and differs from 1. Injectivity of the logarithm on that subgroup, supplied by the existing deep-logarithm lemma with r = 2, gives log(10^N) nonzero. Thus lambda(1) is nonzero and lambda cannot be additive. The constant map satisfies the written continuity hypothesis.

Corrected only the missing algebraic hypothesis: chi is a continuous **group homomorphism**. This is faithful to the source's title, “multiplicative curve character,” and to its proof's explicit uses of chi(gg') = chi(g)chi(g') and chi(sgs^-1) = chi(s)chi(g)chi(s)^-1. No restriction on chi(s), no finite-image assumption, and no additional condition on the scheme were added. The coefficient-definition citation makes the finite extension and its topology explicit; the conclusion is unchanged, including both N and r. The proof gives the intended role of r by placing every powered value in 1 + m_E^r.

## Blueprint and route

Read the chapter record `sec-purity-real-sheaves`, the unit record `sk-d-real-log`, the current main-20261015 item and unit files, and the older master item's full three-paragraph proof. The current item statement is unchanged from master and its current markdown has no proof. Steps 1–3 realize the old first paragraph, steps 4–5 its second, and step 6 its final paragraph. The unit defines the small logarithm on 1 + ell^2 O_E. Choosing r = 2e + 1 places all arguments in that domain, including ell = 2. There is no alternative purity route or SGA reference.

The item is not the unit's key definition, so no unit realization file is changed. Whole-blueprint searches for `compact character`, `compact valuation`, `logarithm`, and `aut-profinite` found the item, its existing deep-logarithm dependency, the small-log definition, and the existing automorphism profiniteness theorem, but no other statement of the item. The item's `blueprint.same_as` is therefore empty.

Generic tool uses are declared in `split_report.tool_uses`: `lem-galois-aut-profinite`, `lem-weil-l-adic-extension-absolute-value`, and `lem-weil-l-adic-extension-integers-dvr`. These provide compactness and the valuation calculation beneath the existing logarithm route; they do not replace a step of that route. The exact-sequence node is already Lean-closed. Definition citations are notions, not route changes.

## Not duplicates

No new nodes. The finite-image-of-a-discrete-valued-map argument is the finite-subcover argument written in step 3; the triviality of a finite subgroup of Z is written immediately after it. The valuation's local constancy is the two ultrametric inequalities written in step 2. None is packaged as an unnecessary new node.

## Mathlib searches

All searches were actually run through the required msearch.py command and are retained verbatim in the item's `mathlib_searches` and in `searches.jsonl`. Two semantic phrasings gave cyclotomic-character continuity and `PadicInt.continuousAddCharEquiv` results. Read `Mathlib/NumberTheory/Padics/AddChar.lean`, especially the overview and `addChar_of_value_at_one`: these concern multiplicative-valued characters of the additive group Z_p and their construction by Mahler series. They do not give an additive-valued logarithm of an arbitrary compact-group character. LeanSearch returned the same AddChar family, character-space compactness, and finite-group complex duality, none an exact match. Loogle's `IsCompact, MonoidHom` found a compact-open-space result, and `Continuous, "log"` returned generic topology declarations; neither states this lemma. Grep of topology/valuation and of principal units, Weil groups and character logarithms found no declaration of the item. Every service answered; no unavailable search is treated as an absence result.

## Review by Q151

I reviewed this delivery directly, as authorized by the direct-delivery brief, with the item and all cited node statements open. There is no second worker or claimed independent lead reading. The maintainer's independent review is still required.

For the item source, I compared the master proof with the current main-20261015 item statement and small-logarithm unit definition. Their intended character is multiplicative, while the literal statement omitted that hypothesis; the explicit constant-map counterexample above is the reason for the recorded correction. There are no new nodes whose sources need a separate review.

Step 1 uses `def-galois-fibre-functor` for the actual definition pi_1 = Aut(F), including finite fibres, a small skeleton, and the evaluation topology. It uses `lem-galois-aut-profinite` for exactly the assertion that this automorphism group is profinite when all fibres are finite. It uses `lem-wf-weil-group-exact-sequence` only for identifying Pi with the degree kernel. I checked the source conditions: U is the geometric base change of the geometrically connected finite-type scheme in the statement, and the finite-set fibre functor on a small skeleton meets the profiniteness theorem's size and finiteness assumptions. The usual Weil topology is spelled out as the convention under which restriction to Pi is continuous. The exact-sequence statement is not used as a topological theorem.

Step 2 uses `def-weil-l-adic-coefficient-extension` to fix the extended absolute value and its topology; `lem-weil-l-adic-extension-integers-dvr` clauses 1, 4 and 5 give norm-one units, a uniformizer with norm strictly between zero and one, and the unique unit-times-uniformizer expression. `lem-weil-l-adic-extension-absolute-value` supplies the nonarchimedean inequality used twice in the displayed local-constancy argument. The extension is finite over Q_ell and the absolute value restricts to the given one, exactly as these statements require. Multiplication of the expressions and uniqueness give valuation additivity directly, so no unstated valuation comparison theorem is hidden.

Step 3 uses the already established compactness and continuous integer-valued homomorphism. Its entire finite-image argument is the finite subcover of the disjoint open fibres. Its entire torsion-free argument is the distinctness of the multiples of a nonzero integer. This is elementary from those established facts, rather than an uncited compactness theorem or a new compact-character clause. The conclusion that valuation zero means a unit is immediate from the expression in step 2.

Step 4 uses `lem-wf-deep-principal-unit-log` for its full stated interface: every integer r > e/(ell-1), continuous logarithm on the principal-unit subgroup, and a single positive exponent that works for ALL units. I checked e > 0 because the absolute value restricts to that of Q_ell, so ell has positive valuation. With ell prime, r = 2e+1 is positive and satisfies the strict inequality even at ell = 2. Step 3 has put every chi(g) in the unit group, so the exponent really is uniform. The elementary valuation calculation for x/ell^2 checks the unit's original small-logarithm domain.

Step 5 again uses the explicit continuous group-homomorphism conclusion of the deep-logarithm node, not a construction hidden in its proof. The power map is a finite product; its multiplicativity uses the commutativity of E^times, not that Pi is abelian. Restricting its codomain to the principal-unit subspace preserves continuity, so composition gives the promised continuous additive map into E. No injectivity or exponential theorem is needed for this main conclusion.

Step 6 uses the exact-sequence node for a group homomorphism with kernel Pi. The two degree calculations show both conjugated elements are in Pi before lambda is evaluated. The subsequent cancellation is elementary in the abelian target and gives both equalities separately. No Frobenius-invariance theorem or comparison of conjugation conventions is invoked.

For delivery-errors B–E: there are no new statement-only nodes, duplicates, Mathlib leaves, or undefined auxiliary objects to audit. The item retains all imported flags and blueprint metadata and adds the missing notion citation. Every use in every step has a verbatim quotation in citations.json, checked against the cited statement; no source proof is used as a stronger statement. The proof itself carries the argument instead of passing a clause to a new node. All non-elementary inputs are the cited interfaces described above. Each step is under 2000 characters, and I checked that the longer valuation step contains only its explicit elementary calculation after those interfaces.

Small-case checks: the trivial character gives the zero additive character; finite torsion image is harmless because the unit exponent may kill it; no nontriviality of Pi is assumed; ramified extensions use their own e and uniformizer; ell = 2 satisfies the strict logarithm bound; and there is no compactness or unit condition imposed on chi(s), which cancels in each conjugation calculation. The correction is essential even on the one-element geometric group, as the constant-map example shows.

The concrete repairs from the imported proof are therefore the explicit multiplicative hypothesis, correct profiniteness citations, the valuation continuity calculation, the finite-cover calculation, uniform-exponent/domain verification, and both conjugation-domain checks. No statement below the item was edited, and no build or compiler was run.
