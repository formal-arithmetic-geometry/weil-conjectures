## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-integral-element-prime-local-criterion.json` (statement, split, not a Mathlib leaf), `citations.json`, and this report. The search command generated `searches.jsonl`. No Lean, repository file, launcher file, or unit/chapter record was written.

The statement is unchanged. The six-step proof follows Stacks Tag 034K (`algebra-lemma-integral-closure-stalks`, algebra.tex:7629–7663). It forms the actual monogenic subalgebra B of A, spreads the local equation to B_f by an explicit denominator and annihilator calculation, proves B_f finite using the existing finite-adjoin leaf, selects a finite principal-open cover, descends module finiteness, and obtains a monic equation in B and hence A. There are no unresolved proof steps or new nodes awaiting splitting.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. Existing Mathlib leaves reused:

- `lem-sc-finite-generated-integral-subring`: adjoining a finite set of integral elements is module-finite.
- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`: principal-cover/unit-ideal equivalence and quasi-compactness.
- `lem-weil-pbc-module-finite-of-localization-span`: module finiteness descends on a finite principal cover.
- `lem-weil-pbc-finite-algebra-is-integral`: every element of a module-finite algebra is integral.

The only definition dependencies are the existing integral-element and module-localization definitions. All reused statement nodes are Mathlib leaves, so there is no off-unit tool-use request.

## Attachments

None. Searched the project library `lean/WeilConjectures/` for the exact blueprint tag and for integrality, localization, and primes. The matches concern normalizations, domains, or integral ring maps; no declaration states this arbitrary-ring elementwise prime-local criterion.

## Sources and searches

Read algebra.tex Tag 034K in full and its inputs: Tag 00GM (`lemma-characterize-integral`, including its proof), Tag 00GK (`lemma-finite-is-integral`), Tag 00EO(2) (`lemma-cover`), and Tag 00E8 (`lemma-quasi-compact`). Checked the tag-to-label correspondence in `literature/stacks-project/tags/tags`. Also read the two definition nodes and the complete statement of each of the four reused leaves, rather than using facts only in their proofs.

Searched the whole DAG by tags 034K, lemma-characterize-integral, lemma-cover, lemma-quasi-compact, monogenic, finite-generation/localization terminology, and expected Mathlib declarations; opened the existing nodes listed above. Ran `tools/blueprint_refs.py search` for integral, integral prime, and 034K, and `ancestor` for this item. No blueprint node states the criterion; ancestor returns null, matching the inherited record. No node was created, so there are no new/existing duplicate pairs.

The latest blueprint is main-20261023-1620 at 7284bb09daf97437d544c51882b325f9c52cd345. Read its `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-images proof (3), as well as the DAG chapter and unit records. The item remains the inherited algebra input for the normalization prerequisites. Its null blueprint ancestor and long provenance chain are retained; neither chapter nor unit route changes.

The five fresh searches are exactly recorded by the required msearch.py command: LeanFinder for the prime-local statement, Loogle `IsIntegral, Localization.AtPrime`, grep for local/prime integrality in RingTheory, LeanSearch for integrality of an individual element, and a second LeanFinder phrasing using maximal ideals. Read the returned hits and the source of `RingHom.isIntegral_ofLocalizationSpan` (RingTheory/RingHom/Integral.lean:44–69), the localization-integrality file, and `IsIntegral.of_finite` (IntegralClosure/Algebra/Basic.lean:64–73). The whole-map theorem needs a principal cover of integral maps, which the hypothesis does not directly give; deriving that cover for the monogenic algebra is the present argument. Almost-integrality and integrally-closed-localization results assume domains/fraction fields or have different conclusions. The inverse implication is therefore not a one-line specialization of these hits. The original node's earlier searches are retained alongside the actual new log records. All services answered; none was recorded as unavailable.

## WANTED

None.

## Corrections and unfinished work

No statement dispute, no change of hypotheses, no source error, and no abandoned argument. The imported node had no proof; this delivery supplies it. The source's phrase about looking at denominators is expanded to an equality in the actual subring B, avoiding any assumption that A maps injectively to its localization. No non-elementary step exceeds 2000 characters (the longest step of any kind is 918).

## Review by N8

I compared the item with Tag 034K: both allow an arbitrary unital map R to A, and both test the image of the same element at every base prime. In particular there is no hidden injectivity, domain, finite-type, or nonzero-ring assumption. I read delivery-errors B–E against these node files and sources.

Step 1 uses precisely the monic-equation definition in `def-weil-pbc-integral-closure` and the localization map in `def-weil-pbc-module-localization`. Applying a ring map to a finite sum and preserving its leading coefficient is elementary. The zero base ring forces the target ring to be zero, so the empty-spectrum case is settled explicitly by X, not discarded.

Step 2 uses the same two definitions. I checked the actual equality criterion in the localization node: an element mapping to zero is annihilated by an element of the multiplicative set. Writing d as the product of coefficient denominators and d_i as the product omitting the ith one gives s_i d_i=d, with no division in R. All these elements are outside the selected prime. The extra u outside the prime kills the cleared numerator in A. Since B is an actual subring, the same equality holds in B before localization. After inverting f=ud, both factors become units, so dividing yields the stated monic equation in B_f. This is a finite fraction calculation from the cited equality criterion, not an uncited theorem asserting that local integrality spreads out. No localization-injectivity claim is needed.

Step 3 first identifies the entire algebra B_f with the subalgebra generated by a/1 by the displayed fraction formula, in both directions. The cited statement `lem-sc-finite-generated-integral-subring` says exactly that the subalgebra generated by finitely many integral elements is finite as a module. Its base is R_f, its ambient commutative algebra is B_f, and its finite set is the singleton containing a/1, integral by step 2. Thus no comparison theorem for localization of adjoin, or for localization of integral closure, is silently used.

Step 4 uses clauses (iii) and (i) of the cited spectrum node: the opens form a cover because each selected f_p avoids p; compactness gives finitely many of them and the cover criterion gives the unit ideal. Step 5 applies the exact statement of the module-localization-span node to M=B, not A. Its unit-ideal and local finite-generation hypotheses were obtained in steps 4 and 3. Step 6 uses exactly the finite-algebra node for R to B. The resulting equation passes to A under the actual inclusion; this final finite-sum identity is elementary. `citations.json` copies verbatim the statements supporting all ten step/node citations.

I tested the denominator calculation on a noninjective map Z to Z/6Z, and on R=A=Z/6Z at its primes (2) and (3): factors outside a prime may be zero divisors, but the annihilator u and inversion of ud still make the calculation valid. For a zero target algebra, X is a relation; for a zero base algebra, step 1 applies. For a field base, the prime (0) gives the original condition. For Z to Q and a=1/2, localization at (2) detects failure, as required; the proof never claims that integrality at just the generic prime suffices. No new statement is being delivered, and the existing finite-adjoin and finite-algebra results are applied without a faithfulness hypothesis. I corrected the potential gap of concluding a relation only in A_f by deriving it in B_f itself. Nothing remains to repair before the tool checks.
