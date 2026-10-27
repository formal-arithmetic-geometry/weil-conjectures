# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-valuation-generic-relation-specialization.json: statement, split; no exact Mathlib match. Five proof steps, using existing nodes only.
- citations.json: eight step/node entries, with quotations checked against the current repository statements.
- searches.jsonl and search-item-*.txt: actual search log and full search responses.

New nodes: 0. New Mathlib leaves: 0. The localization input is an existing Mathlib leaf. The finite coefficient-selection induction is elementary and is written in the item rather than made into a node.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, generic relations, valuation specialization, primitive relations and coefficient normalization; the valuation-specialization declarations found concern scheme-valuative probes and do not state this polynomial assertion. No project declaration proves every clause of this item.

## Literature

No WANTED documents. Read literature/stacks-project/algebra.tex, Tag 00QK, label lemma-finite-type-domain-over-valuation-ring-dim-fibres, statement and entire proof (lines 31380 onward). Its generic-kernel paragraph divides by a nonzero coefficient of minimal valuation and then reduces the relation. Read also Tag 00DK, label lemma-tensor-localization, including its formula and proof, and Tag 00CM, section-localization, including the fraction equivalence relation and the explicit injectivity calculation for nonzerodivisor denominators. Checked all three tags against tags/tags.

Read the current latest blueprint chapter and the lem-trf-local-term-locality statement/proof and the existing unit record sk-i-curve-zero. The algebra argument is the existing DAG's valuation-dimension subargument in the semistable-alteration branch. It does not change the chapter/unit route. The latest local-term proof does not itself discuss valuation coefficients; the inherited blueprint.from chain records that finer DAG elaboration.

## Issues and corrections

No statement correction or dispute. The statement's coefficient equal to 1 is valid: the divisor is itself a coefficient, not merely an arbitrary element of minimal valuation. Finite type and quasi-finiteness occur elsewhere in the proof of 00QK but are not used in this extracted algebraic assertion. Kept them absent. Made the descent from L to B explicit, since the generic vanishing alone does not justify vanishing in an arbitrary algebra with torsion.

The inherited item had no proof, lean_audit record, or project declaration. Retained its statement, citations, existing search records, and blueprint provenance; added the completed proof and fresh logged searches. The new searches returned one-variable denominator normalization, Weierstrass changes, algebraic-independence definitions and residue maps. They do not establish the whole item. Inspected the candidate source for integerNormalization_spec (a one-variable polynomial) and isUnit_leadingCoeff (a field-coefficient statement), and the Weierstrass reduction module's scope. None is an exact or one-line specialization of the present assertion.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Searched the whole DAG by algebraic independence, valuation coefficients, principal finite ideals, localization/domain and the source tag 00QK. Searched the whole imported blueprint with blueprint_refs.py for valuation, algebraically independent, 00QK and generic algebraic dependence. Reused lem-weil-pbc-generic-fibre-localization-domain-irreducible rather than introducing another tensor/localization/domain lemma. Its statement explicitly supplies the localization and domain assertions required here.

## Review by NZ

I checked B through E of delivery-errors against the actual node statements and the source paragraphs, including their repeated historical copy. There are no new-node format, missing-definition, same-tag duplicate, or relabelling issues: the argument remains in the item's five steps, totaling under 3000 characters, and no step exceeds 2000 characters.

For step 1 I opened lem-weil-pbc-generic-fibre-localization-domain-irreducible and checked its hypothesis that every nonzero element of A stays nonzero in the target domain: this follows from A being contained in B. Its statement gives K tensor B as a localization and a domain. The tensor definition supplies the bilinear switch of factors; the proof writes the fraction-zero test to justify both injections rather than claiming an extra theorem from that node. These are exactly the generic-field identifications used later.

For step 2 I opened def-kun-transcendence-degree: its statement gives the supremum over independent subsets and defines independence by absence of nonzero polynomial relations. I spelled out why a tuple with no relation has distinct entries, so its image set really has cardinality n. The polynomial definition supplies finite coefficient support and evaluation. No finite generation of L/K is assumed. For n=0 the strict inequality is impossible, which removes the empty-coefficient-list case.

For step 3 I read the valuation condition in the item and checked the induction in both cases. If d/c lies outside A, c/d lies in A and multiplication preserves every earlier coefficient ratio. Both c and d are nonzero coefficients. The induction uses only that condition, multiplication in A, and the finite coefficient expression in the cited polynomial definition. It works in arbitrary rank, with no discreteness or assumption that all value-group subsets have minima. The chosen coefficient divided by itself is 1.

For step 4 the same cited polynomial statement actually includes its evaluation formula. Scalar multiplication by c inverse preserves zero in L; the injections already proved in step 1 then imply alpha(h)=0 in B. No new localization assertion is smuggled into this step.

For step 5 I opened both the polynomial and tensor definitions. Their statements contain the coefficientwise description, polynomial evaluation, and bilinearity used by the displayed finite sum. Reduction keeps the selected coefficient 1, and the tensor calculation shows the relation is in the special kernel without using flatness or injectivity of the residue map. The citations.json quotations are verbatim; the polynomial and tensor quotations include their full statements so the precise formulas are present.

I tested A a field (normalization still works), A contained in B=K with zero special fibre (e.g. for a DVR and alpha(t)=1/pi the relation 1-pi*t has coefficient 1), n=0 (hypothesis false), and positive or higher-rank valuations (finite induction only). For B=A[t] with alpha the identity the generic transcendence bound fails, as expected. A non-injective structure map is excluded by the domain-containment hypothesis and is never used. No off-route unsplit theorem is cited: the only theorem input is an existing Mathlib leaf and the other citations are definitions.

## Unfinished work

None in the one-level split. No Lean was written and no compiler, Lake or build command was run. Repository and launcher files were read only. Delivery validation and final push use the authorized delivery script.
