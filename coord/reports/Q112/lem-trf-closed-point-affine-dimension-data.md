# Stage-1 report: lem-trf-closed-point-affine-dimension-data

## Files written

- dag/nodes/sec-trace-formula/lem-trf-closed-point-affine-dimension-data.json: existing statement, now split in six steps; no whole-item Mathlib match.
- citations.json: verbatim statement quotations for every step citation.
- searches.jsonl: actual Q112 searches, including the second semantic phrasing.

No new nodes or new Mathlib leaves. All writes are confined to the assigned sandbox. No Lean writing, compiler, Lake, direct git command or local DAG/review checker was used.

## Attachments

None. Project-source searches for the exact blueprint tag and the function-field, closed-point and dimension notions found no declaration stating this whole conjunction. The already existing finiteType_domain_ringKrullDim_eq_trdeg theorem covers the dimension tool only, not this item.

## WANTED

None: all sources used are present locally.

## Problems and corrections

The imported statement is correct; no hypotheses, conclusions or statement dependencies were changed. Its empty proof is replaced by the assembly below. The affine chart is chosen from the finite-type cover supplied by the definition, so no unproved claim about all affine opens or global quasi-compactness is used. The stalk comparison explicitly preserves structural constants, and the quotient calculation identifies the actual residue field, not just an abstract field isomorphic to it. I corrected source label spellings to definition-finite-type (Tag 01T1, in Section 01T0) and definition-spectrum-ring (00DZ).

## Unfinished work

None for the requested one-level split. Existing dependencies retain their own statuses. The remote review_split check passed, with its informational note that the unit has no realization recorded; this item is an auxiliary node, not the unit's key statement.

## Not duplicates

No new nodes. Existing lem-sc-integral-function-field-affine-fraction, lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-zariski-lemma and lem-weil-pbc-finite-type-domain-dimension-trdeg are reused. Searches covered the whole DAG by 00P0, 01RV, 02JX, and the affine/stalk/field concepts; blueprint_refs searches covered dimension, function field, affine dimension, finite type field and closed point. None states the whole affine data package in this item. same_as remains empty and the exact recorded blueprint ancestor and via chain are retained.

## Review by Q112

I read Stacks morphisms.tex, lemma-alteration-dimension (02JX), especially its closed generic-fibre point paragraph. This item spells out the affine algebra needed in that argument. I also read the current main-20261015 blueprint's lem-trf-local-term-locality statement and proof: this algebra is below its normal-cone/contracting-correspondence route, with no alteration of that route. I read the chapter and sk-i-curve-zero unit records and the three levels in SETUP. No SGA route is used. No new node needed a separate source review.

Step 1 uses exactly the cover condition in def-weil-finite-type-morphism, the nonempty-affine domain condition in def-pc-integral-scheme, and the prime-spectrum description in def-weil-affine-spectrum. Stacks definition-finite-type (01T1) confirms this local choice. Spec K is the one affine base here; no finite global cover is asserted. Since x is in U, U is nonempty and A is nonzero.

Step 2 uses def-weil-closed-points for closedness of the singleton, and def-weil-affine-spectrum for the Zariski spectrum. I checked algebra.tex definitions 00DZ and 00E1: intersecting Zariski closed sets containing the prime gives V(m). The step writes the familiar maximal-prime argument out; it is elementary ring/topology reasoning, not a new auxiliary theorem or an assumption that arbitrary open subschemes preserve closed points in the reverse direction. Here closedness is restricted from X to U, which always holds.

Step 3 uses the full statement of lem-sc-integral-function-field-affine-fraction: it explicitly supplies eta in U, the domain and field properties, injectivity, inverse denominators and the quotient description. I read its source at morphisms.tex 01RV and its Mathlib declaration functionField_isFractionRing_of_isAffineOpen in FunctionField.lean. The generic field in the item is exactly that stalk. def-weil-pbc-module-stalk supplies restriction/germ compatibility; constants from K have the same germs through A and directly, proving the required algebra compatibility.

Step 4 uses lem-weil-pbc-affine-open-stalk-localization clauses (b) and (c), which explicitly give both the affine stalk isomorphism and its action on section germs. I read Schemes 01HV(6) and 01HF, and the Mathlib restriction stalkIso and germ_stalkIso_hom definitions. This isomorphism respects K by the same constants calculation, preserves units, and hence carries the maximal ideal to the maximal ideal. With def-weil-residue-field this gives the quotient-field isomorphism. No internal-Hom or etale stalk comparison is being inferred from an ordinary structural stalk statement.

Step 5 uses def-weil-pbc-localization-at-prime for the fractions in A_m, def-weil-pbc-finite-type-algebra for its finite generator meaning, and lem-weil-pbc-zariski-lemma for the finite-dimensional conclusion for a field generated as an algebra. The statement of that lemma has exactly these hypotheses; algebra.tex theorem-nullstellensatz (00FV), including its final sentence for arbitrary finite-type algebras, confirms it. I wrote the quotient map a/s -> bar(a)/bar(s), its surjectivity and kernel, and the generator images, so the field to which Zariski's lemma is applied is the actual residue field through Step 4. Maximality is available from Step 2. No algebraic-closedness of K is used or assumed.

Step 6 uses the statement, not the proof, of lem-weil-pbc-finite-type-domain-dimension-trdeg. I read the complete 00P0 lemma-dimension-prime-polynomial-ring and its proof in algebra.tex. It explicitly gives finiteness, global dimension equality and the same dimension at every maximal localization. The inputs are finite-type A from Step 1, domain A, the fraction field L from Step 3 and maximal m from Step 2. The field structure is the structural K-algebra fixed by Step 3, so the transcendence degree is exactly the item's r. This is a generic off-unit commutative-algebra tool, declared in split_report.tool_uses because no trace-unit statement supplies it; the unit's argument is not replaced.

I checked B--E in both copies of delivery-errors.md against these steps. There is no new statement-only-node packaging to audit, no clause moved into a new node, no circular use of this item or its parent, and every non-elementary fact is the statement of a cited existing node. citations.json contains a verbatim quotation for every uses entry. All proof steps are shorter than 500 characters, so none exceeds the 2000-character long-step threshold or hides a substantial sublemma. I retained the original statement and blueprint provenance, and recorded actual search outputs and their verdicts only.

Small cases checked: for X=Spec F with F/K finite, m=(0), L=F, both dimensions and trdeg are zero; for A=K[t] at an irreducible polynomial of degree greater than one, the residue extension is finite but need not be K, while both dimensions are one; for affine space all maximal localizations have the predicted dimension. Inseparable finite residue extensions are allowed. Non-quasi-compact locally finite-type integral schemes cause no problem since only the one chart at the given closed point is used. The excluded empty and zero-ring cases cannot enter Step 1 because x lies in U and X is integral. A generic nonclosed point of a positive-dimensional affine scheme is outside the hypotheses, so the false assertion that all prime localizations have dimension r is never used.
