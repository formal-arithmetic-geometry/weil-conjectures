# Stage-1 report: lem-trf-sepclosed-valuation-geometric-components

## Files written

- dag/nodes/sec-trace-formula/lem-trf-sepclosed-valuation-geometric-components.json: statement; split into seven steps, retaining its statement and statement dependencies. No full Mathlib match.
- citations.json: one exact statement quotation for every node used by every proof step.
- searches.jsonl: the actual Q22 msearch results, retained as logged.

There are zero new nodes and zero new Mathlib leaves. The sandbox initially had only dispatcher markers, with no earlier item, split, report, or search log to recover.

## Attachments

No attachment for the whole item was found. I searched the project declarations under /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the blueprint id, separably closed residue fields, valuation rings, and geometric components. The normal-domain residue-field theorem in WeilConjectures/Mathlib/RingTheory/Etale/QuasiFinite.lean and the theorem attached to sbc-lem-etale-over-normal cover the residue-field input, not the geometric-integrality and canonical component-bijection clauses. The existing DAG attachment of the latter is reused, not changed. The upstream master checkout is reference material only.

## WANTED

None. All sources used are available in the shared repository. No SGA source is used.

## Corrections and scope

No statement dispute was found. The imported node had an empty proof and no proof dependencies. Its source description advertised a monic-polynomial lifting argument in a report that was not present in this sandbox. I replaced that proposed residue-field argument with the already existing normal-scheme strict-henselian-stalk theorem, Stacks 09Z9(2), after checking normality of every valuation localization. This is a generic tool below the unit route; it changes neither the item nor the trace-formula unit. The precise Stacks source places are now recorded. I kept the chapter, unit, creation record, blueprint ancestor and via list. The current unit is sk-i-curve-zero and its key node is lem-trf-local-term-locality, so no unit realization field is this item's to change.

The important issue in the component clause is that an arbitrary reduced closed subscheme of a geometrically reduced scheme need not be geometrically reduced. The proof uses the component's generic local ring, not that false general assertion. I also made explicit why the component bijection is the specific assignment C to C over the algebraic closure, and why the resulting scheme structure is the reduced induced one.

## Unfinished work

None for this one-level stage-1 split. Existing cited nodes retain their own statuses. No Lean files were written and no compiler, Lake, or build was run.

## Not duplicates

No new node was created. Whole-DAG keyword and tag searches, and whole-blueprint searches for valuation, separably closed field, and the full item notion found no blueprint node stating the full item. Existing subset-geometric-irreducibility, generic-stalk geometric-reducedness, field-tensor irreducibility and product-component nodes supply the needed general results and are cited directly. The search hits for smooth proper curves and component counts do not assert the full item with arbitrary finite-type geometrically reduced Z and arbitrary-height V.

## Review by Q22

I read Stacks varieties.tex Tag 020J (lemma-separably-closed-irreducible), Tag 038H (lemma-separably-closed-field-irreducible-components), its Tag 038F product-component input, and Tag 04KS (lemma-generic-points-geometrically-reduced), including their proofs. For the valuation input I read algebra.tex Tag 00IC (lemma-valuation-ring-normal), and etale-cohomology.tex Tag 09Z9 (lemma-normal-scheme-with-alg-closed-function-field), including clause (2). There are no new nodes with additional sources to audit. I opened and read the statements of all 18 distinct cited nodes; citations.json quotes those actual statements without editing them.

Step 1 takes the integral affine spectrum, affine stalk and function-field identifications exactly from lem-weil-pbc-spec-domain-stalks-function-field. It checks the valuation condition again for each V at a prime, so lem-weil-pbc-valuation-ring-normal applies to the actual stalks, not just to V. No rank, finite-height or Noetherian hypothesis is introduced.

Step 2 uses the second clause of sbc-lem-etale-over-normal. Its hypotheses have all been proved in Step 1, except separable closedness of K, which is a given hypothesis. The definition node def-weil-pbc-henselian-terminology actually includes separable closedness of the residue field in “strictly henselian.” The quotient-localization fraction formula identifies that residue field with the exact field Frac(V/p) in the statement, including p = 0.

Step 3 uses lem-weil-pbc-reduced-induced-closed-subscheme for the actual closed immersion and reducedness. The statement of lem-sbc-subset-geometric-irreducibility accepts arbitrary subsets and the identity extension Omega = k; the required nonempty irreducible inverse image is precisely the given component. It does not require smoothness. The cited closed-immersion base-change theorem supplies the closed immersion after scalar extension. The affine tensor-quotient formula, written out in the step, identifies its image with the set-theoretic inverse image. The affine fibre-product node supplies the tensor-product chart; the quotient formula follows directly from the two universal properties.

Step 4 checks the prime really is minimal by maximality of the component, using the prime/irreducible-closed-subset correspondence. The reduced-induced node gives the precise quotient A/q. Reducedness of A is supplied by the hypothesis at L = k and def-pc-reduced-scheme. The minimal-prime localization node explicitly says q A_q = 0 and A_q is a field; this justifies the displayed equality of the component's and ambient scheme's generic stalks. The affine-open stalk node preserves the algebra scalar maps, so this is an identification over k, as needed for tensoring.

Step 5 checks geometric reducedness at that same generic stalk. Open-immersion base change and the affine fibre-product node give the reduced ring A tensor_k L for each L, and the tensor-localization-over-base node applies with R = k, algebra A, M = A, T = A minus q, and N = L. Its stated formula also preserves multiplication on generators, so it gives the ring identification needed. The two-line nilpotent fraction argument proves reducedness of its localization explicitly; it is not an uncited assertion of flatness or a stronger permanence theorem.

Step 6 applies lem-pur-geometric-reducedness-from-generic-stalks with X = C, whose reducedness was established in Step 3 and whose unique generic-point hypothesis was verified in Steps 4–5. Its statement gives exactly reducedness after every extension, without finiteness hypotheses. The definition of integral scheme then combines this with Step 3's nonempty irreducibility.

Step 7 uses lem-weil-pbc-field-tensor-irreducible over the separably closed base k for Omega and every E, and the affine fibre-product statement to prove the geometric irreducibility required by lem-sc-product-irreducible-components-bijection. This supplies the bijection for Z, with no properness assumption. For a component D mapped to C, D is contained in C_Omega, which is irreducible by Step 3, so maximality makes them equal. The uniqueness clause of the reduced-induced node applies because Step 6 has already proved C_Omega reduced, and closedness is supplied by the closed-immersion base-change node. Thus a merely topological bijection is not mistaken for an unproved equality of scheme structures.

I tested the claims on V = K (the generic-prime case), on a nontrivially valued separably closed field and arbitrary prime localization, on empty Z, on two intersecting affine lines, and on a purely inseparable field extension of an imperfect separably closed field. The last example explains why geometric reducedness of Z cannot be dropped: Spec(k(a^(1/p))) can be reduced and irreducible but acquire nilpotents after field extension. The proof does not assert k perfect and does not need it. In the two-line case the generic localization kills the other branch, exactly as the A_q calculation requires.

Against delivery-errors B–E: there is no new statement-only node to restate an item clause, no duplicate, and no new search record inferred from an unavailable service. All five fresh msearch commands returned actual hits or zero hits and are recorded with their original tool and query. The Mathlib geometric-integrality combination lemma assumes both properties already; it does not prove the item. Every non-elementary input in the seven steps is a cited node, with exact quotes in citations.json. The remaining quotient, localization and maximality calculations are written out. The item has no proof step longer than 2000 characters. Off-unit generic tools are declared in split_report.tool_uses; no route replacement or target change occurs.
