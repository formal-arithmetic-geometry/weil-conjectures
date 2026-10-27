## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-pointed-generic-integral-action-square-power.json`: statement; split into eight proof steps; no exact Mathlib match. The statement and statement dependencies are unchanged.
- No new nodes, no Mathlib leaves, and no unit record changed.
- `citations.json`: one entry for every step/node citation, with a verbatim quotation of the cited statement. The full statements are quoted so that all clauses being used remain visible.

## Attachments

None. Searches in the read-only project library `lean/WeilConjectures/` for the item tag, pointed/generic square powers, Picard admissibility and the square condition found no declaration giving this statement. No source declaration is treated as finished merely because its body is absent from this delivery.

## WANTED

WANTED: Guo, *Divisors on coherent schemes and ampleness of invertible sheaves on homogeneous spaces*, author version dated March 31, 2026, Sections 5.1 and 5.6, Lemma 5.7 and Proposition 5.9(1), for lem-sfb-pointed-generic-integral-action-square-power. The source URL https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf was read online; there is no corresponding local PDF in `literature/`. Nothing was downloaded. `proof_origin.by` is therefore `agent`, as the brief requires for a missing local source.

## Faults and corrections

The supplied node was statement-only. I found no statement dispute and changed no hypothesis or conclusion. In particular, I retained arbitrary test schemes, a single exponent chosen first, a section that need not be invariant, and the possibility of disconnected or geometrically reducible special fibres of Y.

A tempting application of `lem-sfb-normal-product-square-descent` in the order H,H,Y would fail: that statement assumes geometrically integral fibres for all three factors, including Y. I did not cite it. I followed Guo Proposition 5.9(1)'s permutation instead, applying the field square theorem in the order Y,H,H and descending along the final H using the existing generic-line theorem. The cube identity and the section restriction are written explicitly rather than hidden in a new lemma equivalent to the item. While checking the formulas I corrected the notation for the section restriction: e is applied to the common image s in S, not to a point of the parameter scheme T.

The ancestor command reports `blueprint.from.node = None` for this existing item's supplied creation chain. I retained that field and its inherited via list, and retained its concrete from.place. Searches of the whole blueprint (`tools/blueprint_refs.py search 'square'` and `search 'Picard-admissib'`), the DAG by Guo's source and square-condition terminology, and the latest blueprint found no blueprint statement of this auxiliary pointed-family result. `same_as` remains empty. I read the latest main-20261024 direct-image node and proof: its paragraph (3) now uses compactification and open/proper direct image and contains no group-ampleness argument. The historical normal-base ampleness lineage is noted in split_report.blueprint; this delivery only splits the assigned auxiliary, and does not change the unit or chapter route.

## Unfinished work

None within this stage-1 item. The already existing field-product-square and generic-line dependencies remain independent DAG items, as intended. No Lean was written or compiled and no repository or launcher file was edited. All output is in the assigned sandbox.

## Mathlib searches and reuse

The command log is `searches.jsonl`. I ran the required LeanFinder, Loogle, grep and LeanSearch queries through msearch.py and read their returned signatures. The action-square query returned ring Picard tensor identities, tensor powers, basic opens and purely inseparable tensor algebra, not a theorem about translation of line bundles on a scheme. A second LeanFinder phrasing in terms of the homomorphism to the relative Picard group returned `CommRing.relPic`, `Submodule.unitsToPic`, and ring Picard functor maps, again not the statement. The exact logged query text and results are recorded in mathlib_searches. All four services answered; none is represented as an absence result when unavailable.

I also explored flat generic-fibre integrality through the same command. Loogle found `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` and its pullback instances, which require geometric integrality of every fibre. Their hypotheses do not apply to Y here. The small affine localization argument from the already cited flatness and torsion-free-module statements is written in Step 3 instead of becoming a new node. The original search records in the item were retained, with duplicate tool/query records consolidated.

## Not duplicates

No new nodes. Existing field product-square power, smooth normality ascent, smooth composition, product geometric irreducibility, affine flatness, torsion-free flat modules, and generic-line pullback statements are cited directly. In particular no new version of the narrower normal-product-square-descent statement was introduced.

## Review by NM

I read Guo Sections 5.1 and 5.6, Lemma 5.7 and the final assertion and proof of Proposition 5.9, especially the section argument and the change of order in case (1). I checked the local Stacks source `divisors.tex`, Tag 0BCM (`lemma-flat-over-integral-integral-fibre`) and Tag 0BD7 (`lemma-in-image-pullback`), and `descent.tex`, Tag 034F (`lemma-normal-local-smooth`), plus `varieties.tex`, Tag 038F (`lemma-bijection-irreducible-components`). The source's geometric hypotheses hold here because smoothness gives the required reduced/normal fibre properties, the H-fibres are geometrically integral, the Y-generic fibre is geometrically integral, and Y has the supplied section. Properness and commutativity are not among the used hypotheses. There are no new nodes to compare against source statements.

For each proof step I opened every cited node's statement and checked the following uses, rather than borrowing material from its proof:

1. `lem-pc-smooth-flat` gives local finite presentation. Finite type gives quasi-compactness; the affine characterization in `def-weil-closed-immersion` makes the diagonal quasi-compact. These are exactly the three parts of finite presentation in `def-sbc-locally-finite-presentation`. The smooth-section-component statement gives an open containing the entire component through the identity in every fibre and with geometrically irreducible fibres. Connectedness makes that component the whole fibre; smooth-geometrically-reduced supplies the other half of geometric integrality. The identity section ensures nonemptiness. I did not infer integral special fibres for Y.

2. The cited proper-base-change node explicitly includes smooth base change as clause (2); it is not used for a fictitious properness hypothesis. The smooth-composition node states precisely composition of smooth morphisms. Smooth-normal-ascent has arbitrary normal bases, so it applies to each product projection starting from S. Local-Noetherian/lft permanence applies successively because every such projection is locally of finite presentation. Separated-base-change and the qcqs-permanence node's clause (3) give the corresponding generic-fibre properties. The geometric-product node states geometric irreducibility; I separately supply reducedness by smooth-geometrically-reduced, rather than confusing irreducibility with integrality. In particular P_eta is integral and nonempty.

3. The affine-flatness criterion gives flatness of R to D, and the flat-module torsion-free statement gives injectivity into the localization. The affine-fibre-product node identifies that localization with the coordinate ring of W_eta. Nonzeroness follows from the injection, so every nonempty affine meets the generic fibre. The written argument then checks reducedness and irreducibility globally. This is a few-line localization/topological argument, not a concealed general flat-integrality lemma. Surjectivity of P to S comes from the explicitly supplied sections, which also justifies the image of its generic point being eta.

4. `lem-sfb-field-product-square-power` gives a uniform positive integer and a square difference pulled back from the four-factor parameter scheme for three geometrically integral smooth separated finite-presentation factors. Its statement allows Y_eta as the first factor; neither a group structure nor integrality of special fibres is needed. This is the non-elementary power input. Invertibility and commutation with tensors and duals are checked on local generators using the two definition nodes.

5. `lem-sfb-normal-noetherian-generic-line-pullback` states exactly invertible-module descent from triviality on the generic fibre under its five listed conditions. I checked each: normal integral locally Noetherian P, locally Noetherian Z, smooth hence flat and lft projection, integral nonempty residue-field fibres because they are scalar extensions of H_s, and triviality over the generic point xi of P. The last assertion comes from the field square result restricted along xi to P_eta and a basis of the one-dimensional base line. I did not apply the theorem over S or use generic triviality over S as if it were already generic triviality over P.

6. The positive and negative factors of the eight-term difference are explicitly listed. After expanding, they are also the factors of D(y_0) times the inverse of D(y_1). Only symmetry of tensor products is used; the order of products of group elements is unchanged. The three definition statements give exactly the pullback, tensor and dual objects. This is an elementary identity with an existing global trivialization from Step 5.

7. The same elementary pullback identities and inverse-line evaluation identify restriction at y_1=e(s) with D times the inverse pullback of K=e_T^*D. The construction defines a real invertible module K on H^4; no gluing, effective descent, or invariant section is silently asserted.

8. I checked the four actual composites: u_0v_0^{-1}y=ghy, u_1v_1^{-1}y=y, u_0v_1^{-1}y=gy, and u_1v_0^{-1}y=hy for t=(g,1,h^{-1},1). The parameter line is N=t^*K. Pullback of one global isomorphism proves the claim for all B, including non-Noetherian and nonreduced ones, without invoking generic geometry over B. Tensor cancellation gives the exact displayed conclusion.

I checked the trivial group, the identity family Y=S, the trivial line, and base changes with nilpotents. For the missing-special-integrality pitfall, over a DVR R with uniformizer t take the smooth locus of Spec R[x,y]/(xy-t), namely the complement of V(x,y). Its generic fibre is geometrically integral but its special fibre is two disjoint copies of G_m. The section (x,y)=(1,t) exists; H=G_m acts by (x,y) mapped to (lambda*x,lambda^{-1}*y), and this section is not fixed. The proof still applies because its descent projection has H-fibres, and its parameter base is integral by Step 3. No hidden connected-special-fibre or equivariant-section hypothesis is present.

Against delivery-errors B-E: all cited objects are introduced, the item has no new statement-only node to hide a proof, every non-elementary input is a cited statement, all quotations in citations.json are literal substrings of those statements, and no argument is moved into a restatement of an item clause. Every proof step is below 2000 characters (maximum 1297). The two declared off-unit tool uses are the smooth-section-component theorem and product geometric irreducibility; they are generic scheme geometry, not replacements for a unit step. The trace-chapter names that occur are a Mathlib leaf on smooth composition and a Mathlib leaf on flat modules being torsion-free; both are generic geometry/algebra, with no trace formula or Poincare-duality input. No prohibited SGA route is used.

Server `srvcheck.py ... review_split` returned PASS with 0 new nodes. Its note that the existing unit has no realization recorded is about the unit key node, not a field this auxiliary worker may edit. The required full delivery dry run is performed next.
