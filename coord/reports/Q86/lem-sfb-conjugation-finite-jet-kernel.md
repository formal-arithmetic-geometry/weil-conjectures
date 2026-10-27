# Stage-1 delivery: lem-sfb-conjugation-finite-jet-kernel

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-conjugation-finite-jet-kernel.json`: split item, nine proof steps, no Mathlib match for the whole statement.
- `citations.json`: one entry for every step/node citation, quoting that node's statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log; `prepare.py` is a sandbox-only preparation script.

There are **0 new nodes and 0 new Mathlib leaves**. Every non-elementary input already has a node. There was no earlier item copy or report in this sandbox to preserve.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and for conjugation jets, augmentation ideals, and the scheme-theoretic centre. The relevant-looking Hopf-algebra and smooth-section files do not state the item. Unrelated complex conjugation and cohomological augmentations are not attachments. No Lean was written or compiled.

## WANTED

None: Milne's book and the Stacks sources used here are present locally.

## What needed repair

The live item was statement-only. Its mathematical statement is retained, with only an appended sentence identifying existing definition nodes for affine coordinates, ideal powers/quotients, tensors and representations; the corresponding statement dependencies were added. No hypothesis or conclusion changed. There is no statement dispute.

Milne, *Algebraic Groups* (2017), Corollary 8.10 and Proposition 8.9, printed pp.150--151, give the route: local finite-dimensional representations, descending kernels, Noetherian stabilization, and Krull intersection at the fixed point. I made the scheme structures explicit using increasing **ideals**, rather than only a descending chain of closed supports. I also made the coefficient argument explicit before testing the centre on arbitrary algebras; equality only on field-valued points would miss infinitesimal subgroup structure. The inverse-conjugation convention is checked in the proof. The affine quotient and local quotient used by Milne agree: an element outside I is a nonzero constant plus a nilpotent modulo I^(r+1), and its inverse is the finite geometric series. No change of the proof route is involved.

## Mathlib, DAG and blueprint searches

Ran the required item searches with `batch2/msearch.py`, under Q86 and this item, and recorded the exact queries and returned summaries in the item and `searches.jsonl`. Both natural-language formulations returned abstract/special-linear centres and representation intertwining results, not a group-scheme jet theorem. Loogle's two conjugate-equivalence hits concern modules on schemes. LeanSearch returned residue-field actions, an ideal stabilizer kernel, and unrelated categorical kernels. The Mathlib grep for conjugation/local jets and jet kernels returned no hits. All these services answered; none is recorded as unavailable. The inherited search entries from the live item were retained.

Searched the whole DAG by title and statement for Krull intersection, powers of ideals, Noetherian ascending chains, affine finite-type coordinate algebras, smooth connected integrality, group identity components, and rational-representation dictionaries. This found the existing inputs actually cited. In particular the existing `lem-weil-pbc-krull-intersection-jacobson` is a Mathlib leaf; there is no reason to create another separation lemma. Whole-blueprint searches through `tools/blueprint_refs.py search` for conjugation, finite jet and Krull intersection produced no statement equal to this item. Read the current `literature/blueprint/latest/` direct-image proof (3) and its ctf-stability unit, as well as the chapter/unit records. `ancestor` prints None, consistent with the item's inherited `blueprint.from.node: null`; I preserved its full ancestry/place and `same_as: []`.

## Not duplicates

No new node was created, so there are no new/existing-node pairs to distinguish. The finite jet kernel item itself is distinct from its parent about the unipotence of ker(Ad)/Z(G): it constructs the full finite-jet representations and detects the centre, without proving unipotence of the adjoint kernel quotient.

## Review by Q86

I read Milne 8.9 and 8.10 in the PDF, not just the imported source line, and Chapter 4(a), printed pp.83--84, for natural finite-dimensional representations. For the algebra inputs I opened Stacks `algebra.tex`: 00FN (`lemma-Noetherian-permanence`), 00IK (`lemma-Noetherian-basic`), and 00IQ (`lemma-intersection-powers-ideal-module`, part (2)), including the preceding local Krull theorem and its proof. I read 01T2 (`lemma-locally-finite-type-characterize`) in `morphisms.tex`, 0B7R (`proposition-connected-component`) in `groupoids.tex`, and 056T (`lemma-smooth-geometrically-normal`) in `varieties.tex`. There are no new nodes requiring independent sources. Every cited node's statement was opened and read; citations.json uses those exact statements.

1. Step 1 uses `lem-pc-affine-finite-type-algebra` with Y=G, k=F: the item supplies affine and finite type. It uses `lem-weil-pbc-finite-type-algebra-noetherian` with R=F, S=B: the field is Noetherian because it has only two ideals. The remaining monomial spanning and tensor quotient assertions are explicit basis calculations using the tensor and quotient definitions cited, not appeals to an unstated jet lemma. Centering the generators at e ensures that they generate exactly the augmentation ideal, not a different maximal ideal.

2. Step 2 uses the group-scheme diagrams and affine/tensor correspondence to form the actual A-scheme inverse-conjugation automorphism. Because it fixes the identity section, it preserves the kernel of evaluation and all its powers. I checked the order: c_(gh)^(-1)=c_(h^(-1)) after c_(g^(-1)), so pullback gives T_(gh)=T_g T_h. The cited `lem-sfb-rational-representation-comodule-dictionary` explicitly says that a natural group-valued representation on a finite-dimensional vector space is precisely a homomorphism to GL(V). Step 1 supplies finite-dimensionality, so this is not a citation of a mere definition for representability.

3. Step 3 is elementary: the quotient formulas already constructed preserve every power, the augmentation quotient is A, and both truncations of T_g take the class of b to the class of T_g(b). The cited quotient definition supplies the ideal-power and quotient meaning; no additional geometric assertion is used.

4. Step 4 again uses the dictionary's explicit universal-point coefficient formula, not a lemma from its proof. The closed immersion and quotient definitions identify the zero matrix equations with Spec(B/L_r); the group and subgroup definitions identify its algebra points as a kernel subgroup. Surjectivity of the quotient is the reason identity on V_(r+1) implies identity on V_r. Testing the universal point over B/L_(r+1) gives actual ideal inclusion; no claim about supports is substituted.

5. Step 5 uses the exact increasing-sequence clause of `lem-weil-pbc-noetherian-finite-module-acc` with M=B, a finite B-module generated by 1. This proves stabilization of L_r as ideals and hence of the full schemes, including nilpotents. It does not invoke a descending-chain theorem for arbitrary topological closed subsets to obtain a stronger result.

6. Step 6 uses `lem-sfb-locally-algebraic-group-identity-component` only for the geometric irreducibility of G^0, whose hypotheses (algebraically closed F and locally finite type G) are all present. Since G is connected, its open-subscheme component is G. `sbc-lem-smooth-geometrically-reduced` is applied to the structure morphism and its sole fibre, giving reducedness. The integral-scheme definition explicitly equates nonempty reduced irreducible with integrality and says that a nonempty affine coordinate ring is a domain. The identity point ensures nonemptiness. I do not use the dimension-one smooth-curve regularity lemma for this arbitrary-dimensional group.

7. Step 7 checks all hypotheses of local Krull intersection. I is maximal because B/I=F; the localization definition makes B_I local with maximal ideal IB_I. The localization-Noetherian node applies to the Noetherian B from Step 1. The Jacobson-radical Krull node applies with its finite module equal to B_I, generated by 1, and its ideal equal to that local ring's unique maximal ideal. Injectivity of B into B_I is written using the fraction equality and the domain property established in Step 6. It would fail for a general reducible B, which is why that hypothesis was checked rather than suppressed.

8. Step 8 is the direct-sum basis calculation for tensor products over a field: membership in A tensor I^n is coefficientwise membership in I^n. It is one routine argument, not an unstated theorem that arbitrary tensor products commute with arbitrary intersections. It works even for non-Noetherian or nonreduced A and for A=0. The tensor-product definition is the only cited node.

9. Step 9 applies separation to the actual difference of two pullbacks for each b. It then uses the full statement of `lem-sfb-affine-group-centre-base-change`, which defines centrality by commuting after **every** algebra extension A'/A; the affine correspondence makes identity of pullbacks identity of morphisms, hence identity after any extension. Conversely the centre condition applied to the universal point over A tensor B forces the morphism itself to be identity. I wrote the universal quotient-ring comparison showing equality of the two closed subgroup schemes. This uses neither a reducedness assumption on the kernels nor equality just on F-points.

I checked B--E of delivery-errors against this proof. No proof was hidden in a new statement-only node, no clause was merely renamed, no source tag was used as an uncited theorem, and no cited definition was mistaken for a missing geometric theorem. The only extra-unit statements are generic tools, declared in split_report.tool_uses: finite-type affine coordinates, Hilbert basis, ideal ACC, smooth reducedness, localization Noetherianity, and Krull intersection. The existing same-unit group and representation nodes retain the inherited route. All nine steps are under 2000 characters (longest about 1100), and the coefficient calculation is explicit.

Small cases: for G=1, B=F and I=0, V_r=F and the kernel and centre are both G; there is no zero-dimensional-GL problem. For commutative G, all conjugations are the identity and the kernel is again G. For G_a and G_m this holds in every characteristic. The proof allows a nonreduced centre, for example the central mu_p inside SL_p in characteristic p, since the equations are never radicalized. Test algebras include dual numbers, arbitrary polynomial rings, and the zero algebra; none is assumed reduced, finite type, or Noetherian. The group smoothness and connectedness are used exactly to get a domain and global-to-local injectivity. No characteristic-zero substitution or SGA route was used.

## What remains

No mathematical part of this item is left unfinished. The server's preliminary `review_split` returned PASS with zero new nodes; the unit's inherited missing realization is reported informationally and this auxiliary is not its key node. The required full delivery dry run and push follow this report.
