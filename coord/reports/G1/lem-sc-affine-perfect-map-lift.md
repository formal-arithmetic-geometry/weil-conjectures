Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-map-lift.json`: statement split into three proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-open-koszul.json`: new unsplit statement node; Mathlib searches found no match.
- `citations.json`: exact quotations for all cited node uses.

Attachments: none.

WANTED: none.

The item was unsplit and has no matching declaration in the slopmaster2 Lean source. The source is Stacks Tag 08EH (Lemma 36.13.7); the local literature checkout does not contain the Stacks TeX, so the proof is recorded as an agent reconstruction of the affine Koszul argument. I checked the existing derived-Hom node and used it only for the bounded-projective Hom computation. The new child node isolates the non-elementary Koszul construction: a finite principal-open cover of U gives powers whose two-term Koszul tensor is perfect and isomorphic to O_X on U; tensoring preserves perfectness and support. The final step verifies the hypotheses (affineness, quasi-compactness, perfectness, and support) and derives the stated lifting equation from the isomorphism on U. No existing DAG node states this child, and Mathlib searches were run for both the item and child.

## Review by G1

I reread Tag 08EH (Lemma 36.13.7) in `literature/stacks-project/perfect.tex`, the affine comparison Tag 06Z0, the perfect-affine model Tag 08E7, the arbitrary-target RHom result in `cohomology.tex`, and the open-section result Tag 08JA in `sites-cohomology.tex`. The returned version incorrectly required a bounded-below representative of E' and hid the construction of the map from a Koszul object; those are now repaired by explicit statement-only nodes.

Step 1 cites the affine derived equivalence for passing between D(A) and D_QCoh(O_X), the perfect-affine node for a bounded finite-projective model, the strictly-perfect RHom node whose statement allows an arbitrary target complex, and the open-section node identifying alpha with H^0(U,RHom(A|U,E'|U)). I verified that each cited statement contains exactly the hypothesis used. Step 2 cites the new represent-cohomology-class-on-open statement, which directly supplies the Koszul object, its map to O_X, and the RHom morphism representing alpha; this repairs the core C1/D gap. Step 3 cites the new derived tensor-Hom adjunction for gamma and the representability node for the restriction isomorphism beta and the equality with alpha. Step 4 cites the existing Koszul node for perfectness, support containment, and the induced isomorphism on U.

For every new node I ran LeanFinder, Loogle, and Mathlib-source grep searches with the node's intended statement; the recorded results found no Mathlib declaration stating the result (the only matches were general K-projectivity, module monoidal closure, or underived sheaf Hom). I checked edge cases U empty, U=X, a one-element principal cover, and A=0. All new nodes are statement-only and have self-contained hypotheses, source tags, blueprint references, and no proof sketch. The item statement is unchanged.

## Not duplicates

lem-sc-affine-perfect-open-koszul vs lem-sc-affine-perfect-map-lift: the child asserts only existence of a Koszul perfect factor and its isomorphism on U (plus tensor preservation); the item additionally lifts an arbitrary morphism A|_U→E'|_U and constructs β and γ satisfying the compatibility equation.
lem-sc-affine-perfect-section-rhom-open vs lem-pur-rhom-global-sections: the existing node is a statement for the derived category of all modules on an arbitrary small ringed site, while the new node identifies morphisms in D_QCoh on an open subscheme and requires a perfect source; passing from all modules to D_QCoh is not a one-line specialization.

What could not be finished: no Lean code was written, as required for stage 1; the five new statement-only nodes remain unsplit queue nodes.

## Second reading by G1

- Item statement: checked against Stacks Tag 08EH (Lemma 36.13.7), including affine X, quasi-compact U, perfect source, arbitrary quasi-coherent target, restriction map, factorization through a map induced by a perfect Koszul factor, and support preservation; verdict mathematically consistent.
- New node `lem-sc-affine-perfect-open-koszul`: checked against the construction in Tag 08EH, lines 27--34 of the public tag page; verdict is a genuine smaller construction node, with `D(\mathcal O_X)` now explicitly defined.
- New node `lem-sc-affine-perfect-affine-strictly-perfect`: compared with existing `lem-pc-perfect-affine-bounded-projective`; verdict duplicate, removed from the split.
- Step 1: checked against the finite-projective model and ordinary Hom computation in Tag 08EH and `lem-pc-perfect-affine-bounded-projective`; verdict now cites the existing affine model and records the finite principal-open reduction.
- Step 2: checked against the explicit finite cover, powers, and total Koszul tensor in Tag 08EH; verdict cites the child for the non-elementary factor and states the tensor-perfectness consequence.
- Step 3: checked against the canonical Koszul map and the final map construction in Tag 08EH; verdict records restriction compatibility, perfectness, and support.
- Small cases checked: U empty (take I=0 and the factorization is vacuous), U=X (take I=O_X), X=Spec of a field, and a one-element principal cover.

Changes made: corrected the item node's `created.item` from the neighboring consumer to this delivered item; removed the duplicate affine strictly-perfect node in favor of `lem-pc-perfect-affine-bounded-projective`; updated Step 1 and its citation; added the missing derived-category definition dependency to the child node; and rewrote the split summary to describe the actual Tag 08EH finite-cover/Koszul proof rather than an unsupported obstruction-killing shortcut. No statement was weakened.
