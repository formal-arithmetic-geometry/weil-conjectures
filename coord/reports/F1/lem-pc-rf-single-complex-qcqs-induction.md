1. Files written:
- `dag/nodes/sec-picard-framework/lem-pc-rf-single-complex-qcqs-induction.json` (item, split; two new statement-only inputs and one Mathlib leaf reused).
- `dag/nodes/sec-picard-framework/lem-pc-rf-single-complex-affine-base-change.json` (statement-only, no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-rf-single-complex-relative-mayer-vietoris.json` (statement-only, no Mathlib match).

2. Attachments:
- `CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃` (and the companion positional lemmas) belongs to existing node `lem-sf-triangle-morphism-iso`.

3. WANTED:
- None. The source `literature/stacks-project/perfect.tex` and the cited relative Mayer--Vietoris source are present.

4. What was checked and changed:
The imported item was unsplit and has no declaration tagged with its id in either source checkout. I read the complete Tag 0DJ9 proof at `literature/stacks-project/perfect.tex:6532-6604`, including its affine reduction, use of the induction principle, and the displayed relative Mayer--Vietoris diagram. The affine child records exactly the affine module statement used there; the relative Mayer--Vietoris child records the open-cover comparison needed for the induction step. Both children were searched in the whole DAG and blueprint before creation and searched with LeanFinder, Loogle, and Mathlib grep; the generic hits do not state the required derived scheme results.

Step 1 is the local-on-the-base reduction from the first paragraph of Tag 0DJ9; I checked that restriction to an affine open preserves the comparison map and that the cartesian base change remains the relevant square. Step 2 cites the affine child, whose hypotheses are the same stalkwise maps specialized to affine rings. Step 3 defines the induction property on quasi-compact opens and cites the existing `lem-sc-invert-s-cohomology-induction` statement; its hypotheses match the qcqs X and affine-base gluing route. Step 4 cites the relative Mayer--Vietoris child for the exact three restriction maps and the existing Mathlib-backed triangle-isomorphism node for the two-out-of-three conclusion. The item keeps its original hypotheses and target, and `proof_deps` is the union of all cited nodes.

I tested the edge cases in the source argument: a one-open affine cover reduces to Step 2; a cover with empty intersection makes the overlap comparison vacuous and the triangle argument degenerates to the two open terms; and the singleton cover U=X gives the asserted map directly. I also checked every citation quote verbatim against its node statement and declared the induction principle as an off-unit generic tool use.

5. Could not finish:
No unresolved issue.

## Not duplicates
lem-pc-rf-single-complex-affine-base-change vs lem-pc-rf-single-complex-qcqs-induction: the new node is only the affine module reduction used as the base case, while the existing item concludes the global qcqs derived direct-image isomorphism.
lem-pc-rf-single-complex-affine-base-change vs lem-pc-rf-base-change-single-complex-criterion: the new node is the affine stalkwise-to-module implication; the existing criterion is a later specialization for a tensor product and cites the qcqs item, so using it here would be circular.
lem-pc-rf-single-complex-affine-base-change vs lem-pc-derived-pullback-tor-independent-flat-complex: the existing node proves stalkwise tor-independence for a flat complex, whereas the new node converts the already-assumed stalk maps into the affine derived-module isomorphism for arbitrary K and K'.
lem-pc-rf-single-complex-relative-mayer-vietoris vs lem-pc-rf-single-complex-qcqs-induction: the new node is only the open-cover gluing implication under three induction hypotheses; the existing item quantifies over all qcqs schemes and proves the result by induction.
lem-pc-rf-single-complex-relative-mayer-vietoris vs lem-pc-rf-base-change-single-complex-criterion: the existing criterion is a downstream tensor specialization whose proof cites the global qcqs item, while the new node is the independent relative Mayer--Vietoris induction step needed to prove that item.

## Review by F1
I read the item source and every source named by the new nodes. The affine child uses precisely the stalkwise-to-module equivalence of Tag 0DJ8, while the relative child states the relative Mayer--Vietoris comparison from the Tag 0DJ9 induction paragraph. The item’s four steps follow the source in order: affine localization, affine case, qcqs induction, and Mayer--Vietoris plus the triangulated isomorphism criterion. I verified the qcqs and quasi-compact-open hypotheses at the induction step, and that the overlap hypotheses are exactly those required by the relative triangle. The only correction to the imported record was replacing the empty proof with these source-aligned steps, adding the two missing statement-only inputs, and adding the exact citation quotes and tool-use declaration.

## Second reading by F1
Step 1 checked against Tag 0DJ9's local-on-the-base paragraph: the comparison map and base-change square are preserved under restriction; verdict accepted.
Step 2 checked against Tags 0DJ8 and 0DJ9 affine reduction: the stalk hypothesis and affine derived-module comparison match; verdict accepted after making prime images explicit.
Step 3 checked against the statement of `lem-sc-invert-s-cohomology-induction`: affine base case and quasi-compact gluing property match its hypotheses; verdict accepted.
Step 4 checked against Tag 0DJ9's relative Mayer--Vietoris induction and `lem-sf-triangle-morphism-iso`: the two overlap terms are the isomorphisms supplied by induction; verdict accepted.
`lem-pc-rf-single-complex-affine-base-change` checked against Tag 0DJ8: statement-only, self-contained affine square and stalk data; verdict accepted after defining compatible primes.
`lem-pc-rf-single-complex-relative-mayer-vietoris` checked against Tag 0DJ9 and `lem-pc-derived-mayer-vietoris-triangle`: statement-only and now explicitly quantifies the square, K, K', restrictions, and three comparison maps; verdict accepted.
Small cases checked: one affine open reduces to the affine node; an empty overlap leaves the two open terms; the singleton cover U=X gives the target comparison directly; field and zero complexes make the stalk condition and conclusion immediate.
Changes: repaired the missing definition of f' in the item, made the affine prime data explicit, expanded the relative node's formerly non-self-contained “as in” reference, and refreshed citation quotes to remain verbatim.
