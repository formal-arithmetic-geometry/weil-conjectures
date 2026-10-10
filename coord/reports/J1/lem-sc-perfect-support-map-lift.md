Files written:
- `dag/nodes/sec-picard-framework/lem-sc-perfect-support-map-lift.json` (item, split)
- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-support-extension.json` (statement-only, Mathlib no match)
- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-map-lift.json` (statement-only, Mathlib no match)
- `dag/nodes/sec-picard-framework/lem-sc-derived-open-gluing.json` (statement-only, Mathlib no match)
- `citations.json`

Attachments: none.

WANTED: `literature/stacks-project/perfect.tex`, Tags 09IM, 08EK, 08EH, 08DG, because the checkout contains only the cited-tag index; the Stacks statements were checked against the public tag pages.

No statement error was found. The imported item was unsplit and its existing statement matches Tag 09IM. The three children are strictly smaller inputs used by the Tag 09IM proof and do not restate the target.

## Not duplicates

`lem-sc-affine-perfect-support-extension` vs existing DAG nodes: no existing node states Tag 08EK or an affine perfect support extension.
`lem-sc-affine-perfect-map-lift` vs existing DAG nodes: no existing node states Tag 08EH or affine lifting of derived morphisms.
`lem-sc-derived-open-gluing` vs existing DAG nodes: no existing node states Tag 08DG or gluing derived complexes with compatible maps.

## Review by J1

I read the target statement and its source tag 09IM. The public proof reduces quasi-compact X to a cover X=U union V with V affine, applies 08EK to obtain Q supported on T with Q|_{U intersection V} isomorphic to P direct-sum P[1], applies 08EH to lift the composite map to E over V while retaining support, and applies 08DG to glue the two perfect pieces and their compatible maps. Step 1 is the elementary finite affine-cover induction. Steps 2, 3, and 4 cite child statements whose quoted sentences supply exactly the objects, support, lifting, and gluing used; the quotes in `citations.json` are verbatim.

I checked hypotheses: V and U intersection V are affine/quasi-compact where 08EK and 08EH require them; T intersection V is closed with quasi-compact complement; tensoring by the perfect I in 08EH preserves perfectness and support; and 08DG supplies both the global object and the global morphism. The direct-summand compatibility follows from the U-piece P direct-sum P[1]. Mathlib searches were run for the item and each child using LeanFinder, Loogle, grep, and LeanSearch; LeanFinder returned only unrelated generic support/gluing declarations, Loogle and grep had no matching theorem, and LeanSearch was unavailable.

What remains unfinished: none in the split. The literature source file itself is absent from this checkout, so the report records the requested WANTED entry.

## Second reading by J1

- Item statement: checked hypothesis by hypothesis against Stacks Tag 09IM; verdict agrees, including quasi-compactness, quasi-separatedness, retro-compact complement, support, and compatible direct summand.
- Step 1: checked against Tag 09IM proof paragraph 1; finite affine cover and induction are valid for the quasi-compact complement; verdict elementary and sound.
- Step 2: checked against Tags 08EK and 09IM proof paragraph 2; the affine support-extension hypotheses and the projection map are present; verdict sound.
- Step 3: checked against Tag 08EH and 09IM proof paragraph 3; the affine specialization supplies the lifted map and preserves support through the tensor construction; verdict sound.
- Step 4: checked against Tag 08DG and 09IM proof paragraph 4; the overlap transition, the map on the shifted summand, and the compatibility equation are now explicit; verdict repaired and sound.
- `lem-sc-affine-perfect-support-extension`: checked against Tag 08EK, including affine X, quasi-compact open U, closed T with quasi-compact complement, and the `F \\oplus F[1]` restriction; verdict sound. Existing-node search found no duplicate.
- `lem-sc-affine-perfect-map-lift`: checked against Tag 08EH, including E and E' in `D_QCoh`, perfect source, restriction isomorphism, and tensor form; verdict sound. Existing-node search found no duplicate.
- `lem-sc-derived-open-gluing`: checked against Tag 08DG, including both object gluing and compatible morphism gluing; verdict sound. Existing-node search found no duplicate.
- Small cases checked: `U=X` (take the identity restriction), `T=X`, `T=\\varnothing`, affine X, and the zero perfect complex; all statements remain consistent.

Changes: rewrote Step 4 to define the map `P\\oplus P[1]\\to E|_U`, compose the two overlap isomorphisms, and state the local perfectness/support argument. No node statements changed.
