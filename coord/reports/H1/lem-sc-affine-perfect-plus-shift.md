Files written:
- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-plus-shift.json`: split item, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-plus-locally-free.json`: statement-only unsplit node, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-map-lift.json`: statement-only unsplit node, no Mathlib match.
- `citations.json` and this report.

Attachments: `lem-sc-affine-perfect-map-lift` belongs to existing node `lem-sc-affine-perfect-map-lift`.

WANTED: `literature/stacks-project/perfect.tex` is absent from this checkout; I read the synchronized source `/home/ubuntu/c1-stacks-review/perfect.tex` for Tags 08ED, 08EH, and 08EI.

The item had no proof and no Lean declaration. The Stacks proof uses one missing auxiliary lemma and one existing DAG lemma, so I created the missing statement-only node rather than restating the item. The item source is Tag 08EI (Lemma 36.13.8). The new statement is Tag 08ED (Lemma 36.13.7); the affine map-lifting result is already stated by existing node `lem-sc-affine-perfect-map-lift` (Tag 08EH).

## Not duplicates

`lem-sc-affine-perfect-plus-locally-free` vs existing DAG nodes: no existing node states extension after adjoining a finite locally free summand; searches of `dag/nodes` for the Stacks label and key phrases found none.

`lem-sc-affine-perfect-map-lift` is an attachment to the existing DAG node with the same statement and Tag 08EH source.

## Review by H1

I read the complete proofs of Tags 08ED, 08EH, and 08EI in `/home/ubuntu/c1-stacks-review/perfect.tex`. Step 1 cites the exact 08ED conclusion and checks that X is affine, U is quasi-compact, and F is perfect. Step 2 cites the exact 08EH lifting conclusion, with E'=E and the projection endomorphism. Step 3 is elementary: after identifying via beta, the cone of the projection `id` on the locally free summand and `0` on F is the complementary summand F plus its shift; the cone of a morphism between perfect objects is perfect. The two citations in `citations.json` are verbatim portions of the corresponding node statements. I tested the cone claim on F=0 and on a one-term free complex; both give the expected split complexes. Lean searches for the item and each new node used LeanFinder, Loogle, and grep; none found a matching Mathlib theorem (LeanFinder returned unrelated scheme morphism results, Loogle reported the identifier unknown, and grep returned no hits).

What was wrong or incomplete in the imported item: it had no proof, and the source dependencies were implicit. No statement error was found.

What remains: the two auxiliary nodes are intentionally unsplit for later workers.

## Second reading by H1

- Item statement: checked against Stacks Tag 08EI, label `lemma-lift-perfect-complex-plus-shift`, hypothesis by hypothesis; verdict agrees (affine X, quasi-compact U, perfect F, extension restricting to `F \oplus F[1]`).
- Step 1: checked against Tag 08EI proof and the statement of `lem-sc-affine-perfect-plus-locally-free`; verdict cites exactly the finite locally free shifted summand extension and introduces no extra hypothesis.
- Step 2: checked against Tag 08EI proof and the existing `lem-sc-affine-perfect-map-lift` statement (Tag 08EH); verdict uses the stated factorization and restriction isomorphism with the correct source and target.
- Step 3: checked against Tag 08EI proof and the definitions of cone, direct sum, shift, and perfect object; verdict is elementary after the projection decomposition, including the zero-object and one-term finite-free cases.
- New node `lem-sc-affine-perfect-plus-locally-free`: checked against Tag 08ED, label `lemma-lift-perfect-complex-plus-locally-free`; verdict is self-contained, statement-only, and has the required definition dependencies and source tag.
- Existing node `lem-sc-affine-perfect-map-lift`: searched in `dag/nodes` and attached rather than duplicated; its statement was read and matches the use in Step 2.
- Mathlib searches: the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results were inspected; no exact declaration was found.

Changes: corrected the auxiliary node metadata so its `created.item` identifies this delivery, and added this second-reading audit. No mathematical statement or proof step required alteration.
