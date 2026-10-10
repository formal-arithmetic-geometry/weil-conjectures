# Stage-1 delivery: lem-pc-kflat-pullback-preservation

## Files written

- dag/nodes/sec-picard-framework/lem-pc-kflat-pullback-preservation.json: split the item.
- dag/nodes/sec-picard-framework/lem-pc-kflat-stalk-criterion.json: new statement, unsplit; Mathlib searches found no match (LeanSearch unavailable).
- citations.json: verbatim excerpts for all cited nodes.

## Attachments

None. The project declarations found for etale and pro-etale flat resolutions assert a narrower claim; no sorry-free declaration states this ringed-space item.

## Wanted

None. I read the Stacks source at /home/ubuntu/c1-stacks-review/cohomology.tex, sheaves.tex, and more-algebra.tex; this checkout supplies the source missing from this repository's local literature directory.

## Corrections

The imported item cited def-pc-scheme for an arbitrary morphism of ringed spaces, although that node defines schemes. I wrote the full ringed-space and termwise pullback data in the item's statement and cited the inverse-image and sheaf-tensor definitions. The Stacks Tag 06YC proof uses the stalk criterion Tag 06YB and ring base change Tag 06Y1; the former is a genuine separate lemma, while the latter is the short calculation in step 3. The scheme-only lem-weil-pbc-module-stalk-pullback is not cited for the general ringed-space claim. The earlier Mathlib search records in the item were replaced by queries actually run for this split.

## Not duplicates

- lem-pc-kflat-stalk-criterion vs lem-pur-kflat-change-of-rings: the new node detects K-flatness of complexes of sheaves on a ringed space at every stalk, while the existing node concerns change of rings on a site for a K-flat complex already having flat terms.
- lem-pc-kflat-stalk-criterion vs lem-weil-pbc-module-stalk-exact: the new node concerns tensoring arbitrary acyclic complexes and is an iff for K-flatness; the existing node concerns ordinary exactness of a complex at stalks.

## Review by C1

I checked the item against the exact statement and proof of Cohomology Tag 06YC. It assumes only a morphism of ringed spaces and a K-flat complex; neither flatness of the ring map nor flatness of the terms is available or used. I read Tag 06YB for the new node: its forward direction gives K-flatness at a stalk, and its converse detects K-flatness by testing total tensors on stalks. The converse's point-supported complex argument uses the exactness of point pushforward, so the iff is stronger than ordinary stalkwise exactness and needs its own node. I tested the zero complex, a one-point space (ordinary modules), and an arbitrary nonflat ring map; all agree with the statement.

Step 1 uses the existing topological inverse-image stalk theorem for both module and ring sheaves, and the existing change-of-rings tensor-stalk theorem. Their statements give the natural isomorphisms needed to identify the differentials, as in Sheaves Tag 0098. Step 2 uses exactly the forward implication of the new Tag 06YB node. Step 3 uses the definitions of K-flatness and total tensor complexes: an acyclic B-complex remains acyclic after forgetting to A, and tensor associativity identifies the two total complexes. This is the proof of More on Algebra Tag 06Y1 and does not ask that B be A-flat. Step 4 uses exactly the converse implication of Tag 06YB. I checked each citation against the node statement, not its proof, and recorded verbatim excerpts in citations.json. The topological inverse-image and change-of-rings stalk nodes are generic tools from another unit, declared in split_report.tool_uses.

No part of the proof remains unfinished. The new stalk criterion is intentionally left unsplit for its own later item.

## Second reading by C1

- Item statement: checked against Cohomology Tag 06YC (label `lemma-pullback-K-flat`), including the general ringed-space morphism, termwise pullback, and K-flat conclusion; verdict: agrees hypothesis by hypothesis.
- New node `lem-pc-kflat-stalk-criterion`: checked against Cohomology Tag 06YB (label `lemma-check-K-flat-stalks`); verdict: self-contained statement with the stated ringed-space and stalk hypotheses, and no weaker conclusion.
- Step 1: checked against Sheaves Tag 0098 and the statements of `lem-weil-pbc-topological-inverse-image-stalk` and `lem-weil-pbc-stalk-change-of-rings-tensor`; verdict: those statements give the displayed stalk identifications and their naturality supplies the differentials.
- Step 2: checked against Tag 06YB and the exact statement of `lem-pc-kflat-stalk-criterion`; verdict: uses only its forward implication.
- Step 3: checked against More on Algebra Tag 06Y1 and the definitions `def-pc-kflat-complex` and `def-pc-tensor-complex-sheaves`; verdict: the underlying acyclic complex, tensor associativity, and total direct sums are explicitly accounted for, with no flatness hypothesis on the ring map.
- Step 4: checked against Tag 06YB and the exact statement of `lem-pc-kflat-stalk-criterion`; verdict: uses only its converse after establishing K-flatness at every stalk.
- Edge cases: the zero complex, a one-point ringed space (ordinary module complexes), the empty space, and a nonflat ring map all satisfy the stated implications.
- Existing-node audit: searched the DAG for the stalk criterion, K-flat terminology, and both Tag 0098 stalk facts; no duplicate criterion or Mathlib declaration was found. The two stalk tools remain recorded as cross-unit tool uses.
- Changes made: added this second-reading record required by the delivery contract; no mathematical node or proof text required correction after the source and citation audit.
