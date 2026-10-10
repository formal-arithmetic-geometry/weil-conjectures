Files written:

- `dag/nodes/sec-picard-framework/def-pc-derived-direct-image.json` (definition, no Mathlib exact match)

Attachments:

- None. No sorry-free project declaration states this exact scheme-level definition.

WANTED:

- None.

What was checked:

- The item source is the blueprint node document `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-coherence/def-pc-derived-direct-image.md` as recorded in the node, with external source Stacks Tag 0A1G. The statement introduces a scheme morphism `f : X -> S`, defines `Rf_*` as the total derived functor on `D(O_X)`, and identifies `H^i(Rf_*E)` with `R^i f_*E`.
- Existing DAG search found the same notion referenced by Picard definitions and existing derived direct-image lemmas, but no duplicate definition node. The statement dependencies `def-pc-scheme` and `def-pc-derived-category` are the definitions actually used.
- I searched the slopmaster2 source for the item id and relevant derived direct-image names. The source contains generic right-derived-functor implementations and pro-etale operations, but no declaration tagged or stated as this exact project definition, so there is no attachment.
- Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch. The hits are generic `CategoryTheory.Functor.rightDerived`/related declarations or underived scheme pushforward declarations; none states the scheme-level total derived direct image with its cohomology-sheaf notation. LeanSearch was unavailable and is recorded as such in the node.
- This is a definition, so there are no proof steps, proof dependencies, or citation entries. I checked the empty `citations.json` against that fact and tested the edge cases conceptually: for the identity morphism the definition gives the identity derived functor and ordinary cohomology sheaves; for an arbitrary morphism it imposes no extra hypotheses beyond the stated existence of the derived functor.

## Review by K1

I read the item JSON, its blueprint source, the chapter and unit records, and the relevant source files in `WeilConjectures/SixFunctors/ProEtale/`. The source confirms that project code uses generic right-derived functors but does not declare this exact `def-pc-derived-direct-image` statement. The two cited statement dependencies define schemes and the derived category, matching the objects in the item. Since the node is a standalone definition, there are no proof steps whose hypotheses or node quotations need checking; `citations.json` is therefore the empty list. The item was changed only from imported to split status, with the blueprint `same_as` search recorded as empty and the split report documenting the definition clause. No new node was created, so duplicate-node and new-node checks are vacuous.

What could not be finished:

- Nothing.

## Second reading by K1

- Item statement: checked the morphism-of-schemes, total derived functor, and cohomology-sheaf clauses against the standalone blueprint definition and the Stacks derived-functor discussion (Tag 0716); after removing the unsupported parenthetical, the statement is self-contained and has no extra hypotheses.
- New node `def-pc-derived-direct-image`: checked B1-B7, including the two definition dependencies, TeX escaping, blueprint ancestry, and the recorded LeanFinder/Loogle/grep searches; verdict: accepted after removing the reference to an unspecified “file 02”.
- There are no proof steps or citation entries because this is a definition.
- Edge cases checked: the identity morphism gives the identity derived functor; the zero object has zero cohomology sheaves; an empty scheme introduces no additional hypothesis; and the statement does not assert a false vanishing or boundedness condition.
- Existing-node and blueprint searches: `tools/blueprint_refs.py ancestor/search` and repository `rg` found no duplicate definition node; the only similarly named underived/pro-etale definitions have different coefficient categories and domains.

Changes made:

- Set `blueprint.from` to the item itself with the exact definition clause it realizes, as required by the stage-1 blueprint contract.
- Removed the non-self-contained “file 02”/K-injective parenthetical and the unsupported claim that Tag 0A1G supplies the definition.

## Source error

The imported external source Tag 0A1G (Section 36.30) states cohomology-and-base-change results that use `Rf_*`; it does not define the total derived direct-image functor. The definition is supported by the general derived-functor treatment in Tag 0716 (Section 20.3), so the repaired statement no longer attributes its definition to 0A1G. This is a source-metadata error in the imported blueprint citation, not a change to the mathematical definition.
