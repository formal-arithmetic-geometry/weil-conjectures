# Stage-1 report: lem-pc-rf-single-complex-affine-base-change

Files written:

- `dag/nodes/sec-picard-framework/lem-pc-rf-single-complex-affine-base-change.json` (item, split)
- `dag/nodes/sec-picard-framework/lem-pc-affine-derived-base-change-comparison-map.json` (statement-only support node, unsplit; no Mathlib match)
- `citations.json` (verbatim statement excerpts for every proof citation)

Attachments: none.

WANTED: none.

The returned version omitted the datum of a morphism `L(g')^*K -> K'` and used the affine comparison arrow without a cited statement. I added that datum to the item, aligned its stalk map with the qcqs induction consumer, and added the statement-only comparison/localization node required by C1/C4. The item is the affine direction of Stacks Tag 0DJ8, not a declaration already present in `WeilConjectures/`.

## Review by F1

The review below checks the repaired map datum, the new comparison-map statement, every citation quote, and the affine hypotheses against Tag 0DJ8 and the qcqs induction consumer. I verified that the new node introduces the rings, complex, primes, and localizations it mentions, and that its statement-only form contains no proof sketch. I also checked the identity and zero-complex edge cases after the repair.

## Not duplicates

lem-pc-affine-derived-base-change-comparison-map vs lem-pc-rf-single-complex-affine-base-change: the new node only states construction and localization of the module comparison arrow, while the item proves that a supplied morphism and stalkwise isomorphisms make the full comparison a quasi-isomorphism.
lem-pc-affine-derived-base-change-comparison-map vs lem-pc-rf-base-change-single-complex-criterion: the existing criterion is the global qcqs theorem with arbitrary schemes and complexes; the new node is the affine algebra localization identity used inside its affine proof.
lem-pc-affine-derived-base-change-comparison-map vs lem-pc-derived-pullback-tor-independent-flat-complex: the existing node proves a stalkwise Tor-independent flat-complex condition, whereas the new node constructs the A'-linear derived module comparison and identifies its localization.

I read the imported item, its ancestor `lem-pc-rf-perfect-base-change`, the already-split qcqs induction node, and the Stacks source `/home/ubuntu/c1-stacks-review/perfect.tex` at the proof of `lemma-single-complex-base-change-condition` (Tag 0DJ8). I also read the induction statement to copy its explicit datum `L(g')^*K -> K'` and its stalk map. The affine source introduces `S=Spec(R)`, `X=Spec(A)`, `S'=Spec(R')`, `X'=Spec(A')` with `A'=A\\otimes_R R'`, translates the complexes through the affine derived equivalence, and reduces the assertion to the module comparison `M^\\bullet\\otimes_R^L R' -> M^\\bullet\\otimes_A^L A' -> N^\\bullet`; the repaired item and Step 1 follow this exactly.

Step 1 cites the existing affine derived equivalence, affine derived pullback/tensor computation, qcqs preservation of quasi-coherent direct images, and the new comparison-map statement; each says the translation or first arrow used. Step 2 uses the supplied morphism, the affine pullback identification, and the new node's A'-linearity to form the cohomology map. Step 3 uses affine tilde-stalk localization, exact module localization, affine tensor computation, and the new node's localization identity to identify the localized map with the displayed stalk map. Step 4 applies the maximal-localization criterion to maximal ideals of `A'`, then the quasi-isomorphism criterion.

I searched the DAG and blueprint for the comparison/localization statement and found no duplicate. I ran LeanFinder, Loogle, and Mathlib grep for the new node; only underived tensor universal-property declarations appeared, so the node is unsplit. I tested the repaired statement on identity base change, the zero complex, and one-term complexes; the comparison and localization formulas reduce correctly.

What could not be finished: nothing. The dry run is the remaining required check.

## Second reading by F1

- Source statement: checked the item against Stacks `perfect.tex`, Tag 0DJ8, Lemma `single-complex-base-change-condition`, including the affine reduction and the displayed localization formula; all affine, prime, and degree hypotheses agree.
- Step 1: checked the affine derived equivalence, affine derived tensor/pullback, and quasi-coherent direct-image statements; each cited statement supplies the translation used.
- Step 2: checked that cohomology is functorial for the displayed derived morphism and that the resulting map is A'-linear; this is elementary from the derived-category definition and the A'=A tensor_R R' identification.
- Step 3: checked the affine stalk-localization statement, exact localization statement, and affine tensor statement; expanded the K-flat-model localization and kernel/image argument so the identification with the stalk map is explicit.
- Step 4: checked the maximal-localization criterion and the quasi-isomorphism definition; maximal ideals are among the prime stalks, so the conclusion follows for every degree.
- New node `lem-pc-affine-derived-base-change-comparison-map` is statement-only, self-contained, sourced to Tag 0DJ8, and cited verbatim in Steps 1--3 and `citations.json`; its three searches are recorded in the node.
- Edge cases: the identity base change (R'=R) gives the identity comparison; zero complexes give zero isomorphisms; fields and the zero/one-degree complexes introduce no exceptional prime or localization behavior.
- Changes: repaired the missing map datum (E7), aligned the stalk map with the induction node, cited the comparison/localization statement in Steps 1--3, and updated proof dependencies and quotes. Historical `created.item` metadata is retained.
- Second-reader changes: removed a duplicated Step 3 dependency and corrected the split summary to record the one new comparison-map support node; no mathematical statement change was needed.
