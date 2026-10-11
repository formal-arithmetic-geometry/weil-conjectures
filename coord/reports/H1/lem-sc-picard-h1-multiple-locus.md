# Stage 1 report: lem-sc-picard-h1-multiple-locus

## Files written

- `dag/nodes/sec-abelian-varieties/lem-sc-picard-h1-multiple-locus.json`: split statement node.
- `citations.json`: verbatim quotes for every cited node in every proof step.

## Attachments

No sorry-free Lean declaration states the item. The slopmaster2 source contains no declaration tagged `lem-sc-picard-h1-multiple-locus`.

## WANTED

None. The Stacks source used for the item and the two statement-only dependencies was available in the local review checkout; the repository literature mirror does not contain the imported TeX files.

## Review by H1

I read the complete proof of `lemma-H1-O-multiple-picard-flat-proper` (Tag 0BF2) in `/home/ubuntu/c1-stacks-review/more-morphisms.tex`, lines 9519--9619. The item statement was checked against the lemma hypothesis-by-hypothesis: all three families are flat, proper, finitely presented; the universal structure-sheaf pushforward condition is written explicitly after every base change; the pullbacks, locally closed Picard loci, scheme-theoretic containment, and the fibrewise direct-sum H^1 map all match the source conclusion.

Step 1 uses the existing `lem-sc-picard-diagonal-locally-closed` statement only for the universal factorization description of the loci, which it explicitly supplies. Step 2 uses the existing `lem-pc-rf-perfect-base-change` statement for perfectness and arbitrary base-change isomorphisms of proper flat finite-presentation direct images. Step 3 uses the new residue-model node, whose statement explicitly supplies the finite-free complexes, the cohomology-dimension ranks, and chain-map representation. Step 4 uses that same statement for persistence of the residue-fibre rank conditions; the remaining minor and chain-map calculation is elementary linear algebra. Step 5 uses the new proper-section node, which states exactly that a fibrewise nowhere-vanishing section trivializes after shrinking.

For the new residue-model node I checked the source references to More on Algebra Tag 0BC7 and Derived Categories of Schemes Tags 06Z0 and 08EB, and tested the edge cases $h_1=0$ (the degree-one map is the unique map from the zero module) and a one-term complex (the normal form reduces to $\mathcal O_S$). For the section node I checked the source's final topological argument: the zero locus is closed, properness makes its image closed, and its disjointness from the fibre permits shrinking; the empty fibre and the already-trivial line bundle are immediate cases. I searched the whole DAG and blueprint for both statements and found no duplicate or more general existing node. I also searched the slopmaster2 source for the item tag and likely Picard/H^1 names; no exact sorry-free declaration exists. The item and both new nodes each have recorded LeanFinder, Loogle, grep, and LeanSearch searches, with LeanSearch recorded as unavailable.

## What was wrong or corrected

The imported item had no proof or proof dependencies. I supplied the five source-aligned proof steps and added only the two non-elementary generic dependencies that were absent from the DAG. The existing perfect direct-image theorem was reused rather than duplicated. No statement was weakened or changed.

## What remains unfinished

The new residue-model node is intentionally statement-only and joins the later queue, as required for a one-level stage-1 split. No Lean code was written or built.

## Second reading by H1

Step 1 was checked against More on Morphisms Tag 0BF2 and `lem-sc-picard-diagonal-locally-closed`; the universal factorization and scheme-theoretic intersection reduction are present. Verdict: pass.
Step 2 was checked against Tag 0BF2 and `lem-pc-rf-perfect-base-change`; its perfectness and arbitrary base-change use is exactly the cited statement. Verdict: pass.
Step 3 was checked against Tag 0BF2 and the existing `lem-sc-perfect-finite-free-residue-model` statement (Tag 0BCD); the finite-free ranks are supplied by that node and chain-map lifting is stated as the elementary affine-complex step. Verdict: pass after citation repair.
Step 4 was checked line by line against the minor argument in Tag 0BF2; the residue injectivity, the $h_1=0$ case, the vanishing of each $d_i$, invertibility of each $a_i$, and the chain-map identity are explicit. Verdict: pass after expansion.
Step 5 was checked against the final paragraph of Tag 0BF2, `lem-weil-pbc-proper-closed-image`, and `lem-weil-pbc-nonvanishing-section-trivializes`; the closed-image and trivialization facts are now cited. Verdict: pass after citation repair.

The item statement was compared hypothesis by hypothesis with Tag 0BF2, including all base-change pushforward assumptions, the scheme-theoretic containment, and fibrewise $H^1$ injectivity. The claimed residue-model dependency already exists in the DAG, so no new dependency node is delivered; its statement was reused rather than duplicated. Edge cases checked: $n=0$ gives the vacuous direct sum and forces $H^1(X_s,\mathcal O)=0$ under injectivity, and $h_1=0$ makes the minor argument vacuous. The finite-free, proper-image, and nonvanishing-section nodes were searched in the DAG before reuse.

Changes made: cited the existing finite-free residue-model node in step 3; expanded step 4 to include $h_1=0$, the $a_i$ isomorphisms, and the chain-map identity; cited the existing proper-image and nonvanishing-section nodes in step 5; added verbatim citation quotes for steps 3 and 5; corrected the report to record that no new dependency node is needed.
