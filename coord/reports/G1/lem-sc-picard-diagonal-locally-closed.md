# Stage 1 report: lem-sc-picard-diagonal-locally-closed

## Files written

- Item: `dag/nodes/sec-abelian-varieties/lem-sc-picard-diagonal-locally-closed.json` (split into 4 proof steps).
- New statement-only node: `lem-sc-perfect-h0-locally-closed` (Tag 0BDL, no Mathlib match).
- `citations.json` contains verbatim quotes for every cited node use.

## Attachments

None. The related declarations in `WeilConjectures/AlgebraicGeometry/TheoremOfCube.lean` are sorry-bearing and do not state the item exactly.

## WANTED

None.

## What was wrong

The imported item had no proof. The Stacks proof uses the perfect direct-image theorem and the locally closed degree-zero locally-free locus (Tag 0BDL), neither of which was represented by an existing node for this route. I added only the broader Tag 0BDL statement; the item itself now carries the rank, pairing, and determinant-open arguments rather than restating its conclusion in a new node.

## Not duplicates

`lem-sc-perfect-h0-locally-closed` vs existing `lem-pc-rf-perfect-base-change`: the former constructs a finite-presentation immersion characterized by degree-zero locally-free pullback cohomology; the latter only asserts perfectness and arbitrary base change of a proper direct image.

## Review by G1

I read the item against More on Morphisms, Lemma `diagonal-picard-flat-proper`, Tag 0BDP, in `/home/ubuntu/c1-stacks-review/more-morphisms.tex` (the rank decomposition, perfect direct images, cup-product criterion, and determinant-open conclusion). Step 1 uses the exact universal structure-sheaf pushforward statement from `lem-sc-proper-flat-global-sections`; its hypotheses are the item's proper, flat, finite-presentation map and the item's universal pushforward assumption, and the connected-fibre consequence is the elementary fibre argument in the source. Step 2 uses the existing perfect direct-image/base-change statement and the new Tag 0BDL statement; both cited statements explicitly provide the conclusions used. Step 3 uses the projection formula and the universal pushforward identity to identify the two degree-zero pushforwards with the proposed module and its dual, then writes the dual-basis maps explicitly. Step 4 is the source's determinant-open argument and is elementary from the definition of invertibility of a determinant. I searched the DAG and blueprint for the Tag 0BDL statement and for duplicate Picard-locus nodes, and ran LeanFinder, Loogle, grep, and LeanSearch searches for the new node; LeanSearch was unavailable and recorded as such. I checked small ranks $r=0$ and $r=1$: the pairing criterion gives the zero module case directly, and for rank one the determinant is the usual scalar invertibility condition.

## Second reading by G1

- Item statement: checked against More on Morphisms, Lemma `diagonal-picard-flat-proper`, Tag 0BDP; hypotheses and universal base-change factorization criterion agree.
- New node `lem-sc-perfect-h0-locally-closed`: checked against Derived Categories of Schemes, Lemma `locally-closed-where-H0-locally-free`, Tag 0BDL; tor-amplitude, rank, universal pullback test, finite-presentation immersion, and pullback compatibility agree.
- Step 1: checked against the rank-decomposition paragraph of Tag 0BDP and the flat-open and proper-closed image nodes; the fibre and rank-component reasoning agrees.
- Step 2: checked against the perfect-direct-image and Tag 0BDL paragraphs of Tag 0BDP; the cited statements provide perfect base change and both rank loci.
- Step 3: checked against the cup-product paragraph of Tag 0BDP; projection formula, universal structure-sheaf identity, dual bases, and inverse maps agree.
- Step 4: checked against the determinant-open paragraph of Tag 0BDP; the open locus and final factorization equivalence agree.
- Small cases: rank $r=0$ gives the zero bundle, rank $r=1$ gives the scalar pairing test, and the empty scheme and field base are consistent.
- Changes: corrected the item's `created.item` metadata and expanded step 1 to cite the existing flat-open and proper-closed image nodes; no mathematical statement changed.
