# Stage 1 report: lem-sc-perfect-h0-locally-closed

## Files written

- Item: `dag/nodes/sec-abelian-varieties/lem-sc-perfect-h0-locally-closed.json`, split into five proof steps.
- New statement-only node: `lem-sc-perfect-jump-loci` (Tag 0BDI, no Mathlib match).
- `citations.json` records the cited statements used by each step.

## Attachments

None. The slopmaster2 search found no declaration tagged 0BDL or stating this universal locally closed rank locus without `sorry`.

## WANTED

None.

## What was wrong

The imported item had no proof. The Stacks proof depends on the jump-loci lemma (Tag 0BDI), which was absent from the DAG, so I added that statement-only node. The item proof now follows Tag 0BDL: restrict to the upper-semicontinuous rank bound, use a local finite-free model and matrix equations to cut out the closed rank locus, verify the universal property after arbitrary further base change, and glue the finite-presentation charts with pullback compatibility.

## Not duplicates

`lem-sc-perfect-jump-loci` vs `lem-pc-perfect-locus`: the new node gives upper semicontinuity and constructibility of each fibre cohomology dimension, while `lem-pc-perfect-locus` concerns the stronger condition that all cohomology except one degree vanish and the remaining complex is a locally free module.

## Review by J1

I read the item source in `literature/stacks-project/perfect.tex`, Derived Categories of Schemes, Lemma `locally-closed-where-H0-locally-free`, Tag 0BDL, including its preceding Lemma `jump-loci`, Tag 0BDI. The item statement agrees clause by clause: perfect complex of tor-amplitude `[a,b]`, rank `r`, finite-presentation immersion, factorization tested after every further morphism, and pullback compatibility. The new jump-loci statement agrees with 0BDI: base-change invariance, upper semicontinuity, and locally constructible level sets.

Step 1 uses exactly the jump-loci conclusion and checks the open rank-bound reduction. Step 2 uses the definition of a perfect complex for local finite-free models and the jump-loci upper-semicontinuity; the source's truncation at the lower amplitude makes the preceding differential zero, so setting the finitely many entries of the outgoing matrix to zero gives degree-`a` cohomology free of rank `r`. Step 3 uses base-change invariance from the jump-loci statement and spells out both directions of the closed-subscheme universal property, including all further base changes. Step 4 checks finite type of the matrix ideal and identifies the pulled-back cohomology module from the same finite-free presentation. Step 5 is the elementary gluing argument because the local charts represent the same functor.

I checked edge cases `r=0` (the zero matrix and zero module locus) and `r=1` (the rank-one matrix-entry locus) and the empty scheme. I searched the whole DAG and blueprint for Tags 0BDI/0BDL and for jump-locus/rank-locus statements; only the distinct `lem-pc-perfect-locus` node exists. I ran LeanFinder, Loogle, grep, and LeanSearch for the new node and recorded the actual results; LeanSearch was unavailable.

## Second reading by J1

- Item statement: checked against Stacks Tag 0BDL, hypothesis by hypothesis, including perfectness, tor-amplitude `[a,b]`, `r \ge 0`, finite-presentation locally closed immersion, all further base changes, and pullback compatibility; verdict: agrees.
- New node `lem-sc-perfect-jump-loci`: checked against Stacks Tag 0BDI, including pseudo-coherence, fibre dimensions, arbitrary base change, upper semicontinuity, and locally constructible level sets; verdict: agrees.
- New node `lem-sc-perfect-finite-free-residue-model`: checked against More on Algebra Tag 0BCD and its use in 0BDL; verdict: agrees and is strictly smaller than the item.
- Step 1: checked against the first paragraph of Tag 0BDL and the cited jump-loci statement; verdict: the upper-bound open reduction and fibre-dimension argument are stated.
- Step 2: checked against the local finite-free model and matrix-entry construction in Tag 0BDL, with Tag 0BCD now cited for the model; verdict: outgoing degree-`a` matrix and zero-below-`a` cohomology are correctly identified.
- Step 3: checked against the matrix-locus universal-property argument in Tag 0BDL; verdict: both factorization directions and arbitrary further base change are explicit.
- Step 4: checked against the finite-presentation and pullback clauses of Tag 0BDL; verdict: finite matrix ideal and canonical pullback identification are stated.
- Step 5: checked against the chart-gluing conclusion of Tag 0BDL; verdict: elementary overlap gluing is appropriately isolated.
- Edge cases checked: `r=0`, `r=1`, the zero complex, a field base, and the empty scheme; no contradiction found.

Changes made: added the missing finite-free residue-model supporting node and cited it in Steps 2--4; expanded Step 3's converse to show why full-rank kernel forces the matrix to vanish; updated `proof_deps` and `citations.json`; corrected the new jump-loci node's `created.item` metadata; recorded the three Mathlib searches for the added node.
