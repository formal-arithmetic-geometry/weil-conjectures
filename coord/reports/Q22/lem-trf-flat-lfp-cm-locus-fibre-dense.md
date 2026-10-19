# Stage-1 report: lem-trf-flat-lfp-cm-locus-fibre-dense

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flat-lfp-cm-locus-fibre-dense.json`: split statement, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-generic-cm-locus-field.json`: new unsplit statement, no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its Cohen–Macaulay terminology, and the imported blueprint tags; no sorry-free declaration states this item exactly.

## WANTED:

None. The local Stacks source contains Tag 045U and its field-algebra input Tag 00RG.

## Not duplicates

- `lem-trf-generic-cm-locus-field` vs `lem-sbc-fibre-cohen-macaulay-locus-open`: the new node is the dense-open theorem for a finite type algebra over a field (Tag 00RG), while the existing node proves openness for the fibre Cohen–Macaulay locus of a flat locally finitely presented scheme morphism.
- `lem-trf-generic-cm-locus-field` vs `lem-pur-cohen-macaulay-field-extension`: the new node gives density in one affine finite type fibre ring; the existing node gives invariance under arbitrary field extension and relative base change.

## What I checked and corrected

The imported item is the scheme-level assertion of Stacks Tag 045U, assertions (1) and (3): for flat locally finitely presented `f`, the fibre local ring is Cohen–Macaulay exactly on the relative locus, and that locus is dense in every fibre. I kept its statement and dependencies unchanged. The source proof reduces density to Tag 00RG on each affine fibre ring, so I created only the strictly smaller field-algebra statement `lem-trf-generic-cm-locus-field`; its statement is exactly Tag 00RG and its proof is intentionally left for a later worker.

Step 1 uses the affine-open basis and the fibre topology to place an affine chart inside an arbitrary nonempty fibre open. Step 2 uses the cited locally finite presentation affine-ring presentation and the cited affine base-change isomorphism to identify the chart in the fibre with a finite type residue-field algebra. Step 3 applies the new Tag 00RG node and identifies its prime localization with the fibre local ring through the same affine chart and the module-stalk definition; the depth and Krull-dimension clauses are the definitions cited in that step. I read every cited node statement, checked that each quote in `citations.json` is verbatim, and tested edge cases: an empty fibre is vacuous, a zero-dimensional fibre reduces to a field or Artinian finite type algebra, and a nonempty open in an affine chart meets a dense subset.

The Mathlib searches for both the item and the new node were run through `msearch.py` and logged in `searches.jsonl`: LeanFinder, Loogle, grep, and LeanSearch all found no Cohen–Macaulay density theorem. Existing DAG nodes were searched for Tags 045U, 00RG, and the relevant phrases; no duplicate of the new field-algebra statement was found.

## Review by Q22

I read the item source at `literature/stacks-project/more-morphisms.tex`, Tag 045U, and the field input at `literature/stacks-project/algebra.tex`, Tag 00RG. I checked each proof step against the statements it cites: Step 1 takes only the affine-basis and fibre-topology facts; Step 2 takes the finite-presentation affine chart and the affine fibre-product/base-change isomorphism; Step 3 takes the dense Cohen–Macaulay locus in the finite type residue-field algebra and the affine stalk/localization identification. The hypotheses flatness and local finite presentation are carried from the item into Step 2, and the nonempty-open and empty-fibre cases are handled explicitly. I corrected the imported empty proof by writing the three route steps, added the strictly smaller Tag 00RG node, filled blueprint ancestry and the split report, and generated verbatim citations for every use.

## What remains

The new field-algebra node is statement-only and joins the unsplit queue, as required for a stage-1 split.
