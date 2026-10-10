Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-regular.json`: statement split into three proof steps; 0 Mathlib leaves.
- `dag/nodes/sec-curve-estimates/lem-sc-strict-henselization-cotangent-dimension.json`: one unsplit statement node; no Mathlib match.
- `citations.json`: verbatim quotes for every cited node use.

Attachments: none.

WANTED: none.

## Not duplicates

lem-sc-strict-henselization-cotangent-dimension vs lem-sc-strict-henselization-regular: the new node states only the base-change isomorphism and dimension equality for maximal-ideal cotangent spaces; the item states the regular-local-ring equivalence.
lem-sc-strict-henselization-cotangent-dimension vs lem-sc-strict-henselization-dvr: the new node concerns cotangent-space dimensions, whereas the existing node concerns the discrete-valuation-ring equivalence and the scheme-local-ring map.

The source declaration was checked by searching all of `WeilConjectures/` for the blueprint id, Tag 06LN, and strict-henselization regularity; no sorry-free declaration states this item. The source proof in Tag 06LN was read in `/home/ubuntu/c1-stacks-review/more-algebra.tex`, including its use of Noetherianity (06LJ), dimension invariance (06LK), and faithfully flat preservation of minimal generators (07QM). Existing DAG nodes for strict-henselization Noetherianity and dimension were reused. The cotangent-space invariance needed by the minimal-generator argument was not present in the DAG or blueprint, so it is the sole new node; its statement is strictly smaller than the item's regularity equivalence.

## Review by K1

I checked the item against Stacks Tag 06LN hypothesis by hypothesis: `R` is Noetherian and local, and the strict henselization is taken with respect to a separable closure of its residue field. Step 1 cites the existing Noetherianity equivalence and uses it only to make the regular-local criterion applicable to the strict henselization. Step 2 cites the existing equality of Krull dimensions. Step 3 cites the new cotangent-dimension statement and the existing Mathlib leaf characterizing a Noetherian local ring as regular exactly when cotangent dimension equals Krull dimension; the hypotheses for that leaf hold for both rings by Step 1. I read the statements of all four cited nodes and copied the portions used into `citations.json`.

For the new node, I checked the 06LN proof's minimal-generator argument and Tag 07QM parts (1)-(2): faithful flatness and extension of the maximal ideal identify the cotangent space after residue-field base change. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable, and no Mathlib declaration states strict-henselization cotangent invariance. Small cases checked were a field (both cotangent spaces zero) and a one-variable regular local ring, where both cotangent spaces have dimension one after separable residue-field extension. I corrected the new node's source path to the repository's standard `literature/stacks-project/more-algebra.tex` form and kept all imported statement/dependency fields unchanged.

What could not be finished: no Lean code is written at stage 1, and the new helper remains intentionally unsplit as required for a statement-only node.

## Second reading by K1

- Item statement: checked against Stacks Tag 06LN (`lemma-henselization-regular`), first and third conditions; the Noetherian local hypothesis, strict henselization over a separable residue-field closure, and regular-local equivalence agree.
- Step 1: checked against the statement of `lem-sc-strict-henselization-noetherian` and Tag 06LN via 06LJ; it supplies exactly Noetherianity for both local rings.
- Step 2: checked against the statement of `lem-sc-strict-henselization-dimension` and Tag 06LK; it supplies exactly equality of the two Krull dimensions.
- Step 3: checked against the statements of the cotangent-dimension helper and `lem-weil-pbc-regular-local-cotangent-dimension`; the hypotheses are available from Step 1, and the equalities used are exactly those stated.
- New node `lem-sc-strict-henselization-cotangent-dimension`: checked against the minimal-generator argument in Tag 06LN and the faithfully-flat henselization properties in Tag 07QM; the base-change isomorphism and dimension consequence are a valid strictly smaller intermediate fact.
- New node form: statement-only, self-contained, TeX escaped, definition dependencies cited, source tag recorded, and Mathlib searches recorded with unavailable LeanSearch marked unavailable.
- Small cases: fields give zero cotangent spaces; a one-variable regular local ring gives dimension one on both sides; no edge-case contradiction found.
- Changes: no node or proof changes were necessary after the source and dependency audit; this second-reading section was appended as required.
