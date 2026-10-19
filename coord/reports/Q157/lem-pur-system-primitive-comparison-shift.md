Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-system-primitive-comparison-shift.json`: statement, split proof, no new nodes, no Mathlib leaf.
- `citations.json`: 13 verbatim step citations.

Attachments:

- No sorry-free Lean declaration matched the item; the source checkout contains no declaration tagged `(blueprint: lem-pur-system-primitive-comparison-shift)`.

WANTED:

- None.

What was checked and corrected:

- The imported statement was read against `dag/nodes/sec-six-functors/lem-sf-integral-compactification-system-realization.json`, `lem-sf-semilinear-proper-open-mate-pasting.json`, `lem-pur-integral-basic-operation-shift.json`, `lem-pur-shifted-tensor-morphism-calculus.json`, and `lem-sf-open-tensor-normalization.json`; it is unchanged and its hypotheses match those nodes.
- Step 1 uses only the realization node’s simultaneous ringed-diagram models and the basic-operation shift node’s termwise/K-injective/K-flat shift comparisons.
- Step 2 uses the realization node’s flat-term system resolution maps and the signed tensor node’s `(-1)^(bp)` comparison; the shifted pullback/tensor square is checked on each pure bidegree.
- Step 3 checks the associator, unitors, and Koszul symmetry by the explicit signed tensor calculus. The two symmetry exponents differ by `2bp`, so the stated `(-1)^(ab)` factor is correct for all integer shifts.
- Step 4 reads the exact termwise extension-by-zero normalization and verifies that reindexing leaves its component maps unchanged.
- Step 5 checks the normalized `P_b J_k ≅ J_s` map using the open-unit adjunct description and the realization node’s intrinsic system comparison.
- Step 6 checks the clopen decomposition: `J_s` and `S_s` agree componentwise, while `π_s` is identity on the selected component and zero on the complement; both are preserved by shifts. The proper/open node was read to verify these are system maps before evaluation.
- Step 7 explicitly preserves the before-evaluation status and excludes integral realization, arbitrary expression-tree, mate, projection, and exchange claims beyond the statement.
- Mathlib searches were rerun with `msearch.py` for LeanFinder, Loogle, grep, and LeanSearch under the item id. They found only generic shift/pseudofunctor declarations, so the item is not a Mathlib leaf.

What could not be finished:

- Nothing in the split itself remains; the required server dry run is the next validation step.

## Review by Q157

I checked the item source and every cited node listed above. Each proof step names the exact statement it uses: realization supplies the simultaneous ringed-diagram operations and before-evaluation maps; basic-operation shift supplies operation comparisons; signed tensor calculus supplies the Koszul comparison, associator, and symmetry identities; open normalization supplies the adjunct-normalized extension maps; and semilinear proper/open pasting supplies the intrinsic clopen maps. I verified the separated finite-type/open hypotheses are inherited from the item and that no step uses faithfulness of evaluation. The only correction was replacing the initially hand-written citation snippets with valid JSON and quotes copied from the current node statements.
