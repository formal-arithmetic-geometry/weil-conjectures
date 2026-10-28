## What changed

The statement of `derived_source_shift_square` is unchanged. Its proof now applies
`derived_source_shift_descent` to `derived_source_shift_model` through two private proof
imports. The descent argument uses naturality and K-injective representatives of the target.
The representative argument chooses the uniquely normalized source chain shifts, cancels the
explicit input and output model isomorphisms, rewrites the two separate normalization equations,
and uses the proved `source_chain_square`.

New modules provide the two explicit model isomorphisms, the proved degreewise signed chain
square, the proved representative combination, the proved descent, and the two remaining
one-route normalization statements. These normal forms are distinct steps of the assigned
blueprint Step 4, rather than another copy of the square: each calculates one composite and
neither compares it with the other composite. The chain equality and descent are completely
proved here. No existing definition, statement, instance, attribute, or public import changes.
No other existing module is adapted.

Validation: `lcompile.py --all` compiled all seven files cleanly in import order.
The final noncached checks took 18.9 seconds for the chain square, 10.6 seconds
for the representative combination, and 5.4 seconds for the original item.
All profiling and trace options have been removed.

## Proved and sorry left

This is a decomposition, not a completed proof of the original obligation. The original module
had one hole, `WeilConjectures.PodReindexingCoherence.derived_source_shift_square`; its body now
contains a complete Lean proof from the two normalization lemmas. Two holes are added, for a
net increase of one hole across the delivered Lean files. No net closure progress is claimed.
There are zero holes in the item module.

The following new theorems have complete proofs:

- `WeilConjectures.PodReindexingCoherence.source_chain_square`
  (`lem-pod-reindexing-source-chain-square`). The proof cancels the two chain-shift
  isomorphisms, projects to every Hom degree, and evaluates local sections twice. The
  `LeftFormula` hypotheses give identical signs and `chain_projection` gives equality.
- `WeilConjectures.PodReindexingCoherence.derived_source_shift_model`
  (`lem-pod-reindexing-source-shift-model`), from the two normal forms and the chain square.
- `WeilConjectures.PodReindexingCoherence.derived_source_shift_descent`
  (`lem-pod-reindexing-source-shift-descent`), by essential surjectivity on source complexes
  and naturality along an isomorphism to a K-injective target representative.

The only holes in this delivery are:

- `WeilConjectures.PodReindexingCoherence.source_left_normalization`
  (`lem-pod-reindexing-source-left-normalization`), which computes the comparison followed by
  the target-site inverse source shift. Its remaining proof uses `Comparison.derived_model`,
  target-site `LeftNormalization`, and the localization-factor shift square.
- `WeilConjectures.PodReindexingCoherence.source_right_normalization`
  (`lem-pod-reindexing-source-right-normalization`), which computes source-site inverse source
  shift followed by the shifted comparison. Its remaining proof uses source-site
  `LeftNormalization`, `Comparison.derived_model`, and naturality of localization factors.

Both are public named theorems with proof exactly `by sorry`, individual modules, source
citations, detailed proof docstrings, and DAG nodes. The model isomorphisms are explicit
composites of existing isomorphisms, with no data chosen from an existence theorem. The
normalized chain shifts are selected from a uniqueness statement that determines their maps.

## No longer needed

No original import is removed; the original public coherence-data import is still needed.
No existing node or module is claimed pruned. The original coherence-data and exact-restriction
normalization dependencies remain needed through the new nodes. The full double-shift chain
square is not imported: the source-only calculation here works for arbitrary isomorphisms
satisfying `LeftFormula`. Its existing module and declarations are preserved. No unit statement
or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or assigned repair was found. The row is an ordinary proof item, with one
original hole. The plan's representative normalization step requires two substantive equations
through the fixed Hom models; the chain comparison alone does not prove the derived square.
This delivery makes that separation explicit, proves the signed chain comparison and the
localization descent, and records each remaining normalization route independently.

Searches for a direct existing result found general localization shift tools, the recorded
`LeftNormalization`, the double-shift chain square, and the slice-restriction analogue. None
already states either specialized normal form. The source-library boundary is respected.

The normal forms retain both source and target localization-shift isomorphisms, so
zero shift requires no strict equality of shifted objects. Zero complexes and the
empty site introduce no excluded case: the constructions remain isomorphisms and
the chain proof uses all Hom projections. Scalar evaluation uses integer units,
so the sign identities also apply in residue characteristic two.

## New nodes

`def-pod-reindexing-source-model-factors` records `sourceModelInput` and `sourceModelOutput` in
`Sheaf.Paper.PodReindexingSourceModelFactors`. Both constructions are explicit compositions.

`lem-pod-reindexing-source-chain-square` records the proved sectionwise signed source-shift
calculation in `Sheaf.Paper.PodReindexingSourceChainSquare`.

`lem-pod-reindexing-source-left-normalization` records the target-site route calculation in
`Sheaf.Paper.PodReindexingSourceLeftNormalization`, with its remaining proof in words.

`lem-pod-reindexing-source-right-normalization` records the source-site route calculation in
`Sheaf.Paper.PodReindexingSourceRightNormalization`, with its remaining proof in words.

`lem-pod-reindexing-source-shift-model` records the proved combination of those two calculations
and the chain square in `Sheaf.Paper.PodReindexingDerivedSourceShiftModel`.

`lem-pod-reindexing-source-shift-descent` records the proved naturality descent in
`Sheaf.Paper.PodReindexingDerivedSourceShiftDescent`.

Only the proof, proof dependencies, and proof origin of the original item node are changed.
All six new nodes retain the item's chapter and unit and cite the same blueprint Step 4.
There is no change record because no existing interface or other existing module changes.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingDerivedSourceShift": "55e081a4806cb703b7da3a5ff49299405a1d8505", "Sheaf.Paper.PodReindexingDerivedSourceShiftDescent": "c90544f2d805a1de508441e04ca328da698d8cae", "Sheaf.Paper.PodReindexingDerivedSourceShiftModel": "56106e7b2b8a800d2e55fcd9e35026b6c315017f", "Sheaf.Paper.PodReindexingSourceChainSquare": "bc8c898f8f0a84c70d3c020fc74e712f3a742788", "Sheaf.Paper.PodReindexingSourceLeftNormalization": "5db7c9dfdb51dfbab5cfa54c30d27a417873e40b", "Sheaf.Paper.PodReindexingSourceModelFactors": "1e0d0943d3bbef813de279a355239a21f922c982", "Sheaf.Paper.PodReindexingSourceRightNormalization": "b08e46913ddb75693152e912923dccf5573cb80b"}, "results": {}, "time": "2026-10-28T12:36:10+0800", "transitive": 0, "version": 1}
```

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
