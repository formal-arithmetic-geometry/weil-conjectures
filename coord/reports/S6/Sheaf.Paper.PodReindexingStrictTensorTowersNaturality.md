## What changed

Repair `WeilConjectures.podReindexingStrictTensorTowersNaturality` by requiring the
existing `PodCompletionReindex.QuotientGenerators` normalization. The structure
alone only supplies objectwise quotient isomorphisms. The sole caller,
`PodReindexingStrictTensorTowers`, already has the full laws and passes this conjunct;
its signature and conclusion stay unchanged. The change record is
`coord/changes/S6-strict-tensor-naturality-normalization.md`.

The proof precomposes with the inverse tensor comparison and uses finite tensor
extensionality on reduced original-section generators. Normalization at scalar one
computes the comparison on these generators. The existing tensor-map and
reduction-map formulas compute the two composites, and sectionwise reindexing
identifies the resulting sections. No additional statement is split off.

## Proved and sorry left

The corrected `WeilConjectures.podReindexingStrictTensorTowersNaturality` is proved
in full. The one original `sorry` body is replaced by the proof of the repaired
statement. Remaining holes: zero. New holes: zero. Split-off statements: zero. The earlier,
unrestricted statement is not claimed proved: its missing hypothesis is repaired.
The parent theorem remains proved with its original statement. The cleaned item
and adapted caller compile without warnings in 30.4 seconds and 7.1 seconds,
respectively, in one import-ordered lcompile run. The axiom audit of each of the
three reused tensor helpers is exactly `propext`, `Classical.choice`, `Quot.sound`.
The main declaration still reports `sorryAx` through its pre-existing statement
models: `PodCompletionReindex`, `QuotientGenerators`, and `podGoodReindex` already
report it independently. No additional proof hole is introduced by this delivery.

## No longer needed

The planned dependency `lem-pod-reindexing-hom-resolution-model`
(`Sheaf.Paper.PodReindexingHomResolutionModel`) is not used. Naturality of these
strict towers requires no Hom resolution or derived-limit argument. Its import was
not present in the item and is not added. The tensor extensionality and map formulas
are reused from `IntegralScalarTensorLevelReduction` and
`IntegralScalarTensorLevelTower`; their proofs use the existing integral tensor
construction. The independent direct import of `IntegralScalarTensorLevelReduction`
is unnecessary because `import all IntegralScalarTensorLevelTower` exposes the
proved helper it already imports. No library module is withdrawn, and no
source-library declaration is removed. No original public import is removed. The original planned
`lem-pur-integral-operations-well-defined` dependency remains needed through the
reused helpers and is not claimed pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the previous signature assumed no normalization or naturality
of `D.quotient`, even though its proof invoked naturality of those maps. For
identity reindexing in odd residue characteristic, choose a sign depending on the
good representative and multiply its quotient comparison by that sign at every
level. Multiply the tensor comparison by the product of the two signs. The stated
generator formula and tower isomorphism remain valid, but a nonzero inclusion
between representatives with different signs violates naturality. The source and
parent use the fixed normalized comparison, so the repair adds only its existing
generator-normalization law. The parent DAG citer still holds, as recorded in the
statement-change audit. The unit route and all target statements are unchanged.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingStrictTensorTowers": "ad5531dafeb363e1828a5771d96868dca7a11bc0", "Sheaf.Paper.PodReindexingStrictTensorTowersNaturality": "33a3da89310a013c68fcf9e3d16d39fa27c1d9d2"}, "results": {}, "time": "2026-10-28T11:05:49+0800", "transitive": 0, "version": 1}
```

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
