## What changed

The scalar model construction is assembled from two named intermediate interfaces: an
ambient realization isomorphism and its coherent quotient normalization. The item theorem
now packages these fields into `IntegralComparisonScalarModel`. The realization and
normalization interfaces remain explicit split-off obligations for follow-up workers.

## Proved and sorry left

`WeilConjectures.ambientQuotientScalarModel_exists` is proved by constructing the two
structure fields from the split interfaces. The following strictly smaller named theorems
remain sorry:

- `WeilConjectures.ambientQuotientScalarModel_realization_exists`
- `WeilConjectures.ambientQuotientScalarModel_normalization_exists`

## No longer needed

The original proof plan's direct dependencies are represented by the two split interfaces;
the item module itself imports only `IntegralComparisonRealizationModels` and the two sibling
interfaces. No additional imports or DAG dependencies were needed for the assembly.

## Where the brief, the DAG or earlier work was wrong

The existing item proof text bundled construction of the realization and verification of its
normalization into one unresolved theorem. These are independent fields of the target
structure, so the proof is reduced to two strictly smaller named statements and a real
constructor proof.

## New nodes

- `new-trf-ambient-quotient-scalar-realization`
- `new-trf-ambient-quotient-scalar-normalization`

## Second reading by A9

The assembly and all three modules were compiled together in import order. The parent
constructor uses the realization witness directly and applies the normalization theorem to
that exact witness.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AmbientQuotientScalarModelExistence": "4f34f088cc3f6b763100078a9033d1a3fae565f8", "Sheaf.Paper.AmbientQuotientScalarNormalizationExistence": "f111f01387c6d3622e5896bd89bacb82be2b9051", "Sheaf.Paper.AmbientQuotientScalarRealizationExistence": "a8e7dce0154e9cabf8d7e8485dd2e56f9fe352ab"}, "results": {}, "time": "2026-10-28T03:30:38+0800", "transitive": 0, "version": 1}
```
