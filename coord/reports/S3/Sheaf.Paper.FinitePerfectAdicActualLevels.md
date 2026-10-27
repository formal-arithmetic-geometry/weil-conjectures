## What changed

The actual-level theorem now assembles its structure from three proof-only modules. The
level-object module supplies the family of descended complexes and its bounded/lisse
cohomology; the stalk module supplies the geometric Isom-sheaf stalk sections; and the
transition module supplies consecutive arrows with their universal normalization. The
top-level module imports these modules privately and packages their fields.

## Proved and sorry left

The original `finitePerfectAdic_actual_levels` hole is closed by a concrete structure
literal. Three strictly smaller obligations remain as named theorem holes:

- `finitePerfectAdic_actual_level_objects` in node
  `lem-weil-pbc-finite-perfect-adic-actual-level-objects`;
- `finitePerfectAdic_actual_level_stalk` in node
  `lem-weil-pbc-finite-perfect-adic-actual-level-stalk`;
- `finitePerfectAdic_actual_level_transitions` in node
  `lem-weil-pbc-finite-perfect-adic-actual-level-transitions`.

No definition contains a `sorry`.

## No longer needed

No imports or declared dependencies were removed. The top-level constructor uses all three
new nodes; the two original proof dependencies are retained by the split-off modules.

## Where the brief, the DAG or earlier work was wrong

The DAG presented finite quotient objects, geometric stalk sections, and normalized
transition arrows as one proof step. They are independent strictly smaller obligations;
the Lean proof now reflects that decomposition without changing the target statement or
the unit route.

## New nodes

`lem-weil-pbc-finite-perfect-adic-actual-level-objects` records finite-level descended
objects and bounded finite locally constant cohomology.

`lem-weil-pbc-finite-perfect-adic-actual-level-stalk` records the pointwise stalk
sections of the derived local Isom sheaf.

`lem-weil-pbc-finite-perfect-adic-actual-level-transitions` records the descended
consecutive arrows and their universal normalization property.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FinitePerfectAdicActualLevelObjects": "2d0f377e91be055a3bd0606a5856c6c5d18b1316", "Sheaf.Paper.FinitePerfectAdicActualLevelStalk": "e4e20dd8235c3a216a0389eef6194c50e62094b3", "Sheaf.Paper.FinitePerfectAdicActualLevelTransitions": "edc6f61ad344eca9100a0820ec813ae1133e7e95", "Sheaf.Paper.FinitePerfectAdicActualLevels": "1c3131a76896c3bbb141c94ecf5c492b4a8f2048"}, "results": {}, "time": "2026-10-28T04:15:39+0800", "transitive": 0, "version": 1}
```

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
