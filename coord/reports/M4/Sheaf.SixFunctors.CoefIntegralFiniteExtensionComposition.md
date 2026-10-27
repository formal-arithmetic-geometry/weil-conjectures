## What changed

The composition proof is reduced along the two proof steps in the DAG. The item
module now imports two strict component modules and combines their conjunctions
with a real constructor. `comparison_composition_pure_tensor` states the two
unit equations and the associator pentagon. `comparison_composition_transpose`
states the u, v and beta composition equations. Both component proofs remain
explicit named stage-3 obligations with their own DAG nodes.

## Proved and sorry left

The original `comparison_composition` hole is closed by a real Lean proof that
combines the two strictly smaller component statements. Two sorries are added:

- `comparison_composition_pure_tensor`, node
  `lem-sf-integral-finite-extension-composition-pure-tensor`;
- `comparison_composition_transpose`, node
  `lem-sf-integral-finite-extension-composition-transpose`.

No definitions contain `sorry`.

## No longer needed

The item proof no longer directly depends on the six planned lower declarations
`lem-pur-compact-support-integral-coefficient-comparison`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-coef-finite-free-extension`, `lem-coef-finite-dualizing`,
`lem-coef-semilinear-derived-sections`, and the corresponding direct imports.
Those dependencies are represented by the two component obligations instead.
No existing module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original two prose steps each combine several independent conjunction
components. The prior split exposed the top-level composition component but left
those two steps as one unsatisfied theorem. This delivery records each proof
step as a strictly smaller statement and combines them without changing the
item signature.

## New nodes

`lem-sf-integral-finite-extension-composition-pure-tensor` records the pure
coefficient unit and associator component and is stated in
`lean/Sheaf/SixFunctors/CoefIntegralFiniteExtensionPureTensor.lean`.

`lem-sf-integral-finite-extension-composition-transpose` records the transposed
u, v and beta component and is stated in
`lean/Sheaf/SixFunctors/CoefIntegralFiniteExtensionTranspose.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionComposition": "11960a06ede80dd707dd823d1daed713e69bc7d3", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionPureTensor": "664f4d3f2c2becfabf25511ce707b9c8d784128b", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionTranspose": "80a3179ba2493867f976aa8d0c2809276ba76d00"}, "results": {}, "time": "2026-10-28T06:52:36+0800", "transitive": 0, "version": 1}
```

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
