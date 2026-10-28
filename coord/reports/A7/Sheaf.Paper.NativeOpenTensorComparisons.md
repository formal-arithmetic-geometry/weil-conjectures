## What changed

Proved `native_open_tensor_comparisons` by constructing the restriction and
projection isomorphisms separately. The proof totalizes the normalized sheaf
comparisons, compares both sides on K-flat complexes, and descends the resulting
natural isomorphisms along the product localization.

Eight new proved helper modules isolate the acyclic-test K-flat comparison,
natural tensor models, cochain comparisons, restriction descent, and projection
descent. Existing statement signatures and definitions are unchanged. All new
imports in the assigned module are proof imports. All nine delivered Lean files
have compiled, one at a time in import order; the slowest successful check took
55.7 seconds. Profiling options and diagnostic files were removed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_open_tensor_comparisons`.

No new holes or split-off `sorry` declarations. Also proved, in the same
namespace:

- `native_tensor_acyclic_test_kflat`;
- `native_tensor_model_comparison`;
- `native_open_tensor_sheaf_comparisons`;
- `native_open_tensor_chain_restriction`;
- `native_open_tensor_chain_projection`;
- `native_open_tensor_chains`;
- `native_open_tensor_restriction_comparison`;
- `native_open_tensor_projection_comparison`.

The original module and all new modules contain zero `sorry` occurrences.

## No longer needed

None. The original module had no declared proof dependencies to prune; its public
import and statement dependencies are retained. No existing module is withdrawn.
The proof uses the existing natural sheaf projection theorem; its proof remains
a separate project obligation.

## Where the brief, the DAG or earlier work was wrong

The available native K-flat localization theorem uses `NativeTensorKFlat`, the
acyclic-test predicate with the right parameter first. The supplied preservation
fields and derived tensor models use `NativeIsKFlat`, the two-sided
quasi-isomorphism predicate for left-first totals. These are not definitionally
the same predicate. The proof supplies the needed implication using the ringed
presentation, symmetry, and mapping cones.

The sheaf restriction field is a pointwise family of isomorphisms. Its
normalization, together with the inverse-mates formula for `nativeTensorMap`,
is used to prove naturality before applying the total-complex comparison API.

## New nodes

`new-sf-native-tensor-acyclic-test-comparison`: the implication from the native
acyclic-test K-flat condition to both quasi-isomorphism preservation tests.

`new-sf-native-tensor-model-comparison`: natural tensor model isomorphisms for
two families of native K-flat complexes.

`new-sf-native-open-tensor-chains`: restriction and projection comparisons on
unbounded cochain complexes, before localization.

`new-sf-native-open-tensor-restriction-descent`: descent of the restriction
comparison to the native derived categories.

`new-sf-native-open-tensor-projection-descent`: descent of the projection
comparison to the native derived categories.

`new-sf-native-open-tensor-sheaf-comparisons` records naturality of the
normalized restriction isomorphism and the native sheaf projection comparison.

`new-sf-native-open-tensor-chain-restriction` records its restriction
totalization in a separate module to keep compilation within the file limit.

`new-sf-native-open-tensor-chain-projection` records the independent projection
totalization. These two proved statements are combined by the chain node.

All eight nodes are proved in this delivery. The original node's proof records
its use of the two descent theorems. No change records are needed: the only
existing module changed is the assigned module, and its statement and public
imports are preserved.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeOpenTensorChainProjection": "6a51cea6819dc4b65ad6951dd7c36fa56faa5e3e", "Sheaf.Paper.NativeOpenTensorChainRestriction": "27ccd8d4de8e7ae4e318fe7411fb888d95700371", "Sheaf.Paper.NativeOpenTensorChains": "06862436f268850081e691784f308646abbe42f8", "Sheaf.Paper.NativeOpenTensorComparisons": "0934b2b7277f884b9897a70b9039b8322115a0e8", "Sheaf.Paper.NativeOpenTensorProjectionDescent": "40c1c4451ba6523763838ca5cf49df4bf0d403fb", "Sheaf.Paper.NativeOpenTensorRestrictionDescent": "21d25495f5d08262b6ded1f9c03fed7684de4538", "Sheaf.Paper.NativeOpenTensorSheafComparisons": "6469f6ba5a46dfae44d1a70e1c974c825cdee36d", "Sheaf.Paper.NativeTensorAcyclicTestComparison": "34f4e23d3165a1d843b4b7344756798faafff23f", "Sheaf.Paper.NativeTensorModelComparison": "60e9b1c6d3cd135708e9540703d93885732f3fcc"}, "results": {}, "time": "2026-10-28T14:50:04+0800", "transitive": 0, "version": 1}
```

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
