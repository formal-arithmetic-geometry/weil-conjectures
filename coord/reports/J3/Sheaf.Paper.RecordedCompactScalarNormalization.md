## What changed

Proved `AlgebraicGeometry.ProEtale.CoefficientCompatibility.recordedCompactScalar_fixed_normalization` without changing its statement. The proof applies the faithful realization functor, expands the recorded support presentation, pastes its proper and open scalar comparison squares using naturality, and cancels the presentation isomorphisms.

Added two proved factor modules: `Sheaf.Paper.RecordedOpenScalarNormalization` and `Sheaf.Paper.RecordedProperScalarNormalization`. Their imports in the item are private proof imports. The open factor uses the existing scalar-unit and open-counit normalizations. The proper factor identifies the ring-sheaf and sectionwise direct-image models, transports the derived-unit normalizations, and transposes the resulting scalar-restriction cube. The derived restriction cube is isolated in the proved module `Sheaf.Paper.RecordedRestrictionNormalization`; the other new helpers are private and proved. All existing public imports and declaration signatures are preserved.

Updated the item's proof route and added nodes for the two proved factor statements and their proved scalar-restriction cube. No existing public definition, instance, attribute or other module is changed.

Validation: `lcompile.py --all` compiles all four delivered modules in import order with no errors or warnings. The uncached successful checks for the restriction cube, proper factor and assigned module took 44.5 s, 56.3 s and 50.1 s respectively, below the unchanged 60 s limit. All diagnostic options were removed. Exact source comparison confirms the assigned theorem statement and its original public imports are unchanged; all node declaration records match their Lean statements.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.ProEtale.CoefficientCompatibility.recordedCompactScalar_fixed_normalization`. Also proved `AlgebraicGeometry.ProEtale.CoefficientCompatibility.recordedOpenScalar_fixed_normalization` and `AlgebraicGeometry.ProEtale.CoefficientCompatibility.recordedProperScalar_fixed_normalization` in the two factor modules. Also proved `AlgebraicGeometry.ProEtale.CoefficientCompatibility.recordedRestriction_directImage_cube` in the new restriction-cube module.

Holes closed: 1 of 1 in the assigned module. Holes added: 0. Split-off unproved statements: 0. There are no remaining `sorry` declarations in any delivered Lean file. The proof uses the already stated dependency theorems, including their existing unfinished proofs; it does not claim to discharge those dependencies.

## No longer needed

No existing import or module is withdrawn. The planned direct application of `lem-weil-pbc-mate-pasting` is unnecessary for the final pasting: the proved private helper `paste_scalar_factors` uses functoriality and naturality. That node is a Mathlib leaf, so this removes no project module. The other original dependencies remain needed through the statement's definitions or the proved factors. The unit's realized statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The existing finite realization scalar-mate theorem concerns the sectionwise intrinsic direct-image model, whereas `directImagePresentation` uses the ring-sheaf direct-image model. Reusing that theorem directly would skip a normalization comparison. The proper-factor proof establishes this comparison from the prescribed unit equations and proves the corresponding derived restriction cube. No statement is disputed or weakened.

## New nodes

`lem-sp-recorded-open-scalar-fixed-normalization`, in `dag/nodes/sec-smooth-purity/lem-sp-recorded-open-scalar-fixed-normalization.json`, records the proved open-factor realization square. It has no proper image or compactification, and is strictly a factor of the assigned comparison. Its module is `Sheaf.Paper.RecordedOpenScalarNormalization`.

`lem-sp-recorded-proper-scalar-fixed-normalization`, in `dag/nodes/sec-smooth-purity/lem-sp-recorded-proper-scalar-fixed-normalization.json`, records the proved geometric direct-image factor for every scheme morphism. It has no open extension or support functor. Its module is `Sheaf.Paper.RecordedProperScalarNormalization`. Both factors and the restriction cube apply to arbitrary unbounded inputs; the adjunction arguments also cover identity maps, empty schemes, and zero coefficient rings. No change records are needed because only the assigned module and new modules and nodes are changed.

`lem-sp-recorded-restriction-direct-image-normalization`, in `dag/nodes/sec-smooth-purity/lem-sp-recorded-restriction-direct-image-normalization.json`, records the proved scalar-restriction cube for the recorded direct-image presentation. Its module is `Sheaf.Paper.RecordedRestrictionNormalization`. It is a face of the proper-factor argument and contains no scalar-extension mate. After profiling the combined proof and trying to reduce unnecessary unfolding, this self-contained cube was isolated to keep each file within the unchanged compile-time limit.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RecordedCompactScalarNormalization": "ea5d32b9902a6cb7648bb243b4371fb4787b510b", "Sheaf.Paper.RecordedOpenScalarNormalization": "6ddad06def58cc249379fe7191d9426ad2f0d924", "Sheaf.Paper.RecordedProperScalarNormalization": "eafc72eb98cecc751c8d1397d46ab3034b90fd95", "Sheaf.Paper.RecordedRestrictionNormalization": "a00c16f285ff92eea45eecd44df62b834f36db62"}, "results": {"Sheaf.Paper.EtaleProEtaleCompactScalarSquare": {"hash": "aa24f74cc8866eba00c4cfba205c13db3d2356fc", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T01:33:40+0800", "transitive": 0, "version": 1}
```

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
