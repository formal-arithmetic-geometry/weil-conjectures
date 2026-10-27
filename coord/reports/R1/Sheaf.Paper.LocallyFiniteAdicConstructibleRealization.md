## What changed

Repaired the returned delivery cfc8799cbae inside the item module. Replaced its
removed public `WeilConjectures.WeilSheaf.LowerShriek` import with the narrower
public `WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion` import. This
reexports the existing `AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriek`
and `AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekAdjunction` declarations
used by `Sheaf.Paper.LocallyFiniteAdicCompactSupportData`. The importer itself is
unchanged. The returned commit did not include this public import; a later local
attempt had compiled the item but had no confirmed delivery result.

Withdrew the previous, unlanded decomposition and restored the original existence
theorem and its docstring verbatim from current main. The two unlanded draft node
files are archived under the sandbox scratchpad, outside the delivery DAG. The import change is recorded in
`coord/changes/R1-locally-finite-adic-open-immersion-reexport.md`. This
packet changes no existing theorem signatures, definitions, instances, attributes,
or target statements, and contains no copy of a landed theorem.

Validation: `lcompile.py` compiled the repaired item and the unchanged importer
in import order: 29.6 s and 51.1 s respectively, exit 0, no compiler warnings.
Importer source git blob: `228607968cbf697875a27c3beb2d872c5ea196c3`. The
unchanged test copy was removed from the delivery packet after this check.

## Proved and sorry left

This is the assigned import repair: zero holes closed and zero holes added
relative to main. The original one hole remains:
`WeilConjectures.LocallyFiniteAdicRealization.locally_finite_adic_constructible_realization`,
node `lem-sf-locally-finite-adic-constructible-realization`.
The proposed `realizationCore_exists` and `commonField_exists` declarations from
the returned packet are not delivered. No proof progress is claimed.

## No longer needed

Removed direct imports `WeilConjectures.WeilSheaf.LowerShriek`,
`Sheaf.Paper.ContinuousRationalDerivedRealization`, and
`Sheaf.Paper.RationalRealizationScalarCoherence`. The required open-immersion API
is explicitly reexported from its owning module instead. No existing DAG nodes,
modules, proof dependencies, or unit steps are pruned: the original theorem and
its proof plan remain open.

## Where the brief, the DAG or earlier work was wrong

The previous packet removed an exported prerequisite needed by the compact-support
importer. The unknown `actual` errors follow from failure to elaborate its
`adicOpenImmersionLowerShriek`-dependent definitions. The public import repairs
that prerequisite without adapting the importer.

The previous split's assertion `commonField_exists (R : RealizationCore l X)` is
not justified: a core permits independent choices of its integral natural
isomorphisms at each finite field, whereas `commonField` prescribes their relative
normalization. Changing one comparison by a scalar automorphism preserves the
core fields but can change the transition equation. Thus the earlier claim that
the split was universally true was wrong. Both unlanded helper declarations are
withdrawn; the original, correctly stated existence obligation is retained.

## Related modules compiled before delivery

7 related module(s) compiled against this delivery by deliver3.py: 7 OK.

```json
{"capped": false, "direct": 7, "left_out": 0, "own": {"Sheaf.Paper.LocallyFiniteAdicConstructibleRealization": "d3a4d2d7c6354238c765878efefe637a4ddcf85d"}, "results": {"Sheaf.Paper.LocallyFiniteAdicCompactSupportData": {"hash": "228607968cbf697875a27c3beb2d872c5ea196c3", "status": "OK"}, "Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization": {"hash": "b1222b33661731a5f010777a9242825042cdc6f7", "status": "OK"}, "Sheaf.Paper.NativeAdicRealizationData": {"hash": "1c5841337f21707909a7b99a78611e0d05711743", "status": "OK"}, "Sheaf.Paper.NativeCoefficientInverseImage": {"hash": "01bdc6764a3636f469e3c9e7eaf9d66b9e5327ac", "status": "OK"}, "Sheaf.Paper.NativeGeometricBrownConstructibleComparison": {"hash": "90eb752eec7082b347f81fcc85fa44a9ccc197e7", "status": "OK"}, "Sheaf.Paper.NativeWeilLocalizingBrownAdjoints": {"hash": "1c4987d09f9c6a74550dd8ae52e1615d212aaaac", "status": "OK"}, "Sheaf.Paper.SfAdicCommonStageDescentEquivalence": {"hash": "3cef5ea1f2ac78bc6ac6380937ca9dc32b367198", "status": "OK"}}, "seconds": 81, "time": "2026-10-28T02:09:43+0800", "transitive": 0, "version": 1}
```

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
