## What changed

The componentwise counit theorem is now proved from separate mono and epi
support statements, combined by `isIso_of_mono_of_epi`.  The item's
natural-transformation isomorphism proof names that completed counit result with
`have hc` before installing its `IsIso` instance.  No existing public statement
or definition was changed.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.sfProperOpenCounit_isIso` from the two
strictly simpler support halves and `AlgebraicGeometry.Scheme.sfProperOpenSheafComparison_isIso`
from componentwise isomorphism composition.  The delivery adds the named
theorem holes `sfProperOpenCounit_mono` and `sfProperOpenCounit_epi`, recorded by
nodes `lem-exc-proetale-proper-open-counit-mono` and
`lem-exc-proetale-proper-open-counit-epi`; these are the injectivity and
surjectivity halves of the affine support argument.

## No longer needed

No imports, nodes, or modules were removed.  The support imports are retained in
the two new modules because their split proof plans use the corresponding
localization and sheafification inputs.

## Where the brief, the DAG or earlier work was wrong

Nothing was found to be wrong.  The existing componentwise split is now
decomposed into its monomorphism and epimorphism parts, and the balanced
category lemma combines them without changing the target statement.

## New nodes

Added `lem-exc-proetale-proper-open-counit-mono` and
`lem-exc-proetale-proper-open-counit-epi`, the strict injectivity and
surjectivity subclaims used to prove the existing counit node.  Each has one
named theorem hole and a proof plan sourced from Tags 09AE and 09AG.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleProperOpenCounitEpi": "13dc16f657fea57d4d10a9b94d94596454859d66", "Sheaf.AlgebraicGeometry.ProEtaleProperOpenCounitMono": "d778b903f8b58d800b21c5b1765732b3b75881be", "Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison": "09e7169473109df788dd91ac0f0bb5ea32e0cd7d"}, "results": {}, "time": "2026-10-28T07:55:49+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
