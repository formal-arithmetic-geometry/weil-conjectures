## What changed

The item proof now reflects monomorphism along the forgetful functor from ringed-site modules to presheaves of modules. A new helper module states the underlying sectionwise injectivity theorem used by this reduction. The item retains its three public statement imports and adds the helper as a proof-only import.

## Proved and sorry left

The declaration `AlgebraicGeometry.Scheme.sfProperOpenCounit_mono` is proved by `Functor.mono_of_mono_map` from `sfProperOpenCounit_forget_mono`. One sorry remains in the new declaration `AlgebraicGeometry.Scheme.sfProperOpenCounit_forget_mono`, whose node is `lem-exc-proetale-proper-open-counit-mono-section`.

## No longer needed

The former proof-only imports for the detailed affine localization route are no longer needed by the reduction proof; that route is recorded as dependencies of the split-off sectionwise theorem. The item proof directly uses only the new helper.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan conflated sectionwise injectivity with the categorical monomorphism conclusion. The categorical conclusion is a short forgetful-functor reflection step, so the sectionwise argument is isolated as a strictly lower theorem.

## New nodes

`lem-exc-proetale-proper-open-counit-mono-section` records the underlying presheaf-module monomorphism and its sectionwise zero-extension proof route.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleProperOpenCounitMono": "12cf6ef54978f3efbaf1aec3d52b20c031d9dab7", "Sheaf.AlgebraicGeometry.ProEtaleProperOpenCounitMonoSection": "5c285cf217d7821ca53b393f3472a91a87b88d87"}, "results": {"Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison": {"hash": "09e7169473109df788dd91ac0f0bb5ea32e0cd7d", "status": "OK"}}, "seconds": 126, "time": "2026-10-28T12:15:03+0800", "transitive": 0, "version": 1}
```

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
