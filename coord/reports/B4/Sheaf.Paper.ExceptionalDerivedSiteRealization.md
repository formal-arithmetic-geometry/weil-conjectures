## What changed

Restored the published monolithic implementation and removed the unforced proof
module split from the returned delivery. The module keeps the published priority
5000 local instances for `strictEtaleSystemDerived` and `strictEtaleLevelDerived`.
It also drops two private imports that are transitively available and unused by
this implementation (`DerivabilityStructure.Derives` and `KInjectiveResolution`).
The single module compiles with all seven declarations unchanged and proved.

## Proved and sorry left

Closed 0 of 0 existing `sorry`s. No `sorry` remains and no new `sorry` was added.

## No longer needed

The returned split modules `ExceptionalDerivedSiteRealizationHelpers`,
`ExceptionalDerivedSiteRealizationInverse`, and `ExceptionalDerivedSiteRealizationRight`
are withdrawn. Their three implementation DAG nodes and
`coord/changes/exceptional-derived-site-realization-split.md` are withdrawn with
them. The two unused private imports listed above are pruned.

## Where the brief, the DAG or earlier work was wrong

The returned split was made against a stale base. The current published module
already contains the required priority 5000 local instances and compiles as one
file, so the split was not needed. The repair therefore retains the single
published module and only prunes imports that its proof does not use.

## New nodes

None.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalDerivedSiteRealization": "0785e98b702d5f8d2850c572faf02756dac2a9d6"}, "results": {"Sheaf.Paper.AdicPurityExceptionalReduction": {"hash": "ed41f2762ad5ee6d6249765fab3c9883d78ce218", "status": "OK"}, "Sheaf.Paper.FiniteExceptionalSiteNormalization": {"hash": "45a4008948aeb8b277eac484c15db3a7a001323f", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces": {"hash": "dfd7491b122f1402fa3e5e5f1ca4f2b05228ee34", "status": "OK"}}, "seconds": 113, "time": "2026-10-28T07:25:33+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
