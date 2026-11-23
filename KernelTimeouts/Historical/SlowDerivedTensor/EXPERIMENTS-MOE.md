# MOE validation: Slow Derived Tensor

## Provenance

This validation uses the historical source at `bdab171985a`, Lean 4.33.1
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The current control source is
`428569e1ce1` (`@[reducible] def`). Imported declarations are reported at the
finalized environment boundary; S2/S3 pre-finalization data requires a source
probe beside the declaration.

## Snapshot

The probe `/tmp/moe_slow.lean` imported the historical tensor module and ran
`#moe_root AlgebraicGeometry.test_tensorObj_kernelProbe`, followed by
`#moe_decl` for `CategoryTheory.MonoidalCategoryStruct.tensorObj` and
`CategoryTheory.DerivedMonoidal`. The root replay returned:

```text
MOE_KERNEL stage=S5 result=true
```

The S4 trees preserve the complete stored type and checked value type. The
whole theorem comparison first differs at:

```text
root/body/body/body/body/body/body/body/body/body/body/body/body/arg/fn/fn/fn/fn/fn
kind=structural-hash
left=684061942 right=3524748218
```

Following the existing R2 path to the M0 conversion identifies that node as
the second argument of the shared `CategoryTheory.MonoidalCategoryStruct.tensorObj`
head. The exact M0 pair is `tensorObj` versus `tensorObj`, with
`inferInstance` provider arguments of sizes 1,785 and 11,973. The stored
metadata reports `tensorObj` as `abbrev` and `DerivedMonoidal` as
`regular:2`, matching the case record. The historical forward/reverse root
measurements are 49,867/50,279 ms; the reducible-definition control removes
the minute-scale consumer conversion.

The S0/S1 syntax command and the S2 elaboration command were also compiled
against the same MOE module; imported historical declarations remain marked
`source-required`/`pre-finalization-required` in the snapshot as specified by
the contract.

This is an origin record, not a claim that the structural hash itself is a
semantic identity. Paths, node kinds, payloads, and constant hints are the
authoritative fields.

## Audit note and Batch 2 boundary test

The imported consumer has no captured pre-finalization S2 value. Its exact
provider split is supported at S4/S5 (the shared `tensorObj` head, argument 2),
not at an earlier snapshot. The `abbrev` versus `@[reducible] def` change is
source-authored declaration metadata: the fresh A0/A2 controls report the
same 46--52 s tensor argument conversion, while the full consumer conversion
changes from 119,953/127,832 ms to 2/2 ms. This does not demonstrate an
Elaborator-selected difference or a same-Expr metadata-only F2 replay.

E3 puncture: the type-correct A0 `abbrev` spelling re-exposes the body of the
fast A2 regular-definition boundary in the same consumer. Both variants
compile; the fresh round-two measurements above show the expensive full
consumer conversion returns. The separate A3 body-exposure row is a historical
note and was not re-measured. Boundary status: fragile under changing the
declaration kind. No S2/S4 finalization comparison is available for the
imported consumer.
