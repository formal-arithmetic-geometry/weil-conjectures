# RealPurity: exact Kernel site

**Declaration:** `IsReal.exists_isPunctuallyPureOfWeight_cokernel_detWeight`,
origin `e2d8b540cba`.

## Measurements and bisect

The type-only probe is 4.70 s. The historical Before is a Kernel
deterministic timeout at 58.94 s / 5,590,352 KB; Kernel skipped is about
7.4 s. Replacing the entire `hσ` constituent witness with `sorry` still
times out (59.54 s), while a prefix through `hσ` and before later consumers
takes 6.90 s. Replacing only the body of `hreal'` makes the file 7.10 s.
Keeping the two rewrites in `hreal'` and replacing only `exact h` gives the
same cheap result; keeping `exact h` and replacing later purity work still
times out at 58.94 s. This isolates the final equality conversion in `hreal'`.

## Exact expressions

The compact state probe prints:

```text
h : starRingEnd Complex (ι (P.obj.ρ (W.frobenius x)).charpoly.reverse.coeff n)
      = ι (P.obj.ρ (W.frobenius x)).charpoly.reverse.coeff n
goal : starRingEnd Complex (ι (P.obj.ρ (W.frobenius x)).charpoly.reverse.coeff n)
      = ι (P.obj.ρ (W.frobenius x)).charpoly.reverse.coeff n
```

The compact printer shows the same proposition on both sides. The full
`pp.explicit` trace is retained by `probes/PrintHRealCompact.lean`'s companion
run with `set_option pp.explicit true`; it expands the `PadicAlgCl`,
representation, and finite-dimensional instance arguments but has not yet
isolated a smallest unequal subexpression. The measured operation is the
final `exact h` conversion after the equivalence `f` rewrites the sheaf-stalk
polynomial. The typed placeholder controls show that the large constituent
equivalence itself is cheap.

Kernel diagnostics on the isolated `hreal'` probe show only small local
unfold counts (maximum 8), while the full conversion times out; this is a
context-sensitive proof-term/type reconciliation rather than a recursive
computation. The current `Master.lean` form passes in 6.10 s, so the
historical split is insufficient on 4.35.0.

## Classification

Primary mechanism: **unclassified**. Candidate mechanisms: B, C, and E.
Evidence: **confirmed** for the exact `hreal'` conversion, **plausible** for
the candidate mechanisms. The controlled bisect does not distinguish a
proof-abstraction mismatch from a representation-instance mismatch. The
historical After still times out; later master changes are not attributed to
the historical fix.
