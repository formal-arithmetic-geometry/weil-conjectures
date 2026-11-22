# Mismatch Provenance and Recursive Workload Report

Case: PR1627-WeilSheafTransport
Lean / mathlib: Lean 4.35.0, source snapshot 1ef1fddac73; earlier IM/AD
measurements with READY2-4.35.0.
Root: generated `powFunctor` fields and their dependent `id` proof domains.

## 1. Root mismatch

The generated `frobeniusPowIso` field is the first structural divergence in the
dependent generated-field path. The three generated fields have distinct
costs; READY2 does not preserve their parent paths in the root trace.

## 2. Matched baseline

`MatchedGeneric` is **A3 diagnostic**: a same-provider generated field compared
with an `id`-wrapped construction. It is non-structural, both sides
kernel-check, and measured 0.009 ms, one call, depth 0 (earlier IM round 2).
It does not preserve the `powFunctor` dependent telescope.

## 3. Provenance distribution

Earlier O trace root: 10,904,899 calls, 23,911.980 ms comparison-exclusive,
16,853.556 ms reduction-exclusive, depth 61; 1,844,240 distinct and 3,155,760
repeated pairs. The root also had 912 proposition comparisons and no Pi-domain
events. Parent IDs and reduction exposure records are absent.

| Provenance | Calls | Exclusive comparison | Share |
|---|---:|---:|---:|
| M0 | 1 root entry (inferred) | not separable | 0% attributable |
| M1 | not classifiable | not classifiable | Unclassified |
| M2 | not classifiable | not classifiable | Unclassified |
| Matched descendants | not classifiable | not classifiable | Unclassified |
| Unclassified | 10,904,898 recursive calls (inferred) | 23,911.980 ms measured total | 100% of attributable trace |

## 4. Newly exposed divergences

The generated proof prefixes and dependent `id` domains are separately
identified in the source snapshots, but no new divergence can be tied to a
reduction event. No M2 claim is made from repeated-pair counts.

## 5. Selective descendant alignment

| Variant | Result |
|---|---|
| O | Earlier root: 29,453.890 ms, 10,904,899 calls. |
| O1/O2/O12/O-all | Invalid/unavailable. `AlignedGeneratedFields` changes generated providers/domains and removes the root mismatch; no child-only intervention type-checks. |
| R | Earlier restored generated-field source restores the original expensive fields; no separately measured selective restoration. |

The aligned source emitted no root above 100 ms, but it is not a valid C
control because M0 is gone.

## 6. Conclusion

The constructor diagnostic is cheap, while generated dependent fields are
expensive. This supports an interaction between dependent context and mismatch
work, Outcome **D/E**, with no defensible M1/M2 split under READY2.
The restored source snapshot retains the original declaration context; the R
source is included for replay, but no separate selective restoration timing was
available.
