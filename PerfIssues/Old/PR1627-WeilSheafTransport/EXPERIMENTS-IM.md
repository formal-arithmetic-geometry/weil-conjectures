# Intrinsic vs mismatch-induced DefEq report

Case: PR1627-WeilSheafTransport
Operation family: dependent generated fields
Revision: current-case oleans at a2ec460045b; Lean 4.35.0 READY2.
Root conversion: generated powFunctor fields and dependent id domains.

OriginalGeneratedFields and RestoredGeneratedFields are O/R; the aligned generic
helper is A. M is invalid because a matched provider changes the dependent domain
of the next generated field. The generated frobeniusPowIso field is the first
structural divergence.

Fresh root 1539: 29,453.890 ms, 10,904,899 calls, depth 61,
15,941.908/13,511.981 ms comparison/reduction, dependent timers
15,693.452/13,376.044 ms, Expr proxy 151,676,221 / 5,085,228,440 bytes.
READY2 trace: 40,765.536 ms and 23,911.980/16,853.556 ms; 1,844,240 distinct and
3,155,760 repeated pairs cost 2.865 s. A emitted no root above 100 ms.

Conclusion: H1/H3, with no valid H2 isolation. Dependent comparison below the
generated proof body owns the time. No relevant implicit provider is inferred,
so unif_hint is not applicable.

## IM round 2

`probes/im/MatchedGeneric.lean` supplies a diagnostic same-provider generated
dependent field: a `GeneratedField.mk` value with its proof field intact,
compared with an `id`-wrapped construction. The heads are non-identical, both
sides kernel-check, and the pair is definitionally equal.

Fresh READY2 zero-threshold counters measured M at `0.009 ms`, one call, depth
`0`, `0.006/0.003 ms` comparison/reduction, and one proof attempt; the source
check reports `0 ms`. This is a construction-boundary diagnostic rather than
a replacement for the original `powFunctor` root. O/A remain AD-phase values.

Verdict: the generated-field constructor alone is cheap, but the original
dependent-field root remains inconclusive between H1 and H3 without a fresh
compatible replay. No `unif_hint` provider assignment exists.
