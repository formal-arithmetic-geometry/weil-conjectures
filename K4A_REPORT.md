# K4a kernel-cost repair

K4FIX OK for `AlgebraicGeometry.ProEtale.purityCanonicalTateOneTrivialization_weil`.
The statement is byte-identical to K4 commit
`f5d3862758dd592b4bf0a8ce769f0b01e7d5e1af`. The proof first passed at
`a730b76d91afc9eac5a9f4486b802e701fb6fc7a`; its separate axiom audit passed at
`ecd7b1cf8`. The audit reports exactly `propext`, `Classical.choice`, and
`Quot.sound`, including for the native rational root theorem and named scalar
equation. It has no dependency on a sorried leaf.

The original no_expose experiment failed: coefficient reduction, reading, and
the final bridge timed out at 60.6 s, 63.6 s, and 62.6 s. LEAD 00:50 superseded
that strategy with Nailin's native reconstruction plan. The delivered native
modules use `@[expose] public section`; they introduce no opacity controls,
axioms, admissions, heterogeneous equalities, or resource-limit increases.
Failed experiments remain in commit history, outside the delivered source.

## Proof and reusable recipe

1. Preserve each input's inexpensive representation. The rational root source
   remains the raw `Mod.extendScalars.obj` expression.
2. Define a generic Frobenius component with source `Q.obj (P.obj M)`.
3. Rebuild coefficient transport and the rational root law from lower-level
   inputs using this component, without applying the old finished root law.
4. Define `scalarEquation Q a b e c` over an abstract preadditive category in
   a separate exposed module.
5. Package the native law in this predicate, keeping its source spelling.
6. Establish identities of whole isomorphisms; rewrite only the predicate's
   data arguments into the existing named coordinates.
7. Consume the predicate with a generic conjugation lemma, where unfolding
   happens with abstract objects and functors.
8. Apply the existing canonical equation interface and `exact_mod_proofs` at
   the inexpensive final boundary. Profile and audit that final application.

## Integration

K4 needs the five `SmoothPurityK4NativeScalar*.lean` modules,
`SmoothPurityScalarPullbackInterface.lean`, and the proof in
`SmoothPurityCanonicalTateScalar.lean`. The interface exposes its definitions
and adds `purityScalarSourceDatum_eq_iso` and
`purityScalarSourceUnitDatum_eq_iso`. It retains the original comparison laws.
The canonical isomorphism definition and final theorem statement are unchanged.
Source comparison also confirms that all 14 data definitions in the scalar
interface are unchanged, apart from visibility attributes and whitespace.

The finite reconstruction is independent of this scalar proof. The branch
ports 41 K4 source files including the target, from the pinned commit above;
pre-existing dependency boundaries matched exactly. The unused generic
`SmoothPurityScalarDescentConjugation` is included in the final validation.

## Measurements

All builds use `ucheck`, Lean 4.33.1, the upstream lake options, default
heartbeats, and normal kernel checking. Instrumentation is `profiler true`
with a 1 ms threshold. No `trace.profiler` output is used for these measurements.
The pinned mathlib revision is `0df444a360eaa60ab8c11dca51a86af692955474`.
`K4A_BENCHMARK.tsv` preserves source-positioned events;
`K4A_DECLARATION_TIMES.tsv` gives every newly profiled declaration's timings.
`K4A_FILES.tsv` lists all 59 changed or added Lean files and their provenance.
Elaboration, tactic execution, typeclass inference, and kernel checking are
separate profiler phases. Subthreshold events are marked unreported rather
than claimed to be zero. Generated auxiliary declarations are included in
their enclosing declaration's kernel total.

| Declaration | Elaboration | Kernel |
|---|---:|---:|
| `scalarFunctor_coefficient` | 62.58 ms | 6.63 ms |
| `scalarDatum_postcomposeIso` | 19.1 ms | 2.82 ms |
| `purityChangeCoefficientPullbackIso_weil` (native) | 300.2 ms | 139 ms |
| `purityChangeCoefficientTrivialization_weil` (native) | 324.9 ms | 43.7 s |
| `purity_rationalRootTrivialization_weil` (native) | 706.2 ms | 418 ms |
| `scalarSourceIso_eq` | 326.84 ms | 154 ms |
| `scalarSourceUnitIso_eq` | 79.68 ms | 57.5 ms |
| `scalarRootEquation_native` | 452.5 ms | 260 ms |
| `scalarRootEquation_named` | 17.23 ms | 278 ms |
| `scalarEquation_conjugate_named` | 15.8 ms | 1.38 ms |
| `purityCanonicalTateOneTrivialization_weil` | 115.29 ms | 78.9 ms |

The final theorem's tactic time is 122.85 ms and module wall time 3.5 s.
The coefficient module rebuild takes 50 s: the 43.7 s helper is a remaining
cost, explicitly measured and successfully checked at the normal limit.
The axiom-audit build independently rebuilt all changed scalar modules.
The build pool sets `LEAN_NUM_THREADS=3`; per-declaration user CPU and peak RSS
were not collected. Wall times vary across pool machines.

The same native root proof with a `tateTwistOne` source alias timed out in the
kernel at 172 s (`020b18a07c`, log `K4a-20261105T202543.log`). Retaining the raw
coefficient-extension source reduced it to 418 ms. Restating the expanded
named scalar equality still timed out at 187 s (`4a5a5bb1c3`, log
`K4a-20261105T203807.log`); transporting the folded predicate's data arguments
instead checks in 278 ms. These are independent controls, not successful
builds or evidence of a changed heartbeat limit.

Successful scalar logs on `ubuntu@43.131.49.250`:

- `/home/ubuntu/u9/logs/K4a-20261105T203301.log`: native root, 418 ms kernel.
- `/home/ubuntu/u9/logs/K4a-20261105T204302.log`: canonical theorem, 10175 jobs.
- `/home/ubuntu/u9/logs/K4a-20261105T204640.log`: complete scalar rebuild and
  axiom audit, rc=0, 10176 jobs, pool `43.157.168.235`.

## Finite reading

The finite comparison, free module, site, root, Tate-line and integral-reading
constructions were rebuilt in the consumer's
`integersModPowCoeff` / `integersModPowRingObj` vocabulary. The old reading
square is not applied as a proof of the rebuilt square. Native integral
reading checks in 904 ms; five whole-data bridges check in at most 273 ms.
Successful logs are `K4a-20261105T200439.log` and
`K4a-20261105T200712.log` in the same remote log directory.

The original expanded finite proposition times out even as a Prop-valued
definition without a proof (59.3 s, `7dd301e048`, log `K4a-20261105T202423.log`).
Per LEAD 00:50, the original theorem name now uses the exposed
`finiteReadingEquation` predicate with the ORIGINAL equivalence, pullback and
reading constructors as arguments. Its body is the original mathematical
equation. Data arguments are transported using separately checked whole-data
equalities; no final expanded-equation round trip is asserted.
Substituting the original data into the predicate body reproduces the original
equation text exactly after whitespace normalization; this source comparison
supplements the kernel validation and does not replace it.

The final finite predicate, named wrapper and axiom audit are GREEN in
`/home/ubuntu/u9/logs/K4a-20261105T204835.log` at
`061954d781cf150fb2638a8e11f8fabee78c4149`: 22284 jobs completed successfully.
The native integral theorem, original-data predicate, and original-name
wrapper each have exactly the three standard axioms listed above.

| Finite declaration | Elaboration | Kernel |
|---|---:|---:|
| `finiteReadingEquation` (including generated auxiliaries) | 275 ms | 180.78 ms |
| `finiteReadingEquation_native` | 29.35 ms | 592 ms |
| `finiteReadingEquation_original` | 650.87 ms | 342 ms |
| `purity_finiteCoefficientIntegralTateOneReading_pullback` | 616.33 ms | 57 ms |
| `purity_finiteCoefficientIntegralTateOneReading_pullback_exact` | 584.27 ms | 56.8 ms |

The predicate module takes 8.7 s, the original-name wrapper module 6.7 s, and
its axiom audit 3.8 s. The scalar audit, finite audit, and explicitly selected
`SmoothPurityScalarDescentConjugation` together cover all 59 changed or added
Lean files. The declaration table contains 86 declarations, including the
local instances and source-positioned generated auxiliaries.
