# K4c kernel-cost results

The independent Strategy3 reading chain and its dedicated coefficient category pass normal
kernel checking. The unchanged live theorem `purityCanonicalTateOneTrivialization_weil` also
passes after adopting K4a's audited native scalar proof. LEAD's 00:50 plan superseded the
original dense round-trip requirement, and the 03:45 instruction directed adoption of K4a's
successful scalar proof. After K4a's finite audit completed, its original-name finite wrapper
and original-data predicate bridge were also adopted from `620ed3b89`; their recheck on this
branch is pending. This is adoption of a verified repair, separate from the independent
Strategy3 implementation.

The finite wrapper's exposed `finiteReadingEquation` body is the original equation, with the
original equivalences, pullback comparison, and reading isomorphisms supplied as data.
`finiteReadingEquation_original` kernel-checks the transport of those data. No successful
check of the fully expanded old statement is claimed.

## Verified results

Snapshot `bf586f3b59`, remote log
`/home/ubuntu/u9/logs/K4c-20261105T210151.log`:

| Declaration | Logged elaboration | Kernel |
| --- | ---: | ---: |
| `Strategy3.purity_finiteCoefficientIntegralTateOneReading_pullback` | 208.61 ms | 622 ms |
| `Strategy3.K4Coefficient.integralReading_pullback` | 103.02 ms | 53.6 ms |
| `Strategy3.K4Coefficient.realize_equation` | see TSV | 3.37 ms |
| `purityCanonicalTateOneTrivialization_weil` (K4a proof) | 220.9 ms | 56.4 ms |

Both native reading theorems, the generic indexed scalar consumer, the canonical scalar
theorem, its named root equation, and its native rational root equation have axiom closure
exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx` occurs. The scalar coefficient
postcomposition helper costs 30.6 s in the kernel; this cost is retained in the report rather
than hidden behind the final application.

The full invocation above returned failure because of an independent new open-exchange
helper. It certifies the listed completed modules, not a green combined build. Subsequent
combined verification and the open-exchange results are recorded below when complete.

`K4C_BENCHMARK.tsv` records declaration-level profiler output, including failed controls.
Logged elaboration is the sum of the profiler's elaboration events, not total elapsed time;
separately logged tactic and instance-search times are not included. Kernel totals include
generated auxiliaries attached to the declaration. Earlier adopted files used a 1 ms reporting
threshold; absence of a recorded kernel event there means below the reporting threshold, not
zero work. The final profiling pass uses threshold 0 throughout new helper modules.

## Failed controls

- Mixing the old inferred target coefficient object into the new reduction map caused a
  60.9 s kernel timeout. Explicit new codomains fixed the conversion; the native integral
  reduction compatibility then checked in 1.19 s.
- An outer finite pullback-isomorphism equality by `rfl` timed out at 62.2 s; replacing it by
  small identity rewrites still timed out at 57.8 s.
- Even the outer boundary's type and source-functor identity timed out at 65.7 s and 66.5 s.
  A separate raw-ring control (`0d41a6f011`, log `K4c-20261105T204757.log`) reduced them to
  224 ms and 237 ms. Its transported-isomorphism `rfl` then exceeded elaborator recursion.
  That diagnostic variant is frozen in history and is not the retained implementation.
- The indexed scalar consumer itself checked in 10.6 ms, but its concrete source/root input
  conversions exhausted elaboration. This competing scalar route was stopped when K4a's
  audit passed, as instructed.

## Reusable recipe

1. Give the new coefficient type, ring object, reduction maps, and sections explicit types.
2. Rebuild pullbacks, adjunctions, compositors, coefficient equivalences, and reading maps in
   that vocabulary; inspect implicit functor and instance arguments as carefully as terms.
3. Build the finite reading square natively; do not convert the completed old equation.
4. Construct the integral reduction square using reduction maps with explicit new codomains.
5. Compose the two squares with an abstract categorical lemma whose data arguments are explicit.
6. Let the dedicated coefficient-category consumer retain those native objects and maps.
7. For the live scalar theorem, keep K4a's raw root objects and package the equation in an
   exposed predicate defined over an abstract preadditive category.
8. Rewrite whole-isomorphism data inside that predicate and consume it abstractly.
9. Profile intermediate applications and final declarations; audit complete axiom closures.

## Open-exchange follow-up

Following LEAD's 04:25 instruction, the branch also develops the integral open-immersion
contribution to W2(b). Abstract mate-coordinate transport and exchange transport are checked.
Concrete canonical reduction and compactification normalization are under remote verification.
The comparison with the actual finite étale compactification exchange remains separate from
the adjunction-exchange cube; no completion of that outer boundary is claimed here.
