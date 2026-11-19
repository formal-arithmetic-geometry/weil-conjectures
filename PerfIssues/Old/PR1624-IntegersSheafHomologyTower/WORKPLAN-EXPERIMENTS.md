# Workplan experiments: PR #1624

Case: `P1624-iso-trans-last-domain`, declaration
`AlgebraicGeometry.ProEtale.homologyIntegersTowerIso`. Lean 4.35.0,
master revision `1ef1fddac73e`, original module identity, one Lean thread.

## Baseline

The expensive site is the final `Iso.trans` argument-domain conversion:
the inferred type of `isoWhiskerLeft` versus the seventh instantiated
domain. The outer heads are the same `CategoryTheory.Iso`; carrier and
category arguments compare in 0 ms. The source and target endpoint
arguments are both `Functor.comp`, taking 14.706 s and 28.640 s in the
existing domain probe. The original module check is 102 s (111.38 s CPU,
11,038,208 KB RSS); the fixed control is 3.18 s (11.77 s CPU,
2,668,464 KB RSS).

## G1-A: endpoint arguments

Probe: [`G1A-IsoCompArguments.lean`](probes/wp/G1A-IsoCompArguments.lean).

| Endpoint | Argument | Left/right outer heads | Structural | Independent DefEq |
|---|---:|---|---|---:|
| source | 0,1,4,5 | matching `Opposite`/category/sheaf heads | equal | 0-1 ms |
| source | 2,3 | `Sheaf` / full-subcategory category | different | 0-1 ms, unequal |
| source | 6,7 | `Functor.comp` | different | 0/3 ms, unequal |
| target | 0,1,4,5 | matching heads | equal | 0-1 ms |
| target | 2,3 | `Sheaf` / full-subcategory category | different | 0-1 ms, unequal |
| target | 6 | `Functor.comp` / `higherDirectImageQuotPowTower` | different | 8 ms, unequal |
| target | 7 | `Functor.comp` | different | 1 ms, unequal |

The rerun of the argument table used 174.03 s CPU, 2:56.77 wall, and
11,047,696 KB RSS. The complete endpoint timings are from the preserved
`IsoDomainArguments` baseline and measure the same conversion site.

## G1-B/C: one-factor alignment and enclosing body

The workplan probe rechecks each complete endpoint, then attempts to replace
only arguments 2, 3, 6, and 7 on the expected endpoint. All eight attempted
replacements (four per endpoint) are rejected by `Kernel.check` as
ill-typed: those arguments carry dependent endpoint data and cannot be
aligned independently. The probe also reports the immediate body of regular
`Functor.comp`, which is `Functor.mk`.

This separates the cheap local unequal comparisons from the expensive
whole endpoint conversion. The individual argument differences do not
explain the cost by their own checks; the concrete compositions must be
reduced under the enclosing `Functor.comp` representation. Because no
single-factor type-preserving alignment exists, this is a negative control,
not a causal speedup claim.

## Interpretation

The high-level heads are shared, but arguments 2/3/6/7 are not independently
definitionally equal. One-step unfolding exposes `Functor.mk`; this is the
first common body-level representation. The original concrete representation
therefore needs reduction before endpoint equality can be established.
The fixed auxiliary theorem passes the pieces as functor variables and
avoids this comparison. The internal reduction sequence below `Functor.mk`
is not observable with the permitted tools.

**Confidence:** strongly supported for the same-head argument mechanism;
the exact first Kernel branch below `Functor.mk` remains unresolved.
