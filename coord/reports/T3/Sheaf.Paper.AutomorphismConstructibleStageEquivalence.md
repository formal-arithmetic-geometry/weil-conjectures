## What changed

Constructed the common-stage automorphism square by descending its prescribed
rational components. The proof builds a morphism of stage-system functors,
descends its natural transformation, proves that it is invertible, and transports
it through the composition isomorphisms. The component formula follows from the
literal pair-object construction; componentwise extensionality proves uniqueness.

The remaining finite coefficient-transition equation is isolated in the new
`automorphismSquareStageCompatibility` theorem. It is an equality in the rational
category at a finite field, before common-stage descent. Its hypotheses prescribe
the integral compositors and rationalized components. It asserts neither a global
isomorphism nor global existence, invertibility, normalization, or uniqueness.

The pre-existing inverse-comparison argument is now compiled separately in
`AutomorphismInverseComparisonDescent`. Its original public theorem retains its
signature and unfolds `automorphismStageIntegralCancel` to invoke this proved
helper. Profiling identified that argument as approximately ten seconds of the
large module. Local opaque stage witnesses and irreducible comparison interfaces
preserve its formulas; the extraction gives the main module compilation margin.

## Proved and sorry left

Original holes: two. The body of
`WeilConjectures.automorphismStageQbarSquare_existsUnique` is now complete Lean,
using the new finite-stage compatibility statement. This is a decomposition,
not a net hole closure.

One new hole:
`WeilConjectures.automorphismSquareStageCompatibility`.

One original hole remains untouched:
`WeilConjectures.automorphismConstructibleStage_descended_shifts`.

Thus one original hole is reduced, one is untouched, one lower hole is added,
and the total hole count is two. No definition contains a hole.

`WeilConjectures.commonStagePullbackSquare_existsUnique` is fully proved in a
new module. Local irreducibility protects the operation interfaces. Factoring the
categorical assembly into a private helper and then extracting the self-contained
descent proof avoids the expensive unfolding identified by the compiler profiler.
No time or heartbeat limit was raised.

Validation: `lcompile.py --all` compiles all four modules in import order. The
main module takes 50.8 seconds and the extracted inverse proof 11.5 seconds;
the common-stage descent helper previously compiled in 24.2 seconds. Diagnostic
profiler options and traces have been removed.

## No longer needed

Removed the main module's direct proof import of
`Sheaf.Paper.IntegralAutomorphismCancellationNormalization`; the extracted inverse
comparison helper still needs and imports it. No mathematical module or original
DAG dependency is pruned. The original unit
route is preserved. The common-stage construction uses the existing generic
stage-system descent API instead of duplicating its representative calculations.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The finite-stage scalar equation was implicit in
the original proof steps 7–9; it is now a separate, precisely stated obligation.
Identity coefficient inclusions, empty schemes, and semilinear automorphisms
require no additional hypotheses. The equation uses representative-normalized
comparisons; it does not infer equality from reduction to finite coefficients.

## New nodes

`lem-sf-automorphism-square-stage-compatibility` records the finite coefficient
transition equation, its normalized integral origin, rationalization argument,
and the conjugation by the actual stage-transition identifications.

`lem-sf-common-stage-pullback-square-descent` records the fully proved descent of
an already compatible family of finite natural isomorphisms, including its precise
component formula and uniqueness. It uses the existing generic associative
stage-family descent API and the normalized pullback descent theorem.

`lem-sf-automorphism-inverse-comparison-descent` records the fully proved extracted
inverse-comparison argument. Its statement spells out the original integral cancel
formula and retains the rational and common-stage component normalizations. The
original public theorem uses the invertibility instance already available there.

## Related modules compiled before delivery

11 related module(s) compiled against this delivery by deliver3.py: 7 OK, 4 SLOW.

```json
{"capped": false, "direct": 11, "left_out": 0, "own": {"Sheaf.Paper.AutomorphismConstructibleStageEquivalence": "6bb9c8c0d6798dcfc3e0fbaff2197351364de4e0", "Sheaf.Paper.AutomorphismInverseComparisonDescent": "dee45cebd8291d0ada05201317408b7f68d4de8f", "Sheaf.Paper.AutomorphismSquareStageCompatibility": "f9777ba8a38b3c18e61aba838c63896020b671b0", "Sheaf.Paper.CommonStagePullbackSquareDescent": "eabfa90eb24f71d5826ebe77072478b1804b5a34"}, "results": {"Sheaf.Paper.AutomorphismSquareRationalScalar": {"hash": "3f633ada8bff092437f93fb7723baa024f6035b2", "status": "OK"}, "Sheaf.Paper.CommonStageOpenHeartAdjunction": {"hash": "9c5fc8eee1c11e239dcc5d8b35671125e5703e3e", "status": "SLOW"}, "Sheaf.Paper.FieldWeilShriekShiftData": {"hash": "8339b4e3e8b675fccaec54fc404987de96ebcd23", "status": "OK"}, "Sheaf.Paper.FixedPairTruncationCohomology": {"hash": "2d664b1e22e47b4d2c2480150ffe682699b01589", "status": "SLOW"}, "Sheaf.Paper.FrobeniusPullbackOrdinaryExchange": {"hash": "9a3d90de23be8c6da1565d784f371530b6cd875f", "status": "SLOW"}, "Sheaf.Paper.ResidueCompatiblePullbackFrobenius": {"hash": "3809fb3bf7cf447f73328d73f4943b7fdf05fed4", "status": "SLOW"}, "Sheaf.Paper.SfNormalizedRationalWeilSquares": {"hash": "f6275bc1a5725a9b6de7b033c4b5b3b89996817f", "status": "OK"}, "Sheaf.Paper.SfOpenClosedTriangleAllStages": {"hash": "f6be17105c0c75668b15a4398ff58ce2cbce0a37", "status": "OK"}, "Sheaf.SixFunctors.OpenClosedWeilMateFinite": {"hash": "8c1cddfd4a509daed116b18d02a8678db143e7ed", "status": "OK"}, "Sheaf.SixFunctors.OpenClosedWeilMateIntegral": {"hash": "d42f07b1e8972be9600efb177069f4a042a6ce6d", "status": "OK"}, "Sheaf.SixFunctors.SupportedWeilMateLift": {"hash": "dd593ad91ee5296e4c3c0ffc281f23c784a54726", "status": "OK"}}, "seconds": 262, "time": "2026-10-28T11:34:23+0800", "transitive": 0, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
