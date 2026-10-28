## What changed

Proved `WeilConjectures.RationalSmoothPurityCanonical.smoothPullToOrdinary_existsUnique`
by applying the existing normalized localization descent argument to the strict
pullback augmentation. Its inverse on each good representative is the ordinary
pullback comparison, the augmentation, and the inverse completed-pullback comparison.
The descent theorem supplies the universal formula for every resolution and every
presenting isomorphism, including uniqueness. Added proof-only `import all` access
to the existing private descent, finite-Tor transport, and
good-localization lemmas. The existing public imports and declaration signatures
are preserved through a public re-export. Extracted the finite trace setup and
already proved strict augmentation into `Sheaf.Paper.RationalSmoothPurityFiniteTrace`,
which contains zero holes. The independent ordinary-monoidal presentation and
its proved private tensor comparison are extracted into the same setup module.
The item imports that private comparison only for its proof. Cached the six
existing proof arguments in `finiteIntegration`
and locally prioritized canonical category instances to reduce elaboration time.
Every map in that composite is unchanged; its proof arguments agree by proof
irrelevance. Change record: `coord/changes/J2-rational-purity-integration-proof-arguments.md`.
The canonical realization node records this argument and its
localization dependency. Final import-order compilation passed without warnings:
`RationalSmoothPurityFiniteTrace` in 26.3 seconds and the item in 51.8 seconds.
A declaration-by-declaration comparison found no changed public signature or attribute.

## Proved and sorry left

Closed one original hole, with no new holes:
`WeilConjectures.RationalSmoothPurityCanonical.smoothPullToOrdinary_existsUnique`.

Five original holes remain, all on node
`def-pur-canonical-rational-purity-realization` with their existing source and
complete proof docstrings:

- `WeilConjectures.RationalSmoothPurityCanonical.finiteIntegration_smoothPurityMap`
- `WeilConjectures.RationalSmoothPurityCanonical.orientation_existsUnique`
- `WeilConjectures.RationalSmoothPurityCanonical.projection_isIso`
- `WeilConjectures.RationalSmoothPurityCanonical.integralMap_isIso`
- `WeilConjectures.RationalSmoothPurityCanonical.rationalIso_scalar`

The proof preserves the full finite-Tor domain and all presenting isomorphisms.
It applies to the zero object, empty schemes, identity morphisms, and relative
dimension zero through the same localization argument.

## No longer needed

No module, node, or unit step is pruned. The three proof imports for finite-Tor
ordinary pullback completeness, ambient augmentation, and the completion-unit
criterion move from the item to the finite-trace module; they remain needed.
Every pre-existing public import is retained.
The descent reuses the existing canonical source-transport lemmas.

## Where the brief, the DAG or earlier work was wrong

The shared queue snapshot called the item rework and retained an older bad-import
build log. The current server queue instead lists it as a six-hole proof item;
its module source is byte-identical to the shared source. The initial unchanged
compile resolved all imports but took 94 seconds. Profiling identified expensive
instance synthesis in `finiteIntegration`; caching its proof arguments and adjusting
local category priorities brought the full module to 74 seconds. Only after those
improvements, the self-contained finite setup was extracted under brief step 3a.
The standing repository brief prohibits all splitting, while the explicit worker
prompt permits it after improving slow definitions; this delivery follows the prompt.
The previous DAG did not record a Lean argument for the normalized smooth pullback
descent. This delivery fills it using the already proved generic descent theorem.

## New nodes

`def-pur-canonical-finite-trace-setup` attaches the existing finite trace and
strict augmentation declarations and the ordinary monoidal presentation to their
extracted module. It contains no new
mathematical obligation and no `sorry`; the canonical realization node cites it
and no longer lists those declarations as physically declared in the item.

## Related modules compiled before delivery

13 related module(s) compiled against this delivery by deliver3.py: 13 OK.

```json
{"capped": false, "direct": 13, "left_out": 0, "own": {"Sheaf.Paper.RationalSmoothPurityCanonical": "2430a765f47401bf90e0fc5e77750537c4322789", "Sheaf.Paper.RationalSmoothPurityFiniteTrace": "0132a3d1f91d1f330b047db225dbada3544e07a2"}, "results": {"Sheaf.Paper.ConstantPurityFrobeniusSquare": {"hash": "57e1afb9cc6da75a28f05ec3856b5b1c77ee5d7b", "status": "OK"}, "Sheaf.Paper.NormalizedFieldPurityTraceData": {"hash": "36c609617fbf62f13e66eb65c56ed562e39b1837", "status": "OK"}, "Sheaf.Paper.NormalizedOrientationPerfectDuality": {"hash": "145740e6c5f67bc36ee7e1685fb1db5db7f77808", "status": "OK"}, "Sheaf.Paper.PurityOrientationDatum": {"hash": "8ad95cb67fbc679d675646cfe7deac645c7691d3", "status": "OK"}, "Sheaf.Paper.RationalWeilPurityNaturalityMate": {"hash": "bea9b1ea85e14d4d7c780bf521d6174ea17668f6", "status": "OK"}, "Sheaf.Paper.SmoothExchangeScalarCompatibility": {"hash": "16a1d704e33e2ff5dfc911308828582d30471344", "status": "OK"}, "Sheaf.Paper.SmoothOrientationCoefficientFamily": {"hash": "85e678539acc0c392ae845414062edde93186d60", "status": "OK"}, "Sheaf.Paper.SmoothOrientedExchangeComparisons": {"hash": "de3d5be39a7b13d81a4349282813b9d32286bd94", "status": "OK"}, "Sheaf.Paper.TowerTracePurityComparisonData": {"hash": "012d5b7763990f7c15e15cf4fcebdda6336c4c34", "status": "OK"}, "Sheaf.Paper.WeilPurityEquivarianceData": {"hash": "bdce441e9daeca0d3c8b4c8f9ff71787b78dbb3a", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityLineComparisons": {"hash": "7dfea4a2aa9ca58786b61db04994341c85d15175", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityTraceCoherence": {"hash": "0091913289529cd60ce8938cc38e96ee7a2ce7a4", "status": "OK"}, "Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality": {"hash": "4cb460929f9ff045c0629d458c2bcf359c6e98da", "status": "OK"}}, "seconds": 143, "time": "2026-10-28T07:26:42+0800", "transitive": 0, "version": 1}
```

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
