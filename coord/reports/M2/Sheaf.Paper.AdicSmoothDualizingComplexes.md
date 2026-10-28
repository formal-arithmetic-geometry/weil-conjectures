## What changed

Proved `WeilConjectures.AdicSmoothDualizing.existsUnique_rootComparison`.
Finite Tate site descent supplies existence. Invertibility of the prime follows
from invertibility of its positive level power. Equality on local lifted root
tensors proves uniqueness using the existing extensionality theorem and `Iso.ext`.
Added the proof-only import `Sheaf.Paper.FiniteTateLocalRootTensorsExt` in the
finite-comparison module.
The argument includes degree zero and the first positive coefficient level.

Proved `WeilConjectures.AdicSmoothDualizing.adic_and_rational_smooth_dualizing_complexes`.
The integral normalization is the specification of the uniquely chosen integral
identification. A fully proved private categorical helper transports the counit
through an identification. Apply it to rationalization, small-model scalar
extension and common-stage inclusion; cancellation of each inverse identification
recovers exactly the recorded integration maps.

Proved `WeilConjectures.AdicSmoothDualizing.integralTwist_mem` from the existing
signed-line membership, triangulated shift stability and integral residue-Tor
criterion. The coefficient prime is invertible in the residue fields because its
local-ring image is a unit. No finite-type restriction on T is needed. The proof
adds only private imports of `IntegralResidueTor` and
`SfIntegralConstructibleTriangulated`.

Replaced the existing `finiteUnitPlus` proof by direct application of exact
derived-functor preservation of lower bounds. `levelSetting` now is an abbreviation
with exactly the same record value, and unnecessary scoped transparency overrides
were removed. The change records are
`coord/changes/M2-adic-level-setting-transparency.md` and
`coord/changes/M2-adic-finite-power-module.md`, and
`coord/changes/M2-adic-finite-comparison-module.md`.
The existing finite-power block is extracted into
`Sheaf.Paper.AdicSmoothDualizingFinitePowers` and publicly imported by the item;
all eleven qualified names, signatures and bodies are preserved. Its one
existing hole is moved with it and the existing definition node's Lean record
is updated. This is a compile-time file split after the definition improvements,
not a new mathematical decomposition.
`finitePowerComparison` now uses named site and intrinsic single-shift factors
with the same literal endpoints and the intrinsic functor written in its signature.
These are the original factors, separated to avoid repeated kernel unfolding.
The finite-comparison interval is likewise extracted into
`Sheaf.Paper.AdicSmoothDualizingFiniteComparison` and publicly reexported.
All existing declaration signatures and mathematical data are preserved. The old
public import surface remains available through public reexports. The previous
combined item compiled cleanly in 47.8 seconds once, but subsequent probe and
profiling runs exceeded 60 seconds, motivating these file splits.
The final three modules compiled in import order in 11.8, 44.9 and 32.7 seconds;
the final item with the membership proof compiled in 31.4 seconds.
Direct-consumer checks before the file extraction: `PoincareDualityConventions` compiled in 42.6 seconds;
`RationalSmoothPurityFiniteTrace` compiled from the unpublished-dependency cache.
`RationalSmoothPurityCanonical` had no Lean errors but exceeded the limit with
this packet (80.6 seconds) and also in a separate baseline sandbox against the
published item (70.8 seconds). Its profile attributes the main costs to its own
`smoothPullToOrdinary_existsUnique` kernel checking and `rationalIso_scalar`
statement elaboration. `PurityOrientationDatum` could not load the unpublished
`RationalSmoothPurityFiniteTrace.olean` through its published Canonical dependency.
No consumer source changes are included.

## Proved and sorry left

Closed three of seven original holes:

- `WeilConjectures.AdicSmoothDualizing.existsUnique_rootComparison`
- `WeilConjectures.AdicSmoothDualizing.integralTwist_mem`
- `WeilConjectures.AdicSmoothDualizing.adic_and_rational_smooth_dualizing_complexes`

No holes were added. Four original holes remain in namespace
`WeilConjectures.AdicSmoothDualizing`. One remains in the item, attached to
`cor-pur-adic-and-rational-smooth-dualizing-complexes`:

- `existsUnique_integralIdentification`

Two are moved unchanged to `AdicSmoothDualizingFiniteComparison`, attached to
`def-pur-adic-finite-comparison-model`:

- `existsUnique_lineProjection`
- `existsUnique_finiteRealization`

The fourth, `existsUnique_etalePowerPresentation`, is unchanged in the extracted
`AdicSmoothDualizingFinitePowers` module and attached to its existing owner,
`def-sf-etale-power-presentation`. No new split-off statements were introduced.

## No longer needed

No module is globally pruned. The direct proof imports
`Sheaf.AlgebraicGeometry.FiniteEtaleTateTensorFamily` and
`WeilConjectures.SixFunctors.Etale.Derived.InvertibleSheafPowers` move from the item
to the finite-power module. The public `FiniteTateSiteDescent` import moves to
the finite-comparison module. All three imports remain needed by these
constructions. The finite-power node remains needed there; the corollary node now
records the finite-power definition node as the direct dependency instead.
The remaining holes retain their declared dependency route. The completed
proofs use the existing finite Tate descent, local-root-tensor extensionality and
constructible exceptional coefficient-comparison nodes; these dependencies are now
explicit in the item node.

## Where the brief, the DAG or earlier work was wrong

The node did not record the declarations used for the finite root-comparison and
categorical counit-assembly steps, or the reusable membership route. Its proof and dependency list now include them.
The pre-existing broad transparency overrides made the module expensive to
elaborate. The finite-setting wrapper can expose its unchanged field data directly.
No mathematical statement was weakened or changed.

## New nodes

`def-pur-adic-finite-comparison-model` records the existing completed-line
projection, normalized finite site comparison and intrinsic realization data in
their extracted module. It adds no theorem statement or hole; the two original
projection and realization obligations move with their constructions. Its proof
records the completed root-comparison argument and the literal factors of
`finitePowerComparison`. The associated change record is
`coord/changes/M2-adic-finite-comparison-module.md`.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 2 OK, 2 SLOW.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.AdicSmoothDualizingComplexes": "29bf4c65824450f599ebfa4fead36f9c686eb8f7", "Sheaf.Paper.AdicSmoothDualizingFiniteComparison": "6a571cbcc9e27ff2fab4ca3b56e1389f36b8508c", "Sheaf.Paper.AdicSmoothDualizingFinitePowers": "e465c49298dadc0fb90dcebb0b5660fabb4b6535"}, "results": {"Sheaf.Paper.PoincareDualityConventions": {"hash": "71d52f8104ddecbf825f8e45fb9ea089898b08b2", "status": "OK"}, "Sheaf.Paper.PurityOrientationDatum": {"hash": "8ad95cb67fbc679d675646cfe7deac645c7691d3", "status": "SLOW"}, "Sheaf.Paper.RationalSmoothPurityCanonical": {"hash": "2430a765f47401bf90e0fc5e77750537c4322789", "status": "SLOW"}, "Sheaf.Paper.RationalSmoothPurityFiniteTrace": {"hash": "0132a3d1f91d1f330b047db225dbada3544e07a2", "status": "OK"}}, "seconds": 217, "time": "2026-10-28T11:05:00+0800", "transitive": 0, "version": 1}
```

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
