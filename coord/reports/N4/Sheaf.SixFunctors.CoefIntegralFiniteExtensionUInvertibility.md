## What changed

Closed the assigned `comparison_invertibility_u` proof by assembling two
blueprint-aligned reductions. The levelwise finite reduction assertion is stated
in `CoefIntegralFiniteExtensionUReductionIsInvertible`, and the normalized
reduction reconstruction criterion is stated in `CoefIntegralFiniteExtensionUReconstruction`.
The assigned module imports both and applies them in sequence. The two lower
proofs remain named split-off statements with their source and proof plan.

## Proved and sorry left

The assigned declaration `comparison_invertibility_u` is proved. Two strictly
simpler statements are split off with `sorry`: `comparison_reduction_isIso_u`
(node `lem-sf-integral-finite-extension-u-reduction-is-invertible`) and
`comparison_invertibility_u_of_reductions` (node
`lem-sf-integral-finite-extension-u-reconstruction`). No definition contains a
`sorry`.

## No longer needed

No existing proof dependency import was removed. The assigned proof uses the core
map definitions, the levelwise reduction statement, and the reconstruction
statement. The detailed finite comparison and coherence nodes remain dependencies
of the levelwise split, while `lem-sf-integral-constructible-reduction-hom` is used
by the reconstruction split.

## Where the brief, the DAG or earlier work was wrong

The original node bundled finite-level counit invertibility with the Milnor/Roos
reconstruction argument, but the current library exposes neither as a theorem
that closes the bundled target. The proof is therefore decomposed into these two
strictly smaller mathematical steps; the target statement and unit route are
unchanged.

## New nodes

`lem-sf-integral-finite-extension-u-reduction-is-invertible` records levelwise
invertibility of the finite reductions.

`lem-sf-integral-finite-extension-u-reconstruction` records the effectivity step
that lifts compatible invertible reductions to invertibility of `u`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionUInvertibility": "2572f8f06c97ac8289a68fc1c87ff4e54dcd89fb", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReconstruction": "8eaec2bf0248586c86074a3abe5363eb33f727da", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReductionIsInvertible": "da9c494d47726769b6ecec43b70a338ad1bc5704"}, "results": {}, "time": "2026-10-28T06:49:13+0800", "transitive": 0, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
