## What changed

Repaired and proved `AlgebraicGeometry.Scheme.PurityIntegralTower.strictTateTensorTower_evaluation`
in `Sheaf.Paper.StrictTateTensorTowerLiftEvaluation`. It now chooses corrected level
isomorphisms satisfying the evaluation equation from any initial level isomorphisms.
The original equation for every arbitrary choice was false.

The proof first proves local surjectivity of the actual completed-coefficient projection
using the existing `pbcCompletedScalar`, its constant quotient projection formula,
and local constant representatives. It proves full faithfulness of ordinary scalar
restriction. Mathlib's full faithfulness of `DerivedCategory.singleFunctor` and
`Functor.mapDerivedCategorySingleFunctor` then lift the evaluation discrepancy to
an ordinary quotient-line automorphism. Adjusting the initial isomorphism by that
automorphism cancels the discrepancy. No global fullness of derived scalar restriction
is assumed or asserted.

Added only the proof import `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`.
The existing public import stays. All helpers are private and fully proved; no new
module or public helper is introduced. The source tree `lean/WeilConjectures` is untouched.

Adapted the sole consumer, `Sheaf.Paper.StrictTateTensorTowerLift`, to use the corrected
isomorphisms as its existential witnesses. Its complete public signature is unchanged.
The original consumer was compiled against the corrected theorem and failed at line 72:
`strictTateTensorTower_evaluation ...` now has type `∃ q′, ∀ n, ...` while the
original proof expected `∀ n, ...` for its initial `q`. The two changed proof lines
unpack that existential and insert the resulting witnesses.
Updated the evaluation node's statement, Lean record and proof, with a statement-change
record auditing its sole citer; updated the parent's proof description. Change record:
`coord/changes/strict-tate-tensor-tower-evaluation-normalization.md`.

## Proved and sorry left

The item originally had one hole, in
`AlgebraicGeometry.Scheme.PurityIntegralTower.strictTateTensorTower_evaluation`
(node `lem-pur-strict-tate-tensor-tower-evaluation`). The corrected normalization theorem
is proved in full, and the original parent lift theorem is assembled from it without
changing that parent's statement. The false universal-in-the-initial-isomorphisms
statement is explicitly repaired, not claimed to have been proved.

Item holes remaining: zero. Holes added: zero. Split-off statements: zero.
Single-file validation through `lcompile.py`: corrected evaluation module compiled
without warnings in 31.3 seconds; adapted parent compiled without warnings in
21.6 seconds against the delivered evaluation module. The unchanged original
consumer's expected type mismatch was checked before adapting it.
`AlgebraicGeometry.Scheme.PurityIntegralTower.strictTateTensorTower_lift` remains
proved with no direct hole. The existing separate theorem `strictTateTensorTower_data`
is untouched and remains a dependency with its existing hole; no hole is moved into it.

## No longer needed

Removed proof dependency `lem-pur-site-restriction-module-adjunction-exact`
(`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`) from this node's proof plan.
It concerns restriction to a localized site and supplies no normalization of arbitrary
level isomorphisms. This proof instead uses scalar restriction and Mathlib's existing
single-complex comparison and full-faithfulness instances. That module was never
imported by the item, so no Lean import removal or module withdrawal is claimed.

No other declared dependency or module is pruned. The strict tower data dependency
and the unit's entire realized route are preserved. The existing constant-to-completion
map is reused rather than reconstructed under a second name.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (repaired): the old theorem asserted the equation for arbitrary
`q`. Replace one `q n` by its composite with multiplication by `-1` on a nonzero
rank-one quotient line at an odd prime, with `d = 0`. Its inverse changes the left
side, while the right side and every hypothesis stay fixed. For example the scalar
ring at exponent one for `ell = 3` has distinct scalars `1` and `-1`.
The AdicTower fields do not constrain these independently supplied `q`.

The source construction asks for chosen evaluation-compatible identifications, as
the existential parent theorem states. The correction proves precisely their existence,
retaining `M`, its levels, its evaluation, and `h`. The sole DAG citer
`lem-pur-strict-tate-tensor-tower-lift` still holds: choose the corrected isomorphisms
instead of the arbitrary initial ones. Its Lean proof is adapted in this delivery.

Edge cases: the zero object needs no nontrivial correction; the full-faithful lifting
argument applies unchanged. All single degrees are handled uniformly, including
`d = 0`, and local quotient surjectivity works at `n = 0` and every prime, including
`ell = 2`. No extra hypothesis is imposed on any case.

Searches used the prescribed LeanFinder and Loogle services plus `rg` over Mathlib,
WeilConjectures and Sheaf. The useful generic lemmas are the Mathlib single-complex
full/faithful instances, exact-functor single comparison, and `Functor.Full.of_iso`.
The two named dependency declarations were read before choosing this shorter route.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.StrictTateTensorTowerLift": "2ab24b6f6dd09bef95729ca7b4459270de6ad5af", "Sheaf.Paper.StrictTateTensorTowerLiftEvaluation": "ee5fa287f48610dfbc0b7c81105adb9965c22e4f"}, "results": {}, "time": "2026-10-28T07:08:03+0800", "transitive": 0, "version": 1}
```

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
