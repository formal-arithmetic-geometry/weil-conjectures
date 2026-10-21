## What changed

Filled all three proofs in `Sheaf.AlgebraicGeometry.UnrestrictedFrobeniusFactorization`.
The projection theorem uses existing characteristic/descent lemmas, the proved source-library
`Scheme.comp_iterateFrobenius`, the global-sections identification of Frobenius on Spec k,
and existing base-change/coefficient-action projection identities. Pullback uniqueness gives
both arithmetic factorizations; `galoisMap_inverse` and associativity give both geometric
factorizations and both inverse equations. Model naturality follows by applying the pullback
functor to naturality in the slice category. Absolute naturality follows directly from
`Scheme.comp_iterateFrobenius`.

Added the private proof import
`WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural`. Updated the item's node's
`proof`, `proof_deps`, and `proof_origin` to describe these existing APIs and the Lean argument.
All three existing signatures, all public imports, all definitions and existing docstrings
are unchanged. No consumer adaptation or change record is required.

Validation: the final item compiled through `lcompile.py` on the project server in 4.2 seconds
with exit code zero and no warnings on resumption (the earlier compile took 3.3 seconds). Static comparison confirms all three signatures are
unchanged, the only modified node fields are proof/proof_deps/proof_origin, and all Lean lines
fit within 100 characters.

## Proved and sorry left

Closed the three original holes, all attached to
`lem-pur-unrestricted-frobenius-factorization`:

- `WeilConjectures.FiniteFieldDatum.unrestricted_frobenius_projections`.
- `WeilConjectures.FiniteFieldDatum.unrestricted_frobenius_factorization`.
- `WeilConjectures.FiniteFieldDatum.unrestricted_frobenius_naturality`.

Holes left: zero. Holes added: zero. Split off: zero. The argument requires no finite-type,
quasi-compactness, separatedness or nonempty-scheme assumptions. Characteristic is expressed
by vanishing of p in global sections, so the empty scheme and zero section rings are covered.

## No longer needed

Removed the unused private proof imports `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`
and `Sheaf.AlgebraicGeometry.SchemeCharacteristic`. The corresponding direct proof dependencies
`def-weil-locally-ringed-space-morphism` and `def-weil-scheme-characteristic-p` are unnecessary:
characteristic inheritance and naturality are already proved by existing library APIs.
`lem-weil-finite-field-pow-card` is no longer a direct proof dependency; the existing descent
lemma already proves the required finite-base identity. This does not withdraw any of these
nodes or modules or claim they are globally unused.

The finite-type-only factorization theorem `absoluteFrobenius_factorization` in
`Sheaf.AlgebraicGeometry.FrobeniusFactorization`, its iterate machinery, and the affine-tensor
or sheaf-gluing approach are not needed. All remaining original dependencies are retained,
and the node explicitly records the used relative-Frobenius and coefficient-action APIs.
No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The plan's sectionwise naturality, characteristic
inheritance, finite-base descent and coefficient inverse calculations already have proved
library interfaces, so they need not be reconstructed. The final naturality step is shorter
using functoriality of `Over.pullback` than comparing the two projections again. These are
local simplifications of the stated argument and do not bypass a unit's route. The current
unit record has no realized statement or step assigned to a different required node here.

The first two compile requests received no answer from the busy server within 210 seconds.
Retries returned normal compiler diagnostics, after which the final compile passed.

Delivery tooling failed before a confirmed push. The first `deliver3.py` invocation crashed
with `subprocess.TimeoutExpired` while its sharedrepo worktree ran
`git checkout -q --detach origin/sheaf-dag` (600-second timeout). A retry waited for repository
coordination and was terminated with exit code 137 without a delivery result. Neither attempt
printed DELIVERED. The fully proved module and its clean 3.3-second compile remain preserved
in this sandbox.

On resumption, the source comparison again confirmed the same three theorem signatures,
zero remaining holes, and an exact match between proof-step uses and proof_deps.
Three resumed delivery attempts received no answer from the compile server within
210 seconds and pushed nothing. Each busy-server response was followed by a pause
before retrying; no proof or statement changes were needed.

A subsequent standalone lcompile.py check succeeded in 4.2 seconds with exit code zero
and no warnings. Delivery was then retried against the responsive compile service.

The exact appended axiom probe also compiled in a scratch diagnostic: SHEAF-PROBED 3,
3.3 seconds, no forbidden axioms. Its sole warning was the probe template own line width.
A later delivery retry waited for a slot and returned DELIVERY BUSY (all 24 delivery
slots occupied); the packet was retained and retried after a pause.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
