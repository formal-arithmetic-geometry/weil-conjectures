## What changed

Rebuilt the repair from the current quarantined module after the stale-base return of
33f05d00f2 (base e0d550965). The live Lean path is still absent and the rework row still
points to the preserved quarantine source. Comparing that source with the retained packet
confirmed that
both public amplitude declarations, their proofs, and the private helper signature are
preserved. Restored the module at its original Lean path and reapplied the removal of the
orphaned declaration-local binder and duplicate `R(f)^![A]` notation registration.

Additionally replaced the private `exists_uniform_proper_dimension_bound` proof by the
upstream theorem `exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace`,
specialized using `isAddTorsion_of_finite`. Its conclusion and hypotheses are identical.
Removed the now-unused public import of
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`. This is a substantive repair
against the current source, rather than an unchanged re-push. The overlong extraction
comment is wrapped at 100 characters. No source-library files change.

The rebuilt module compiled cleanly through lcompile.py on this retry (3.6 seconds).
Change record: coord/changes/W8-upper-shriek-sync-scopes.md.

## Proved and sorry left

Assigned compilation repair with zero existing holes: proved 0 of 0 sorries,
closed 0 holes, added 0 holes, split off 0. No sorry remains in the module.

The existing complete public proofs are preserved:

- `AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek_of_amplitude`
  (lem-etale-upper-shriek-bounded-below-from-amplitude).
- `AlgebraicGeometry.Etale.hasBoundedBelowUpperShrieks_of_amplitude`
  (lem-etale-upper-shrieks-bounded-below-from-amplitude).

The private `exists_uniform_proper_dimension_bound` remains fully proved, now directly
from the upstream proper-pushforward theorem. No new statements or nodes are introduced.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`.
The private helper no longer directly uses `exists_fibre_dimension_bound` or its node
`lem-fin-finite-type-fibre-dimension-bound`: upstream already proves its precise proper
pushforward conclusion. This is a local import removal; no module is withdrawn and no
claim is made that this dependency is globally unreachable. The public theorem proof
routes and their nodes are unchanged.

The duplicate notation registration and orphaned binder are obsolete extraction artifacts;
the retained upstream public import supplies the exceptional-pullback notation.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantine repair, not a missing-proof item. Its current source
is in quarantine/ rather than lean/, as coord/rework.tsv records. The upstream sync
extraction retained an orphaned local binder and duplicated upstream notation. Removing
them repairs the section-closing and ambiguous-notation errors.

The returned delivery 33f05d00f2 failed the landing freshness check against base e0d550965.
This repair rereads the current
quarantined source and retains all its mathematical declarations. It also uses the newly
available upstream proper-pushforward theorem to eliminate the obsolete duplicate proof
and its Sheaf import. Exact import and declaration-use searches in lean/ and quarantine/
find no consumers of this extracted module or its two public declarations. No consumer
adaptations, target changes, or DAG proof-route changes are needed.

The previous retry reported a delivery-tool lock wait and did not push. On this retry,
reconstructed the sandbox module directly from the current quarantine source and checked
that the resulting substantive repair matches the retained packet. Compilation and delivery
results below concern this retry.

Delivery-tool failure on this retry: two `deliver3.py --no-push` attempts stalled before
preflight in the import-cycle cache. Interrupting the first after over three minutes
located the wait at `deliver3.py:225` → `delivery_cache.py:140,73,52`, where `_load`
blocks in `fcntl.flock(lock, fcntl.LOCK_EX)`. The second attempt reproduced that wait;
its traceback also passed through `_load:66` (retry after the repository base changed).
Other delivery processes showed lock waits exceeding twenty minutes. Both attempts were
stopped; no successful dry run or push occurred. No launcher script, cache setting or lock
file was changed. The substantive repair and clean compilation remain in this sandbox.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
