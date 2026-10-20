## What changed

Restored Sheaf.RingTheory.AuslanderBuchsbaum from the rework archive. Replaced the retired
GlobalDimension import with the canonical upstream module; used Mathlib's categorical
projective dimension in WithBot ℕ∞ and a proved comparison with the least natural Ext bound.
Retained the full original last-minors/resolution-depth/regular-quotient proof. The missing
depth-equivalence, zero-module-depth, and finite-free-depth helpers are now proved privately
under Sheaf because the upstream versions are private. No upstream declaration is edited.

Restored and adapted the unclaimed quarantined consumer
Sheaf.RingTheory.UniformPerfectQuotientBound in the same packet. Its two public statements
and public imports remain byte-identical to the archive. Updated both DAG proof records;
the item's Lean attachment is preserved and its equivalent signature is recorded.
The unit's statement and realized steps are preserved.

Both modules compile cleanly through lcompile.py --all; uncached checks took 2.8 seconds
per file. The unadapted consumer was compiled first and failed on the removed wrapper
and changed finite-dimension predicate; the adapted version compiles.

Change record: coord/changes/G2-auslander-buchsbaum-upstream-api-restoration.md.

## Proved and sorry left

This is a zero-hole assigned rework repair, not a new closure of an admitted theorem.
Holes closed: none (0). Holes added: none (0). Holes left in both delivered modules: none (0).

The complete proof of IsLocalRing.depth_eq_projectiveDimension_add_depth
(lem-weil-pbc-auslander-buchsbaum) is restored and checked against the current API.
The complete proofs of ModuleCat.exists_uniform_finite_projective_resolution_quotient_pow
and ModuleCat.uniform_finite_projective_resolution_quotient_pow_iff_tor_vanishing
(lem-weil-pbc-uniform-perfect-quotient-bound) are also restored. All seven private item
helpers are proved; no theorem is split off. The original quarantine modules also had zero
holes, so the honest net hole count is zero.

## No longer needed

Removed the item's import of retired Sheaf.RingTheory.CohenMacaulayDepthFirstTerm;
its upstream helpers are private, and the necessary results are proved locally.
Replaced the item's Sheaf.RingTheory.GlobalDimension and
Sheaf.RingTheory.BoundedProjectiveResolutionDimension imports with the canonical
upstream modules. No mathematical dependency of AuslanderBuchsbaum is pruned.

Removed UniformPerfectQuotientBound's proof import of
Sheaf.RingTheory.BoundedProjectiveResolutionDimension and its direct proof dependency
lem-weil-pbc-projective-resolution-ext-degree: the consumer now reads the categorical
bound directly from Auslander–Buchsbaum. That bridge remains needed by AuslanderBuchsbaum,
so no library module or declaration is withdrawn. No new nodes; no deleted files.

## Where the brief, the DAG or earlier work was wrong

The quarantined source assumed public helpers from a since-retired Sheaf copy and the
since-retired natural-number ModuleCat.projectiveDimension wrapper. The current upstream
finite-projective-dimension predicate takes an Ext-bound witness instead of an explicit
bounded-resolution witness. These are equivalent in the item's stated universe by the
existing bounded-resolution bridge. The new equality embeds depths into WithBot ℕ∞ to
match Mathlib's canonical projective dimension, without changing its mathematical meaning.

The recorded step 2 could no longer reuse public depth helpers: the adopted upstream
module makes them private. The updated node describes the proved local helpers. The
consumer now needs no direct bounded-resolution conversion. Searches through msearch
(LeanFinder, Loogle, grep) and both Lean roots found no existing Auslander–Buchsbaum depth
formula; the similarly named upstream theorem concerns unique factorization instead.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
