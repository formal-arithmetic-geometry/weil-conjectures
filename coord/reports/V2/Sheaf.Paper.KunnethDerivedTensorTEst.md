## What changed

Retained and repaired the proof candidate in
`Sheaf.Paper.KunnethDerivedTensorTEst`. The public theorem's signature is
unchanged. The argument uses bounded dévissage on the good upper truncations of
the second factor, a categorical K-flat representative of the first factor, and
exact filtered colimits. The categorical argument is a private helper in the
same module; `exactAt_colimit` proves the exact-colimit step from Mathlib.

Added the missing short-complex functor-equivalence import, supplied explicit
colimit arguments, and made the graded tensor existence proof pointwise to avoid
expensive instance unfolding. Updated the original node's proof and dependencies
and the Lean docstrings to describe this route. There are no new modules,
definitions, statement changes, or new nodes. The proof-scope commands and unchanged
consumer interfaces are recorded in
`coord/changes/V2-kunneth-derived-tensor-proof-scope.md`, as preflight requested.

A generic coefficient-category wrapper specializes the categorical argument using
exactly the symmetry and monoidal instances of `derivedTensor`. This avoids a costly
kernel comparison between the specialized ModuleCat instances. Explicit classical
choice from the start of the generic proof avoids repeated expensive instance
elaboration. The complete proof compiled without errors or warnings through
`lcompile.py` (`scratchpad/profile-full.log`, 10.4 seconds); the delivered file
removes the profiling options. No heartbeat or time limit is raised.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.derivedTensor_isZero_homology_of_torAmplitudeGE`
(node `lem-kun-derived-tensor-t-est`). The generic tensor estimate, its etale
specialization and the two exact-colimit helpers are proved privately in the
same module. Zero holes remain in the item; zero holes are added elsewhere.
No statement was split off.

## No longer needed

Removed `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution`: the argument does
not use `lem-kun-0f1m`, its arbitrary-pullback assertion, or scalar restriction
from independent-coefficient K-flat models. It uses the existing categorical
K-flat resolution in `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`.

Removed `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: no telescope,
pointed-neighbourhood colimit, or geometric stalk assertion is needed. The good
truncation component of `def-kun-truncations` remains used through Mathlib and the
source library's `CochainComplex.filtrationLE` API; the node remains a dependency.

Removed the redundant direct import
`WeilConjectures.AlgebraicGeometry.DerivedCategories`, already provided by the
public statement interface. Its node remains needed for the category and homology
comparisons. The total tensor and derived tensor definition nodes remain needed.
Other consumers may still need all removed imports; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old route has an interface mismatch: its lower-flat-model lemma supplies
independent-coefficient ringed-site K-flatness, whereas the categorical comparison
used by the recorded derived tensor requires categorical K-flatness after scalar
restriction. The alternative avoids that conversion and uses the original
Tor-amplitude hypothesis directly in bounded dévissage. The source-library
`DerivedCategory.isGE_obj_of_isGE` is already proved and supplies the finite
induction. No new unproved result is introduced. The unit has no realized
statement or proof steps, so its route is unchanged.

The earlier report's claimed pruning of the entire `def-kun-truncations` node
was too broad: the good-truncation component is still used. Only its direct
module import and unrelated telescope and stalk components are removed.

Preflight required a change record for the private proof's added universe and
namespace-opening commands. The record lists all transitive consumers; no public
signature or definition changed and no consumer adaptation is necessary.

A first dry run passed in full, but the subsequent push command stopped before
pushing because its repeated compile timed out. Moving `classical` to the start
of the generic proof reduced the profiled compile to 10.4 seconds; final checks
were then rerun on this revision.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
