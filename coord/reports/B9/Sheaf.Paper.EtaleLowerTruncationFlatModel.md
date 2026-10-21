## What changed

Completed `AlgebraicGeometry.Scheme.etale_lower_truncation_flat_model` without changing
its statement or any public definition. The proof uses Mathlib's good truncation,
its quotient, and evaluation preserving kernels. The boundary isomorphism is obtained
by uniqueness of kernel limits, and its differential equation follows by cancellation
of the image monomorphism in the kernel inclusion's chain-map equation.

The public flat-quotient theorem has coincident site and coefficient universes,
whereas this item has site universes u+1 and u. A private categorical helper implements
the same argument at independent universes, reusing the existing proved private
`mono_bottom_of_tensor_rows` through a proof-only `import all`. It obtains flat
covers from the existing proved `hasFunctorialFlatResolution_kfi`, not from a new
existence assumption. The existing tensor comparison transfers flatness between
`IsFlatOnSite` and categorical flatness. All new helpers are private and proved.
The first clause of `etale_kflat_criteria` proves K-flatness of the kernel.

Updated the item's proof steps and proof dependencies to record these APIs. The
unit statement and route are unchanged. Added only proof imports; existing public
imports and all declaration signatures are preserved.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.etale_lower_truncation_flat_model`
(node `lem-kun-lower-truncation-flat-model`). Holes closed: 1. Holes added: 0.
No sorry remains in the delivered module. No statement is split off.

The generic arguments also include zero differentials, a zero coefficient ring,
and every integer cutoff. In particular a zero incoming differential makes the
boundary image zero, and the kernel-limit construction still gives the stated
inclusion and differential equations.

## No longer needed

Removed the proof-only import
`WeilConjectures.SixFunctors.Etale.Derived.Tensor` and the proof dependency
`def-kun-derived-tensor`. The two K-flat predicates here agree directly by
`isKFlatIndependentCoefficients_iff_isKFlat`, so no derived tensor construction or
signed-symmetry comparison is needed. This is pruning from this item's proof only;
no source-library declaration or module is removed.

The specialized public flat-quotient theorem is not applied because its universes
do not fit; its module remains needed for its proved generic tensor-row chase.
The other original proof dependencies remain in use. No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The proposed direct application of `flat_quotient_tensor_shortExact` does not fit
the site's independent universes. Its argument does fit, and is implemented by the
private helper with the existing independent-coefficient flat-cover and colimit
APIs. The planned signed-symmetry comparison at the final step is unnecessary:
the library already proves the required predicate identification definitionally.

The command-only change record is
`coord/changes/etale-lower-truncation-proof-commands.md`. Preflight requested it for
file-level universe/open/namespace changes. The downstream check found zero
consumer modules; no consumer adaptation or target-statement review is needed.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
