## What changed

In `Sheaf.Paper.FiniteFreeCompactComposition`, proved quotient-transition compatibility,
constructed the uniquely section-normalized ordinary pushforward restriction isomorphism,
and proved bounded-below etale origin for every universal coefficient tensor presentation.
The last proof reflects the input Tor interval to an etale witness, bounds its scalar
extension using the scalar/tensor comparison, and identifies its pro-etale realization
with the supplied presentation by the two universal properties.

Added two proved private helpers (constant-direct-image naturality and the generic
restriction/pushforward composition isomorphism) and a private local smallness instance.
Local irreducibility settings keep Lean from unfolding derived-functor constructions.
All existing public signatures, definitions and public imports are unchanged. The node
records the implemented preliminary route and retains its original assembly steps.

## Proved and sorry left

Closed 3 of the original 8 holes, all in namespace
`WeilConjectures.FiniteFreeCompactComposition`:

- `coefficientInclusion_commutes`.
- `pushRestriction_existsUnique`.
- `finiteTensorOrigin`.

Added 0 holes; split off 0 statements. Five original holes remain unchanged, all owned
by `lem-coef-finite-free-compact-composition`:

- `pullRestrictionInv_isIso`.
- `pushRestriction_isIso`.
- `openRestrictionInv_isIso`.
- `finiteLevelComposition`.
- `systemComposition`.

This is a partial proof delivery, not a decomposition. The closed declarations use the
library's existing theorem interfaces; this does not claim that their entire dependency
closure is free of `sorry`. The item compiled successfully; delivery runs the final
compile and preflight checks.

## No longer needed

No original import, node or module is withdrawn. The five remaining holes still need
the original composition and system-restriction dependencies, so those dependencies
are retained in the node. The proof of `finiteTensorOrigin` needs no reduced integer-ring
basis or finite-sum calculation: finite Tor amplitude already bounds scalar extension
below. This prunes that local proof step, not the finite-free results needed elsewhere.

The trial private imports
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison` and
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients` were removed: both
APIs are already publicly reachable through the original coefficient-extension import.
No duplicate imports remain.

## Where the brief, the DAG or earlier work was wrong

The previous finiteTensorOrigin proof sketch used finite freeness for boundedness.
Its conclusion is only bounded-below etale origin, for which the input's finite Tor
interval and the scalar/tensor comparison suffice. Its docstring and the node now
record that shorter argument. No statement or definition repair was necessary.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
