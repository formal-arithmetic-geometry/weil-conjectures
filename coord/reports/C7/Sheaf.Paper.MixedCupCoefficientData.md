## What changed

Proved `change_domain` and `tensor_domain` in
`Sheaf.Paper.MixedCupCoefficientData`, retaining every existing signature and definition.
Added proved private helpers for integral membership and transport of finite membership
along isomorphisms. Added private proof imports of `IntegralResidueTor`,
`DirectImagesConstructible`, `ClosedScalarDomains`, `FiniteCompactSupportScalarTransport`,
and `ProEtaleBoundedConstructibleTriangulated`. Updated the existing definition node's
proof plan and proof dependencies to match the Lean argument.

Finite scalar preservation uses the existing arbitrary-ring-map theorem
`closedScalarDomains_scalar`, transported through the canonical intrinsic realization
and `realizationScalarIso`. Reduction reads the uniform interval and constructible
reductions from the input. Integral scalar and tensor outputs are constructible by their
codomain types; `integral_residue_tor` supplies finite Tor. Passage composition uses
induction, with the first result as the input to the second.

## Proved and sorry left

Closed both original holes:
- `WeilConjectures.MixedCupCoefficientChange.change_domain`.
- `WeilConjectures.MixedCupCoefficientChange.tensor_domain`.

No sorry remains in this module. No holes were added or split off. These proofs use
existing library declarations; their transitive proof obligations remain owned by their
existing nodes. The new helpers are fully proved and private.

## No longer needed

No existing imports, modules or nodes are withdrawn. The node previously had no proof
dependencies. The docstring's suggested `finiteCompactSupportDomains` route is unnecessary:
`closedScalarDomains_scalar` already supplies the finite scalar domain result. The integral
completed-tensor reduction/interval-addition argument is unnecessary here because the
recorded tensor output is constructible and `integral_residue_tor` gives the full integral
finite-Tor condition. All statement dependencies and the unit route are retained.

## Where the brief, the DAG or earlier work was wrong

The existing node had no numbered proof steps for its two membership theorems. Added the
actual assembly argument. No false statement or definition repair was needed. In particular,
finite coefficient maps are arbitrary unital maps, and the proof adds no flatness condition.
The integral residue theorem requires invertibility of the coefficient prime on the scheme;
this is proved by mapping its unit in the base field to each residue field.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
