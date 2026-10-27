## What changed

Proved `AlgebraicGeometry.Etale.etale_pullback_twist_tor_window` in
`Sheaf.AlgebraicGeometry.EtalePullbackTwistTorWindow`, preserving its complete signature
and the three existing definitions. Added private proved helpers for transport of
constructible cohomology and Tor amplitude and for the canonical model isomorphism.
Added proof imports for the arbitrary-line theorem, direct flat-model existence,
constructibility comparison, the source Tor-amplitude equivalence and derived shifts.
Updated the item node to match this route. The existing canonical sheaf monoidal
instance is activated locally after the three unchanged public definitions. The
conservative preflight classifies this command as an interface change; its record is
`coord/changes/Q8-pullback-twist-proof-local-tensor.md`. There are zero downstream
Lean modules and no consumer adaptation is required.

The proof establishes Noetherianity from the finite-type structure maps and proves
invertibility of ell^n in every target stalk by mapping its inverse from k. It converts
the finite Tate line's localized-site cover to the pullback cover expected by the line
model theorem. It inverts the canonical comparison, extracts the shift, and transports
all seven requested properties. The final clause obtains a representative directly and
uses the zero twist, zero shift, single-functor unit comparison and right unitor.

The edge cases n=0, c=0, either scheme empty, a=b and negative s are retained: the
invertibility proof uses powers of a nonzero field element, including the zeroth power;
there is no nonemptiness hypothesis on the cover; the interval shift is a-s,b-s; and
no flatness of R over ZMod (ell^n) is assumed. Source read: Stacks etale-cohomology.tex,
lemma-when-ctf and lemma-pullback-ctf; current blueprint exceptional comparison Charts.

## Proved and sorry left

Closed the sole hole in `AlgebraicGeometry.Etale.etale_pullback_twist_tor_window`
(node `lem-sp-etale-pullback-twist-tor-window`): proved 1 of 1. No holes added or split
off; no sorry remains in the delivered Lean file. The proof uses the already stated
`AlgebraicGeometry.Etale.etale_pullback_line_flat_model`, whose existing hole remains
in its own module; that dependency is not changed by this packet.

## No longer needed

Removed the direct proof import `Mathlib.Algebra.Homology.BifunctorShift`; the existing
derived shift API supplies the needed comparison and already depends on that machinery.
The shift node remains a dependency because this API localizes its signed comparisons.

The route no longer needs `lem-sp-etale-scalar-flat-model` or its module
`Sheaf.AlgebraicGeometry.EtaleScalarFlatModel`. Only existence of a representative is
needed, supplied directly by `lem-sf-etale-flat-constructible` in
`Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`. Removed the scalar-model node
from this item's proof dependencies. This is pruning of this route, not withdrawal of
the scalar-model module: other library consumers may still need it.

## Where the brief, the DAG or earlier work was wrong

The DAG's identity-scalar-extension step is unnecessary; direct model existence has
exactly the required interface. The line-model theorem exposes invertibility of the
canonical derived-to-model comparison, rather than an arbitrary representing
isomorphism. The proof constructs the requested inverse and then moves the shift of
the second factor to the whole derived tensor. No statement or definition repair was
needed. The local instance activation is documented in the change record named above. The unit route is unchanged.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
