## What changed

Constructed the finite quotient transport directly, with no new public declarations.
The proof recovers a sheaf-of-rings isomorphism from the condensed monoid isomorphism,
evaluates at the singleton, and uses naturality to identify the action on sections.
The resulting ring equivalence preserves maximal-ideal powers. Quotient equivalences
therefore give continuous-function sheaf isomorphisms compatible with reductions and
transitions. Pullback, scalar restriction, and the monoidal unit comparison produce
exactly the module isomorphisms and both normalization identities in the statement.

All auxiliary constructions and lemmas are private and fully proved. Existing public
signatures, definitions, instances and public imports are unchanged. The node's proof,
proof dependencies and proof origin now describe this argument.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.smallIntegralFiniteQuotientTransport`.

Holes added: zero. Holes remaining in the delivered module: zero. No decomposition
or split-off theorem was needed. This count concerns this module, not the existing
proof dependencies elsewhere in the library.

## No longer needed

Removed the direct proof dependency `lem-sfb-integers-profinite-tower`: neither a
profinite inverse-limit identification nor quotient finiteness is used. The quotient
coset basis suffices for discreteness. Its replacement is
`lem-sfb-integers-coset-basis`, together with the existing absolute quotient lemma in
`det-pe-derived-nakayama-resolution`.

No existing public import was removed and no module was withdrawn. The removed DAG
edge does not claim that the profinite-tower module is globally unused.

## Where the brief, the DAG or earlier work was wrong

The statement and its mathematical plan are sound. The full profinite-tower theorem
was stronger than this proof needs. The obligation can be proved without another
split: no arbitrary witness is chosen from an unproved existence theorem, and no
coefficient construction or target meaning is changed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
