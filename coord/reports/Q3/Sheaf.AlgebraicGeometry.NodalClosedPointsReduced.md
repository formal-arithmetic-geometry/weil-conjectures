## What changed

Proved `AlgebraicGeometry.isReduced_of_nodal_closed_points` in
`Sheaf.AlgebraicGeometry.NodalClosedPointsReduced`, with its signature unchanged.
Three proved private helpers identify the kernel of killing a power-series coordinate,
prove that coordinate prime, and deduce reducedness of the nodal quotient from radicality
of the product of the two distinct prime coordinates. Smooth closed points have reduced
stalks by the existing smooth-over-a-field theorem. At the other closed points, the
Noetherian stalk injects into its faithfully flat completion, whose reducedness is
transported along the given plain ring isomorphism. On each affine chart, maximal ideals
map to closed points by the Jacobson property. Their reduced stalks give reduced maximal
localizations, so Mathlib's local criterion and affine-cover gluing prove reducedness.
The node's proof and proof_origin now describe this realization. The listed dependencies
remain relevant, including the localization results underlying the Mathlib local criterion.

Added proof-only imports for power-series coordinate restriction, radical quotients,
reducedness as a local property, and prime elements. No public imports, definitions,
public signatures, source-library files, or unit routes changed.

Validation: the whole module compiles without errors or warnings through lcompile.py;
a temporary `#print axioms AlgebraicGeometry.isReduced_of_nodal_closed_points` reported
exactly `[propext, Classical.choice, Quot.sound]`. It was removed after checking.
The final compile after import removal took 5.6 seconds. The argument is vacuous for an
empty scheme, uses no quasi-compactness or dimension hypothesis, and works in every
field characteristic. The nodal-ring argument only needs that the coefficient field is
a domain; it does not use the algebraic-closedness assumption to strengthen any premise.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.isReduced_of_nodal_closed_points`
(blueprint: `lem-trf-nodal-points-reduced-algebraically-closed`).
Added 0 holes. Split off 0 statements. No sorry remains in the item or the delivery.
All three new private helpers are completely proved.

## No longer needed

Removed the direct proof imports `Mathlib.RingTheory.Localization.AtPrime.Basic` and
`Mathlib.RingTheory.Localization.Submodule`; the retained Noetherian and local-property
imports provide the required localization API. No project module or DAG dependency is
pruned: the revised proof still uses the listed geometric, completion, power-series,
and localization inputs. The separate fraction calculation transferring reducedness
from a closed-point stalk to an arbitrary generization is unnecessary, because the
existing maximal-localization criterion proves each affine chart reduced directly.
The product embedding of the nodal ring is also unnecessary: the same axis-restriction
homomorphisms prove coordinate primality and radicality of `(uv)`.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The six-step plan is mathematically valid. Mathlib already
packages its Noetherian-stalk calculation and supplies a shorter final local criterion.
The current blueprint unit has no realized step assigned to this auxiliary nodal result;
the implementation changes no unit statement or route. The Stacks reducedness paragraph
(curves.tex, lemma-facts-about-nodal-curves), completion faithful flatness (algebra.tex,
lemma-completion-faithfully-flat), and faithful-flat injectivity
(lemma-faithfully-flat-universally-injective) were read against the actual proof.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
