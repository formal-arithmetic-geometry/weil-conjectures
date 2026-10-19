## What changed

Proved all four original auxiliary theorems in
`Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`.
Local bijectivity of the forgotten ring-sheafification unit follows from Mathlib's
equalizer- and image-sieve lemmas. Exactness follows from sectionwise preservation
by constant module presheaves and exact module sheafification. Forgetting
commutativity preserves sheafification equivalences by the local-bijectivity criterion.

For coefficient transport, proved compatibility of the canonical ring isomorphism
with the two units. Private helpers construct a linear sheafification unit after
coefficient restriction, extend it by the module-sheafification adjunction, and show
that the resulting comparison becomes the identity on underlying abelian sheaves.
Faithfulness supplies naturality and reflection of isomorphisms supplies invertibility.
The module actions are constructed by the existing sheafification functors; no new
object is selected from an unproved existence theorem. Updated the existing node's
proof to record these arguments. All public signatures, definitions and imports stay
as in the current source.

## Proved and sorry left

Closed four of four original holes, all attached to node
`def-sfb-site-derived-constant-module-functor`:

- `CategoryTheory.realizationRingUnit_locallyBijective`.
- `CategoryTheory.commutativeSiteConstantModuleFunctor_exact`.
- `CategoryTheory.realization_forget_preservesSheafification`.
- `CategoryTheory.commutativeSiteConstantModuleFunctor_transport`.

No sorry remains in the item. No holes added or split off. All private helpers are proved.
The resumed session compiled the complete item without warnings through lcompile.py
in 56.9 seconds, within the 60-second limit. The current dry run also passed compilation,
the axiom probe and preflight. The retained profiler run identified
kernel checking and the private-module linter on the concrete transport theorem
as the main costs. The current-source consumer check found 424 downstream modules
and no users of the new private helpers.

## No longer needed

No imports, nodes or modules are removed. There are no declared proof dependencies
to prune. The original constant-module functor remains the transport target.
The retained attempt's removal of the public KFlat import has been undone to preserve
the published import interface used by other modules. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node was a definition node with an empty proof plan despite four auxiliary proof
obligations in its Lean attachment. Its proof field now records their actual proofs.
The retained attempt left the transport comparison open. Separating its initial
linear map from the adjunction extension, and abstracting the sheafification instances
in the private comparison lemmas, makes the complete argument compile.

The resumed dry run passed compilation and the axiom probe, then required a change
record for the new scoped variable and local irreducibility commands. Their scope and
lack of downstream effect are documented in
`coord/changes/N2-constant-module-transport-local-commands.md`.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
