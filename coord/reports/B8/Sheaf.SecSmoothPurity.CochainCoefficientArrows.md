## What changed

Proved four of the five original obligations in
`lean/Sheaf/SecSmoothPurity/CochainCoefficientArrows.lean`, without changing any
existing signature, definition, visibility, or import.

`extensionFunctor_laws` follows from the sectionwise extension functor's laws and
functoriality of module sheafification. `extensionFunctor_mapPresentation` simplifies
the two identity transports. `extensionAdjunction_existsUnique` constructs the Hom
bijection using the sectionwise extension/restriction adjunction and module
sheafification. Its unit has the specified formula; `Adjunction.ext` proves
uniqueness from that formula. The private proof helpers generalize the existing
construction in `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` to the
independent site and coefficient universes of the assigned declaration.

`restrictionTensorComponent_comm` follows by transposing the tensor comparison's
naturality through the scalar-extension adjunction, using counit naturality, then
summing over bidegrees. A proved private generic lemma establishes the signed total
calculation for an arbitrary natural lax tensor map. It checks the two differential
summands separately and preserves the integer sign by additivity. The proof follows
the summand calculation of `tensorPullbackTotalComponent_comm`, without requiring
an invertible restriction tensor map.

The static command-surface check also requires the explanatory change record
`coord/changes/cochain-coefficient-arrows-proof-surface.md`. Its private/scoped
commands do not change any downstream declaration. The checked direct consumer is
`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`; it needs no adaptation.

Fresh single-file validation against the current published build with the required
`lcompile.py` completed without errors or warnings (23.0 seconds, 2026-10-19).
The retained sandbox was compared against the current source: all existing public
signatures, definition bodies, visibility, and imports are unchanged. The five
original obligations and their node attachment are still current.

## Proved and sorry left

Original holes: five. Holes closed: four, by declaration name:

- `CategoryTheory.CochainPullback.extensionFunctor_laws`.
- `CategoryTheory.CochainPullback.extensionAdjunction_existsUnique`.
- `CategoryTheory.CochainPullback.extensionFunctor_mapPresentation`.
- `CategoryTheory.CochainPullback.restrictionTensorComponent_comm`.

One original hole remains unchanged:
`CategoryTheory.CochainPullback.scalarAssociation_existsUnique`
(node `def-pur-cochain-coefficient-arrows`). It still needs the construction of the
normalized scalar-association isomorphism through algebraic inverse image and
sheafification, together with its generator-based uniqueness proof.

No holes added; no decomposition or split-offs. Every private helper is proved.

## No longer needed

None. No imports were added or removed, and no declared dependency, node, or module
has become unnecessary. The assigned definition node has no proof-dependency plan
to prune. Its existing statement dependencies remain necessary for the definitions.

## Where the brief, the DAG or earlier work was wrong

The assigned node is a definition node with an empty `proof` and `proof_deps`,
although its module contains five named proof obligations. Their existing
docstrings supply the mathematical proof plans. The existing scalar-extension
adjunction implementation is private and has more restrictive universes; it cannot
be applied verbatim to the assigned independently sized sites. The delivery adapts
that proved construction in private proof helpers, preserving the public API.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
