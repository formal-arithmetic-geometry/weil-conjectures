## What changed

Proved `WeilConjectures.integralTowerInverseImageUnit_existsUnique`. The actual
sequence direct image is an equivalence: its site functor is the product of the
isomorphism-induced site equivalence with the identity, and its coefficient map
is invertible. The recorded adjunction unit, followed by the canonical comma
restriction, therefore gives the required isomorphism at each quotient level.
The completed coefficient projection equation supplies scalar compatibility.

The level isomorphisms commute with every quotient transition and are natural in
the sequence module. A generic evaluation construction assembles the entire tower.
The specified section formula determines it uniquely, since the recorded casts
and the inverse-image section maps are surjective.

Added proof imports of `Mathlib.CategoryTheory.Sites.CoverLifting` and
`Mathlib.CategoryTheory.Adjunction.FullyFaithful`, and proved private helpers.
The three new private continuity helpers are registered only as local instances.
Existing public signatures, definitions, imports and declaration docstrings are
unchanged. Updated the node proof, dependencies and origin. No source-library file
is changed. The proof context and consumer review are documented in
`coord/changes/G4-integral-tower-unit-proof-context.md`.

Searches: LeanFinder located module pullback and composition APIs; Loogle had no
indexed hit for `Adjunction.leftAdjointUniq`; source and Mathlib searches located
`pushforwardPushforwardEquivalence` and its section formulas. The existing
restriction/evaluation and coefficient-map APIs suffice; no new public model is
introduced.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.integralTowerInverseImageUnit_existsUnique`
(node `def-trf-integral-tower-inverse-image-unit`). Added zero holes; zero remain
in the item module. No statement is split off and no new module is introduced.

The complete candidate compiled through `lcompile.py` in 27.5 seconds, including
kernel checking, with a diagnostic heartbeat budget of 50,000. The delivered
source removes the diagnostic options and uses the project compiler settings.
The normal-settings delivery compile also passed in 29.8 seconds, with one unused
section-variable warning. The final source omits that unused assumption from the
private transition lemma; the delivery tool verifies this source during preflight.

## No longer needed

None. The original node has no proof dependencies to prune. All existing public
imports remain needed by its definitions and interfaces. No node or module is
withdrawn; the proof uses the existing site, sequence, coefficient restriction,
realization and inverse-image APIs, together with proved Mathlib results.

## Where the brief, the DAG or earlier work was wrong

The original node has an empty proof plan despite its named existence and
uniqueness hole. Its declaration docstring supplies the construction, which this
proof makes explicit. The sequence pullback is a chosen left adjoint, so its unit
is proved invertible through the actual direct-image equivalence.

Concrete simplification of the base-change functor on identity arrows unfolded
scheme pullback constructions and exhausted kernel resources. The final proof
uses a product-functor equation proved for an arbitrary functor, together with
generic section and evaluation APIs; it preserves the actual site functor and
the specified adjunction unit.

Preflight required a change record for the extra proof context. The record lists
all 116 transitive consumers; none requires adaptation. The private continuity
helpers now use local instance registrations.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
