## What changed

Prove `WeilConjectures.compactSupportFiniteCoefficientPresentation` without changing its
statement. All Lean changes are in the assigned module; the assigned node's proof and
proof dependencies follow the new proof. All new helpers are private and proved.

The ordinary comparison is constructed by identity on section carriers. Naturality of
constant-section ring maps follows from the sheafification adjunction, then `NatTrans.ofOpSequence`
extends successor compatibility along the actual quotient sequence to every `n ≤ m`.

For the derived comparison, transport to the coefficient-sized `AsSmall` site models.
The existing ringed-topos coefficient acyclicity theorem applies there; an exact module
equivalence transports this back to the original sites. Apply the existing normalized
square construction and derive its arbitrary-resolution formula by naturality and
cancellation. Restriction is never assumed to preserve K-injectivity.

The section identities, additive structures, and categorical transports are proved
for abstract ring sheaves before specialization. This avoids kernel reduction of
large concrete coefficient constructions. The complete proof compiled through
`lcompile.py` in 41.6 seconds with profiling enabled; profiling and check commands
were removed for delivery.

Only proof imports are added: `import all Sheaf.CategoryTheory.DerivedExactSquareCoherence`,
`import all Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact`, and
`import Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage`. The `all` imports
reuse existing proved private transport and derived-square helpers.

## Proved and sorry left

Closed: `WeilConjectures.compactSupportFiniteCoefficientPresentation`
(node `lem-trf-compact-support-finite-coefficient-presentation`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the item: 0. No new statement
with `sorry` is introduced. Existing dependencies retain their own proof obligations.

## No longer needed

No original import is removed: the original public import supplies the unchanged
statement's objects. The proof no longer uses the planned dependency
`prop-weil-pbc-proetale-constant-ring-map` (`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`):
ordinary naturality follows directly from sheafification, without an inverse-ring-map
isomorphism. It also does not use `lem-coef-semilinear-derived-sections`
(`Sheaf.Paper.SemilinearDerivedSections`): the existing generic ringed-topos acyclicity
and normalized derived-square calculus suffice. These nodes are removed from this
node's proof dependencies; other consumers and the original public interface retain
their dependencies. No module is withdrawn, and no unit route is bypassed.

The older fixed-universe `proEtaleDerivedDirectImage_restrictScalars` already contains
the required normalization, but cannot be directly specialized: it ties the scheme
and coefficient universes together. The present transport preserves their independence.

## Where the brief, the DAG or earlier work was wrong

The node's former proof suggested specializing the entire semilinear system calculus.
That is unnecessary here: this is an ordinary finite coefficient square, and the
existing ringed-topos coefficient-acyclicity helper provides precisely its difficult
input. The statement and the unit's mathematical route are unchanged.

Mathlib searches used the prescribed `msearch.py` interfaces: Lean Finder for exact
restriction and derived module direct image, Loogle for `SheafOfModules.pushforwardComp`,
and grep for restriction/right-derived comparison. They found generic ordinary
pushforward comparisons, but no independent-universe normalized specialization.

Edge cases: identity quotient (`n=m`) is included by naturality at an identity. The
construction uses no points, nonemptiness, or properness assumption, and applies to
empty schemes and all scheme morphisms. Every resolution is arbitrary as required.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
