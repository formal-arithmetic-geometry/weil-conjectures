## What changed

Proved three theorems in `Sheaf.Paper.ProperOpenCoefficientMate` without changing
any existing public signature or definition:

- Coefficient naturality follows by composing the existing direct-image map's
  naturality with the open scalar and proper/open natural isomorphisms.
- Site naturality uses a private natural isomorphism transporting the unbounded
  proper/open isomorphism through the fully faithful bounded-below inclusion.
  Its component is proved equal to the existing pointwise definition.
- The site square follows from the open-counit normalization of
  `compactSupportSiteComparison_open_counits`, specialized to an open immersion.
  A proved private categorical lemma transports open adjuncts through that
  normalization. Another proved private lemma identifies the bounded-below
  restriction inverse with the open transpose of the existing interchange.

Updated the existing node's proof, proof dependencies and proof origin to record
these arguments. Added one proof-only import,
`Sheaf.AlgebraicGeometry.CompactSupportSiteComparisonOpen`.
Removed the unused proof imports of
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence` and
`Mathlib.CategoryTheory.Adjunction.Mates`.

Validation after resuming: the complete retained module compiled through
`lcompile.py` against current server dependencies in 31.3 seconds, with exit code 0.
All existing public signatures and definitions match the current repository;
the only remaining `sorry` is the coefficient-square theorem named below.

## Proved and sorry left

Closed 3 of the 4 existing holes:

- `AlgebraicGeometry.Etale.properOpen_coefficient_mate_naturality`.
- `AlgebraicGeometry.ProEtale.properOpen_site_mate`.
- `AlgebraicGeometry.ProEtale.properOpen_site_mate_naturality`.

One existing hole remains, with its original source and complete proof in words
under node `lem-sp-proper-open-coefficient-mate`:

- `AlgebraicGeometry.Etale.properOpen_coefficient_mate`.

Added holes: none. Split-offs: none. The coefficient square still needs the
normalized scalar/pullback mate rectangle; the naturality and site arguments
are complete independently of that equality.

## No longer needed

Removed the proof imports
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence` and
`Mathlib.CategoryTheory.Adjunction.Mates`: the new site proof does not use the
general pullback-coherence theorem or the generic mate-pasting theorem.
The node's proof dependency `lem-weil-pbc-comparison-pullback` is dropped;
the site proof instead uses the named fixed pullback comparison already present
in the definitions, together with the open-counit normalization.
No whole module is pruned. The coefficient square retains its
recorded normalized mate argument and associated dependencies. The site square
uses the compact-support open-counit normalization and an elementary adjunction
calculation instead of the former general mate-pasting and tensor argument.
The node's site step therefore drops those uses. Both naturality proofs use
composition of natural transformations and do not use either square equality
or the boundedness hypotheses.

The added dependency `lem-amb-compact-support-site-comparison-open` is used as a
tool for its open-evaluation counit normalization, specialized to the canonical
compactification of an open immersion. This replaces only a node-level transport
calculation and keeps the unit's coefficient and site compatibility route.

## Where the brief, the DAG or earlier work was wrong

The inherited report described only two closed holes and was stale relative to
the inherited in-progress site proof. The required dry run found an overly
specific rewrite in its bounded-below restriction helper. Repaired it using
explicit naturality of the unbounded open unit and the actual compatibility map.
The pointwise bounded-below interchange did not directly expose naturality;
its existing definition is the component of a natural isomorphism obtained
by fully faithful cancellation. No statement or mathematical source error
was found. All existing statements and public definitions are retained.

The resumed delivery dry run also classified an added top-level namespace opening
and elaboration option as public command changes. Both were removed; helper names
are qualified explicitly, preserving the original top-level command interface.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
