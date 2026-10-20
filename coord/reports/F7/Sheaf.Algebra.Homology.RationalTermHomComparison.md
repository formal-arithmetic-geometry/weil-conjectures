## What changed

Proved `CategoryTheory.RationalTermHom.rational_term_hom_comparison` in
`Sheaf.Algebra.Homology.RationalTermHomComparison`, following the existing four-step
argument. The proof constructs the normalized degree-zero isomorphism, specializes
the existing bounded-free RHom model to finite free single complexes, extends the two
contravariant actions by tensor base change, and transfers invertibility and the
ordinary dual retraction along the given localized splitting.

Added only proved helpers in the same module. The projection API packages the
original chosen projections with their product and naturality laws and an equality
fixing them to that original family. This avoids repeatedly expanding a large
existential specification. Explicit universes and ordinary definitions prevent eager unfolding of the single
and Hom-complex wrappers. These repairs preserve the objects, arrows, normalization,
and theorem meaning. See `coord/changes/F7-rational-term-hom-projection-api.md`.

Added private proof imports for free-module sheaf duality, tensor base change, and
preadditive opposite categories. Updated the existing node's proof and dependencies;
the unit route and all statements are retained. No source-library module is edited.

## Proved and sorry left

Closed 1 of the original 1 holes:
`CategoryTheory.RationalTermHom.rational_term_hom_comparison`
(node `lem-sf-rational-term-hom-comparison`).

Holes added: 0. Holes left in this delivery: 0. Split-off statements: 0.
This proves the item from existing declared dependencies, including the bounded-free
RHom model; it does not claim that all dependencies are already axiom-free.

The proof treats rank zero via zero objects, makes no assumption that the localized
category is idempotent complete, and uses tensor induction rather than division by
the scalar. Consequently zero/unit scalars, a zero coefficient ring, and an empty
site require no additional hypotheses.

## No longer needed

Removed direct public imports:
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: no derived-Hom definition
  is used directly; the finite-free argument uses the stated bounded-free model.
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`: the argument works
  over an arbitrary coefficient ring and never uses a uniformizer.

Removed redundant private import
`WeilConjectures.Algebra.Homology.HomComplex`, already supplied by the public
`HomComplexProjections` import.

Removed `def-pur-derived-internal-hom` from this node's direct proof dependencies;
it remains a statement dependency and remains needed by the bounded-free model.
No module is withdrawn and no globally unused module is claimed. All other original
proof dependencies are used. The new direct dependencies on the Hom projections and
ordinary sheaf Hom record the normalization and coefficient-linearity calculations.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The original module was already close to
the compilation limit before adding a proof. Profiling exposed expensive elaboration
of the chosen product-family specification and repeated small-site instance searches.
The projection package records exactly the original chosen family and exposes its
already proved laws; it does not choose new mathematical data from an unproved mere
existence theorem. Its existence theorem is proved in this file.

The declared route suffices without a new result or bypassing a unit. The original
consumer `Sheaf.Paper.SitePerfectCoefficientDual` does not use the changed wrapper
names in its Lean statements or bodies and already imports the removed derived-Hom
module directly. No forced consumer adaptation is proposed.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
