## What changed

Proved `WeilConjectures.point_derived_sections_tensor_descent`, preserving every public
signature and definition. Private helpers prove point-section exactness in independent
universes and identify the published derived scalar extension with the localization of
ordinary exact scalar extension, by uniqueness of left-derived functors. The comparison
has exactly the published counit normalization. The proof also constructs the localized
comparison and proves both uniqueness assertions, the formula for every resolution,
and roof naturality. The DAG records this shorter argument.

Change record: `coord/changes/Q3-point-derived-descent-proof-scope.md`. It records
the private section and local attributes flagged by the conservative interface check,
and the unchanged downstream consumer.

The complete proof compiled with `lcompile.py` in 29.9 seconds. The private scalar
comparison helpers precede the point-specific declarations and derived-category
instances, keeping inference in their minimal parameter scope. The published universal
pair is used directly; its final proof term is recorded for kernel conversion because
elaborator unification otherwise unfolds the large scalar witness. The delivery tool
checks the exact delivered file and its axioms before pushing.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.point_derived_sections_tensor_descent`
(`lem-weil-point-derived-sections-tensor-descent`).

Holes closed: 1. Holes added: 0. Sorries left in delivered Lean: 0.
No intermediate theorem was split off; every private helper is proved.

## No longer needed

Removed these direct proof imports and their corresponding direct node dependencies:

- `Sheaf.Paper.PointProEtaleSectionsExact`
  (`lem-weil-point-proetale-sections-exact`): its sheaf universe is too small; use the
  existing independent-universe geometric criterion and affine-evaluation API instead.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  (`lem-pc-kflat-resolution`): universal uniqueness constructs the exact comparison
  directly; the resolution equation then follows from naturality for every quasi-isomorphism.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
  (`lem-pur-left-derived-from-kflat-class`): the published scalar pair already carries
  its universal property, so no resolving-class construction is needed here.

Removed their obsolete `tool_uses` approvals. Also removed the redundant direct
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` import, already publicly
re-exported by the retained source-library import.

These are direct dependency cuts. No global module withdrawal is claimed: dependencies
of the published scalar construction and other consumers remain intact.

## Where the brief, the DAG or earlier work was wrong

The point-section exactness dependency has a smaller sheaf universe than the assigned
statement allows. Its geometric argument extends through the existing affine-evaluation
API, without changing any statement or definition. The original resolution-based plan
is longer than the universal-uniqueness argument. The final resolution equation follows
from naturality for every quasi-isomorphism, so its K-flat and flat-term hypotheses
need not be used by this proof.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
