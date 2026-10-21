## What changed

Prove `AlgebraicGeometry.ProEtale.derivedLocalClassEdgeComparison` without changing its
statement or any of its canonical constructions. The proof uses the adjunction description
of the local-class edge. Private helpers establish naturality, the derived-unit identity,
compatibility with composition, exact-right-adjoint normalization, and shift compatibility.
The section-command additions are recorded in
`coord/changes/derived-local-class-proof-sections.md`; the downstream scan found zero
current Lean importers, so no consumer adaptation is needed.
The bounded-below comparison is identified with the restriction of the unbounded derived
unit followed by the specified Leray isomorphism.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.derivedLocalClassEdgeComparison`
(node `lem-pur-derived-local-class-edge-comparison`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0. Split statements: 0.
All private helper theorems are proved. No other module is changed.

Validation: the complete module compiled through `lcompile.py` in 11.7 seconds with
no errors or warnings. All original public definition bodies and public imports are
retained verbatim; the original theorem statement is unchanged.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel`;
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`;
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`;
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`.

Removed direct proof dependencies:

- `lem-pur-ringed-site-grothendieck-abelian` and
  `lem-pe-injective-complex-slice-section-model` (also removed from `tool_uses`);
- `lem-sp-grothendieck-enough-injectives`,
  `lem-weil-pbc-dplus-injective-representative`,
  `lem-weil-pbc-kinjective-hom-derived`,
  `lem-weil-pbc-right-derived-plus-injective`, and
  `lem-sp-right-adjoint-preserves-injectives`;
- `def-weil-derived-cohomology-sheaves`, `def-weil-abstract-derived-category`, and
  `def-weil-pbc-site-comparison-morphism` as direct proof steps (their definitions remain
  in the public interfaces).

The slice-site section model and explicit injective-representative computations are
unnecessary for this proof. The existing canonical adjunctions, their normalization on
complexes, and short-complex homology perform those computations abstractly. No source
library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The planned cycle-level argument can be replaced by the functorial adjunction calculation.
The coefficient-sheaf categories used here are ordinary `Sheaf J (ModuleCat Λ)`, so the
separately encoded ringed-site slice-section model is not needed. All original public
statements and definitions are retained.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
