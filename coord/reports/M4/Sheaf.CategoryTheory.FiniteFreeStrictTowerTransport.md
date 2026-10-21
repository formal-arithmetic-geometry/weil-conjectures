## What changed

Proved `SheafOfModules.finiteFreeStrictTowerTransport`, keeping every public statement and
non-theorem definition unchanged. All added helpers are proved private declarations in the
item module. Updated the item's DAG proof and proof dependencies to the argument actually
used. No other library module is changed. The change record
`coord/changes/M4-finite-free-strict-tower-proof-context.md` documents the additional
file-local proof elaboration commands required by the static preflight, with all downstream
users and their unchanged interfaces.

The proof constructs finite coordinates in the sectionwise module category by tensor
cancellation, localizes the exact scalar adjunction to prove preservation of derived products,
and constructs the limit comparison by the absolute right-derived universal property.
The actual short-exact-sequence boundary is transported using Mathlib's mapping-cone identities.
The three Roos squares then prove invertibility by the triangulated five lemma. The same
comparison satisfies the augmentation and entire-augmented-tower naturality equations.

Validation: the final proof compiled through `lcompile.py` in 30.0 seconds, without warnings.
`#print axioms SheafOfModules.finiteFreeStrictTowerTransport` lists only `propext`,
`Classical.choice`, and `Quot.sound`. The original public definitions, transport structure,
and theorem signature are preserved.

## Proved and sorry left

Closed the original hole in `SheafOfModules.finiteFreeStrictTowerTransport` (node
`lem-weil-pbc-finite-free-strict-tower-transport`): one hole closed, zero holes added,
zero holes left in the delivered Lean module. No statements are split off.

## No longer needed

Removed the following proof imports:

- `WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison`.
- `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Sheaf.Paper.RestrictionDerivedProducts`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective` as a direct import; the
  normalized tower construction still uses its result transitively.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses` as a direct import;
  injective-term resolutions are reused from the normalized tower construction.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`.
- Redundant `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` imports.

Removed these direct proof dependency edges:

- `lem-sfb-finite-free-scalar-coordinates`, `lem-sfb-internal-section-scalar-adjunction`,
  `det-def-sfb-ring-object-sheaf`, and `sk-def-sfb-change-of-scalars`: tensor cancellation
  and finite biproducts construct the sectionwise coordinates directly.
- `lem-weil-pbc-diagram-site-realization`: the existing functor-category Grothendieck
  instance and normalized tower construction supply the needed tower resolutions.
- `lem-weil-pbc-kinjective-hom-derived` and
  `lem-weil-pbc-right-adjoint-preserves-kinjective`: localized adjunctions prove derived
  product preservation, and the Roos triangle proves the limit comparison is invertible.
- `lem-sc-p1-split-ses-boundary-comparison`: mapping-cone identities prove exact-functor
  boundary compatibility for all short exact sequences without choosing splittings.
- `lem-weil-pbc-restriction-derived-products`: the ordinary adjunction and exact localization
  construct the derived adjunction directly, with independent coefficient universes.

Retained the Mathlib nodes for restriction of scalars, injective objects, exact derived
factorization, and SES triangles: the proof uses their actual declarations. In particular,
`def-pc-sheaf-restrict-scalars`, `def-sp-injective-resolutions`,
`lem-weil-pbc-exact-functor-derived-factorization`, and
`lem-weil-pbc-complex-ses-triangle` are not pruning claims. Bounded-below injective resolutions
are unnecessary, but the injective-object clause of their shared node is used.
Retained the K-injective product, evaluation, resolution, and normalized tower nodes used
by the reused construction.

These are dependency-edge pruning claims only; no source-library declaration or module is
removed. Deleted only obsolete entries of the item's `tool_uses`, preserving the order of
all retained approvals. The unit's realized statement and proof-step nodes remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned internal scalar-coordinate declarations do not directly match this item's
sectionwise independent-coefficient interface. The proved tensor-cancellation theorem avoids
that mismatch. The planned homotopy-equivalence argument is unnecessary: exact localized
adjunctions and finite-power self-adjointness prove the product claim, and the triangulated
five lemma proves the limit claim. No mathematical statement was weakened or disputed.
The edge cases rank zero, rank one, zero towers, and unbounded complexes are covered by
finite biproducts and the unbounded resolution API.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
