## What changed

Proved `CategoryTheory.CondensedBar.bar_augmentation_columns_imply_rows` in
`Sheaf.CategoryTheory.BarAugmentationRowComparison` without changing its statement.
For each fixed column, the source of the assumed quasi-isomorphism has zero terms in
positive degrees, because the bar evaluation functor is additive and therefore preserves
zero objects. Mathlib's `exactAt_iff_of_quasiIsoAt` transfers exactness to the resolution
column. Thus the corresponding term of the positive vertical-cohomology row is zero;
`HomologicalComplex.ExactAt.of_isZero` and `ExactAt.isZero_homology` then give the required
horizontal homology vanishing. This is precisely step 7 of the existing node, with no
spectral sequence or extra exactness assumption. The argument includes horizontal degree
zero and every strictly positive vertical degree.

Removed three unused private proof imports. Public imports, definitions, declaration
signatures and the unit route are unchanged. The larger comparison theorem is untouched.

Validation: the final file compiled through `lcompile.py` in 19.5 seconds, with no
compiler errors or warnings.

## Proved and sorry left

Closed 1 of the item's 2 original holes:
`CategoryTheory.CondensedBar.bar_augmentation_columns_imply_rows`.
Added 0 holes and split off 0 statements.

The sole remaining hole is
`CategoryTheory.CondensedBar.bar_augmentation_row_comparison`, with existing node
`lem-sfb-bar-augmentation-row-comparison`. Its existing source and eight-step proof remain
in its docstring and node. This is a partial delivery of the multi-theorem module, not a
claimed proof of the larger comparison theorem.

## No longer needed

Removed private imports:

- `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`
- `Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality`
- `Mathlib.CategoryTheory.Adjunction.Limits`

None is used by the completed column-to-row proof. No DAG node or module is asserted to
be globally unnecessary: the unfinished comparison theorem retains its existing proof
plan and dependencies, including the row-collapse and derived-naturality nodes. No
module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No correction was needed for the proved implication. In the displayed proof of step 7,
“the zero complex” means a complex all of whose terms are zero objects, not a judgmental
equality to a selected zero complex. The termwise exactness argument avoids choosing such
an equality. The original theorem's strictly positive vertical-degree hypothesis is
necessary and is used through `Nat.ne_of_gt`.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
