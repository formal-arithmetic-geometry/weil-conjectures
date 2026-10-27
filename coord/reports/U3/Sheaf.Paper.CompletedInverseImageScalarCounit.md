## What changed

Completed both proofs in `Sheaf.Paper.CompletedInverseImageScalarCounit` without changing
any public statement, definition, or public import. The coefficient counit is constructed
from the specified sectionwise transport: constant-sheaf uniqueness gives its finite
coefficient normalization, and limit projections give the completed normalization.
Mathlib's module pushforward composition, congruence, and identity isomorphisms then
construct the required module counit, with uniqueness checked on every section.

The scalar identity is proved on generators using the normalized ordinary scalar
adjunction, transported to the derived category through its homotopy localization, and
then conjugated by the specified completion comparisons. All auxiliary lemmas are private
and proved. Added private proof imports of
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`,
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`, and
`Mathlib.CategoryTheory.Localization.Predicate`. Updated the existing node's proof route.

## Proved and sorry left

Closed both original holes:

- `WeilConjectures.integralInverseImageCounit_existsUnique`.
- `WeilConjectures.completedInverseImage_scalarCounit`.

Two holes closed; zero holes added, zero split off, and zero holes remain in the item.
Existing stated dependencies are used as permitted by stage 3; their proofs are not
replaced or weakened by this delivery.

## No longer needed

Removed these private imports from the item:

- `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (already available through
  the required derived-mate API).

The proof does not use the planned finite-free-coordinate argument or the comparison
with an abstract left derived functor: ordinary scalar extension already has the exact
instances and the termwise derived model used in the statement. Removed the obsolete
proof dependencies/approved tool uses `lem-sfb-finite-free-scalar-coordinates` and
`lem-weil-pbc-exact-functor-derived-functor`. The finite-free completed scalar comparison
is retained as a statement dependency and public import, but its finite-coordinate proof
is not used; its separate proof dependency/tool-use entry is removed. No module is
withdrawn, and no claim is made that other consumers no longer need these modules.

Also removed direct proof-dependency entries `def-weil-proetale-inverse-image`,
`def-weil-sheaf-of-modules-category`, and `def-pur-sheaf-tensor-product`. Their public
interfaces remain available through the unchanged statement imports; the proof uses the
explicit inverse-image comparison and normalized ordinary scalar adjunction APIs instead
of constructing a general pullback or a tensor sheaf from scratch.

## Where the brief, the DAG or earlier work was wrong

The original proof plan redundantly reproved exactness of the ordinary scalar functor.
Its existing exactness instances suffice. Equality on sections of the tensor sheaf is
established through the adjunction unit and its injective Hom equivalence, not by
identifying sheaf tensor sections with a sectionwise tensor product. No statement repair
or additional hypothesis was needed. The identity-isomorphism, zero-module, and
identity-coefficient cases are included in the formulas without exceptional choices.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
