## What changed

Proved `HomotopyCategory.KInjectives.replacement_triangulated` without changing its
statement, the inclusion/localization shift instances, or any source-library declaration.
The right orthogonal inherits its triangulation from Mathlib. The upstream `Qh`
already has full and faithful instances. For essential surjectivity, represent a derived
object by a complex, apply the stated quasi-isomorphism-only resolution hypothesis,
and invert that quasi-isomorphism after localization.

For each supplied quasi-inverse `G`, `CategoryTheory.Equivalence.mk` adjointifies the
supplied unit and counit without changing the functors. `commShiftInverse` constructs
the compatible shift structure; `commShift_of_functor` and
`Equivalence.IsTriangulated.mk'` establish exactness of `G`. Composition with the
inclusion and the opposite-functor instance give the final two assertions. A proved
private helper `triangulated_inverse` performs this transport for an abstract equivalence;
this keeps the inverse shift structure explicit during elaboration. The existing named
unit, counit and shift-instance binders are retained verbatim; a declaration-scoped
`linter.unusedVariables` setting suppresses warnings for their implicit use.

## Proved and sorry left

Closed the one original hole:
`HomotopyCategory.KInjectives.replacement_triangulated`
(node `lem-sf-kinjective-replacement-triangulated`).
Holes closed: 1. Holes added: 0. Sorries left in the delivery: none.
The complete module compiled cleanly through `lcompile.py` in 2.8 seconds.
No decomposition and no new public statements; one proved private helper.

## No longer needed

Removed six redundant private imports, all already publicly imported transitively:

- `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`
- `Mathlib.CategoryTheory.Triangulated.Orthogonal`
- `Mathlib.CategoryTheory.Triangulated.Subcategory`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.CategoryTheory.Equivalence`

No mathematical dependency nodes or project modules are pruned. The proof follows
the existing node's route, using its Mathlib leaves and upstream full/faithful instances.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The supplied unit and counit need not satisfy the
triangle identities themselves: `CategoryTheory.Equivalence.mk` adjointifies them,
keeping both functors and the supplied counit. This realizes the plan's instruction
to choose an equivalence adjunction for each quasi-inverse. No hypothesis is added.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
