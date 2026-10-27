## What changed

Proved `DerivedCategory.exactAdjoint_classicalCounitComparison` without changing its
signature or public imports. Disabled the unused-variable linter locally for
the three stronger hypotheses retained in the public interface. Added the private proof import
`Mathlib.CategoryTheory.Adjunction.FullyFaithful` for `Adjunction.inv_map_unit`.

The proof follows the existing six-step DAG plan. Orthogonality makes both the
transpose of an arbitrary map and the transpose of zero vanish; injectivity of
the adjunction equivalence therefore proves the lower bound without assuming
additivity. The unit restricted to `Plus AX` gives `r`; whiskering and canonical
right-adjoint uniqueness give `beta` and `alpha`. The bounded-below lift of the
source defines `t` as a composite of natural transformations. The final identity
uses the actual-unit triangle identity, counit naturality, right-adjoint counit
normalization, and comparison naturality.

## Proved and sorry left

Closed: `DerivedCategory.exactAdjoint_classicalCounitComparison`
(node `lem-pur-exact-adjoint-classical-counit-comparison`), the item's sole hole.

Holes closed: 1. Holes added: 0. Sorries left: none. No statements split off.

Validation: server compilation succeeded without warnings (final file: 3.7 s).
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The additional proof import passes the import-cycle check.

## No longer needed

None. All original imports remain necessary, and all four existing proof
dependencies are used through their Mathlib declarations. No nodes or modules
are withdrawn. The unit route and the DAG proof remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Existing library right-adjoint bound results
require additivity; the DAG's singleton argument avoids that extra hypothesis.
The latest blueprint locates `sk-prop-a1` under `sec-six-functors-basics` rather
than the historical `sec-smooth-purity` directory; its first localization triangle
is the same route served here. No definition or statement was changed and no
consumer adaptation was necessary.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
