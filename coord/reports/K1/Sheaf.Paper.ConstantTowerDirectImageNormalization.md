## What changed

Filled all three assigned proof holes in
`Sheaf.Paper.ConstantTowerDirectImageNormalization`.

The ordinary comparison is constructed from invertible mates of coefficient
restriction squares; its tensor formula proves compatibility with the quotient
transitions and uniqueness. Adapted flat resolutions and localization on a resolving
class construct the derived comparison with its specified counit normalization.

The final theorem follows from the canonical right-derived unit equations, exact
square coherence, and adjunction mates. This proves the K-injective representative,
evaluation, inverse-limit, and augmentation/projection identities for the exact maps
in the original statement.

Only the assigned Lean module changes. The constant-sheaf functor is kept folded
locally during elaboration, together with the K-flat predicate; its construction and exported interface stay unchanged.

The private ordinary tensor-unit and quotient-transition implementations now use
the existing normalized scalar adjunction. This removes repeated sheafification
transports; their original section formulas remain proved. The tensor-generator
extensionality proof uses the direct sheafification universal property. Private
proved equations for scalar extension keep its chosen construction folded during
these calculations. The public `augmentation` definition also binds its
propositional universal-property instance with `have` instead of `haveI`, avoiding
proof inlining; proof irrelevance preserves the resulting lift. See the
change record `coord/changes/K1-constant-tower-normalization.md`.

Validation: the final module compiled in 54.4 seconds with no warnings. The full
delivery axiom scan on the completed proof also passed (45.3 seconds). The original
sources of both consumers compile unchanged against the optimized sandbox module:
`Sheaf.Paper.ProEtaleConstantReductionTower` in 49.0 seconds and
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows` in 6.3 seconds. All original
public declaration headers and public imports were compared with the shared source
and preserved.

## Proved and sorry left

Closed:

- `ordinaryReductionPull_existsUnique`.
- `reductionPull_existsUnique`.
- `constantTowerDirectImageNormalization`.

Three holes closed, zero holes added, zero local holes left. All new private helpers
are proved. Existing stated dependencies may retain their own independent holes;
none is moved or duplicated by this delivery.

## No longer needed

No module is withdrawn and no source-library declaration is removed.

The proof no longer needs these former direct private imports:

- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

Seven redundant direct Mathlib imports are also removed; each is already available
through the retained imports' public export closure:

- `Mathlib.Algebra.Homology.Functor`.
- `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`.
- `Mathlib.Algebra.Category.Grp.FilteredColimits`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `Mathlib.CategoryTheory.Sites.Limits`.

The former Sheaf imports' abstract diagram-site projection/tensor machinery is
replaced by the explicit
coefficient adjunction and whole-tower localization square already defining the
maps here. Some modules remain transitive imports of the unchanged public interface;
removing these direct proof imports does not claim that every such module disappears
from the target import closure.

Accordingly the old proof-only uses of
`lem-pe-constant-left-module-inverse-image`, `lem-weil-pbc-diagram-site-realization`,
`lem-weil-pbc-kinjective-total-derived`,
`lem-weil-pbc-ringed-projection-mate-exact`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-ringed-tower-pushforward-limit-comparison`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`lem-weil-tower-category-levelwise-abelian`, and
`prop-pur-kinjective-resolutions-exist` are unnecessary as separate proof steps.
Statement dependencies and the parent unit route remain intact.

The private `scalarExtensionPresheafMap`, `scalarExtensionMap`, and
`scalarExtensionMap_tmul` helpers are removed: scalar adjunction supplies their only
consumer's construction directly.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The former DAG argument asked for general diagram-site
projection results although the existing definitions already specified these maps
by exact localization and adjunction mates. The revised proof follows those precise
interfaces and proves their compatibility directly. All public signatures and
coefficient hypotheses are preserved.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
