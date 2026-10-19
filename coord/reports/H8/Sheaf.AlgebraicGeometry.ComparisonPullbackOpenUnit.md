## What changed

Proved `AlgebraicGeometry.ProEtale.comparisonPullbackOpenUnit` in the assigned module,
with its exact original signature and all three public abbreviation bodies unchanged.
Two proved private helpers identify the conjugate of the canonical comparison and
compute the mate of the fixed sectionwise restriction map. Their derivations reuse
the already proved private calculations in `OpenComparisonUnitNormalization`.
Injectivity of the iterated mates correspondence identifies the required mate;
`unit_mateEquiv` and cancellation of the comparison with its inverse finish the proof.
The DAG proof and proof dependencies now record this argument.

Added proof-only import `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique`.
The helpers use three elaboration options scoped to their declarations; the change
record is `coord/changes/H8-comparison-pullback-open-unit-proof-context.md`.
No consumer adaptation, statement change, definition change, or new axiom is involved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.comparisonPullbackOpenUnit`
(node `lem-pur-comparison-pullback-open-unit`).
Added 0 holes and split off 0 statements. No sorry remains in the delivered module.
Both private helpers are fully proved. The canonical maps are constructed from the
existing adjunctions and isomorphisms; no arbitrary witness is selected.

## No longer needed

Removed these six proof-only imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The concrete restriction adjunctions and canonical localization uniqueness maps already
available through the public imports suffice. The first, third, fifth and sixth modules
supply constructions already exposed transitively; no direct import is needed.
`RingedSiteModules` is unnecessary for the proof in the existing ModuleCat-valued
sheaf category. The general objectwise Kan-index restriction theorem
`lem-sfb-proetale-object-inverse-image-restriction` and its module are not used: the
mate is computed directly from the fixed restriction adjunctions and pullback arrows.
Removed that node from proof_deps and the top-level tool_uses list.
Also removed `lem-weil-pbc-open-immersion-etale`,
`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`,
`def-weil-open-immersion`, and `def-weil-sheaf-of-modules-category` from proof_deps:
there is no separate appeal to their theorems in this argument; the needed instances
and categories are already part of the concrete constructions and statement.
These nodes remain in stmt_deps where applicable. No unit statement or unit proof
step is bypassed (the unit record has no realized node for this item).
Both original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The interrupted sandbox attempt applied `openComparison_unit_normalization` clause 2,
which concerns the extension-by-zero adjunction unit and takes a sheaf on V. This item
instead concerns the comparison-adjunction unit and takes a sheaf on T; the compiler
confirmed the mismatch. No library statement was wrong. The DAG's long separate
Kan-index unit calculation is unnecessary once one uses the existing concrete
localization adjunctions and the iterated mates theorem.

Edge cases: the proof is purely functorial and never assumes a nonempty open, a
nonzero sheaf or a nonzero coefficient ring. It keeps the specified canonical gamma
and c throughout, so it also excludes arbitrary rescalings of either comparison.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
