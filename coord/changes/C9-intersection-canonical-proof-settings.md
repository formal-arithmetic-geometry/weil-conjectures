# AlgebraicGeometry.intersection_canonical_affine_embedding

## Reason

The stage-3 proof needs names from `CategoryTheory.Limits` and explicit backward elaboration
settings to compare the actual pullback sheaf and chart restriction functors. These are
file-local proof elaboration commands, not changes to a mathematical definition or statement.
The static preflight classifies changed namespace openings and options as interface commands,
so this record documents them. No public declaration, public import, notation, instance,
attribute, target, or non-theorem body is changed. New private definitions construct the
inverse-image adjunction lifts explicitly, with all local-ring obligations proved.

The scoped unused-variable linter option preserves the original named proof binder `he` in
the theorem's conclusion. That binder witnesses the subset equality but does not occur in the
proposition's following text. The actual proof uses the corresponding introduced hypothesis.
No checking or kernel validation is disabled, and no heartbeat or time limit is raised.

## Old

```lean
universe u v
open CategoryTheory TopologicalSpace Opposite
```

There were no backward elaboration options or scoped unused-variable linter option.
The original theorem signature is retained verbatim in the delivered file.

## New

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
```

Immediately around the original public theorem and its docstring:

```lean
set_option linter.unusedVariables false in
```

The theorem signature and public imports are byte-identical to the original. Every helper is
private and fully proved. These local proof commands do not change any consumer's proposition
or definition; no consumer adaptation is needed.

## Users

`tools/downstream.py ... --uses AlgebraicGeometry.intersection_canonical_affine_embedding`
reports only the defining module as an explicit name use, and 33 transitive import consumers.
The table includes all 33 as well as the assigned module. Every consumer retains exactly its
existing statement and definitions. No Challenge target meaning is changed, so no target
statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding | C9 | Proof completed; private helpers and local proof commands added. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcValuativeDescent | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood | J1 | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.CoproductFpqcEffectivity | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineQuotientRepresentable | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleRelationQuotient | J7 | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage | S9 | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent | C5 | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse | S9 | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.InvariantOpenAffinizationEquivariance | C8 | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable | W8 | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.SeparatedLqfAffineRelationCover | T2 | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.SeparatedLqfFpqcDescent | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.AlgebraicGeometry.UniverseEnlargedEtaleRealization | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.NormalLatticeFiniteCoverPresentation | M6 | Unchanged interface; no adaptation. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.StratifiedLatticeScheme | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.TameIntegralReductionFamily | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SecPurity.NormalLocallyConstantFiniteSection | S8 | Unchanged interface; no adaptation. |
| Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent | unclaimed | Unchanged interface; no adaptation. |

## Status

landed 20261023T123412-L-1183635 2026-10-23 (merge of deliver/C9/Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding)
