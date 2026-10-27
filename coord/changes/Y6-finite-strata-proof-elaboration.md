# AlgebraicGeometry.ProEtale.FiniteStrataCompletion.finite_strata_completion_detection

## Reason

The module's one original theorem is now proved. Its scalar-model calculation previously
triggered expensive unfolding of categorical scalar extension and the chosen standard
derived category. Proof-local irreducibility and a private constructed leaf projection
keep these calculations within their existing comparison APIs. Stage-3 preflight treats
new attribute commands conservatively as visibility changes and requests this record.
All added attributes explicitly have `local` scope. No original public signature,
public import, definition, or existing attribute is changed. No target changes meaning.

## Old

The original module has these elaboration options, with no following local attributes:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
```

The original proof of `finite_strata_completion_detection` is `by sorry`.
The five original definitions `pull`, `completionCone`, `leafCover`, `leafCoverTest`,
and `leafScalarModels` remain verbatim in the new file.

## New

The original options remain, followed by this proof-local attribute:

```lean
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.Mod.extendScalars
```

After the five unchanged original definitions, the following proof-local attribute
precedes private, proved helpers:

```lean
attribute [local irreducible] CondensedRing.upperStar finiteConstantScalarExtension
```

Every added helper is private and proved. The theorem's full signature is unchanged.
Its complete proof combines indexed-to-recursive tree refinement, module/homology zero
detection, the existing strict completion restriction comparison, and scalar matrix
transport through the actual leaf-cover projection. There are zero remaining holes.
The two unit-route imports `Sheaf.AlgebraicGeometry.WeaklyEtaleStability` and
`Sheaf.Paper.CartesianCoefficients` are retained.

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteStrataCompletionDetection --uses pull
completionCone leafCover leafCoverTest leafScalarModels finite_strata_completion_detection`
reports zero downstream Lean modules. Its name-use hits are exclusively the item itself.
DAG parents remain valid because the statement and all public data are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteStrataCompletionDetection | Y6 | One theorem proved; local elaboration attributes and private helpers only. |

## Status

landed 20261024T022442-L-2992400 2026-10-24 (merge of deliver/Y6/Sheaf.Paper.FiniteStrataCompletionDetection)
