# LocallyClosedGeneratorTensorIntersection proof-local commands

## Reason

Record the file-local commands used by the private proof helpers. The stage-3 scanner
conservatively treats sections, universes and local attributes as interface changes.
The six original public definitions, their bodies, the public imports and the target
lemma's signature are unchanged. No public declaration, instance or attribute is added.
No other module needs adaptation. The complete item compiles cleanly in 35.3 seconds with normal settings and no warnings.

## Old

The original proof context, verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
```

## New

The original context remains. Private helper sections bind the category and hom
universes explicitly. They prove the finite-biproduct tensor calculation, tensor
restriction and flatness detection, and the canonical degree-zero tensor comparison. A private theorem also caches the existing
functorial-flat-resolution proposition for the concrete coefficient-module category.
Every section is closed. The outer `GeneratorTensorProof` section ends before the public
theorem, restoring its original local instance and attribute context. The extra opening of
`CategoryTheory.MonoidalCategory` only resolves notation. Local instance registrations cache
already-existing tensor
and monoidal structures; they introduce no new chosen data. Local irreducibility
prevents repeated unfolding of canonical functors and monoidal constructions. The
proofs use their equations and naturality APIs instead. The local attributes are:

```lean
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] upperStar upperStarComp upperStarCongr
  Mod.monoidalCategoryStruct
attribute [local irreducible] upperStarLowerStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction
attribute [local irreducible] generatorExtension generatorRestriction
  generatorIntersectionModule generatorTensorSource generatorTensorTarget
  derivedTensor DerivedCategory.singleFunctors DerivedCategory.homologyFunctor
attribute [local irreducible] tensorRestrictionIso ObjectProperty.flat
attribute [local irreducible] ordinaryComparison
attribute [local instance] gradedTensorExists gradedTensorFourExists
  gradedGoodTensor12 gradedGoodTensor23
attribute [local instance] singleDerivedMonoidalExists
attribute [local irreducible] Functor.LaxMonoidal.μ
attribute [local instance] singleDerivedMonoidalExists
attribute [local irreducible] singleTensorHom singleTensorIsoComp
attribute [local irreducible] derivedComparison
```

The concrete derived comparison and its naturality proofs pass `Mod.braidedCategory`,
`Mod.monoidalClosed` and the proved flat-resolution cache explicitly to the generic private
construction. These are the existing canonical structures, with no local data chosen.

The proof also uses file-local `synthInstance.maxSize 2048`, declaration-local
`maxSynthPendingDepth 16` for the concrete derived comparison and normalized existence lemma, and declaration-local
`backward.isDefEq.respectTransparency` options. They change elaboration only.
The final comparison uses generic source/target factories with explicit tensor-functor
parameters. Two proved equations identify the actual derived and intersection tensor
functors with their canonical constructions; transport occurs inside a private theorem.
The public theorem consequently compares applications of the actual public functors.
No public definition was repaired or replaced.

All temporary guards, profiler options, trace commands and reduced heartbeat budgets have
been removed. The server's file time limit is unchanged.

## Users

A source import-graph scan of both library roots found zero current Lean importers.
The existing DAG parent still needs this result, so the module and its Lean attachment
are retained. There is no consumer edit and no forced adaptation. Its future importers
see the same public API and data; the local commands expire at the end of the file.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | E8 | Original theorem hole filled by private helpers; unchanged public API and data. |

## Status

landed 20261022T022034-L-431456 2026-10-22 (merge of deliver/E8/Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection)
