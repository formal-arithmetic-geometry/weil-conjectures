## What changed

Proved `AlgebraicGeometry.Scheme.Modules.globalTensorPullback_mates_isIso` without changing
its signature or public imports. The unit mate is recognized by the universal property of
maps from the unit sheaf and linear maps from the rank-one free module. For fixed B, the
tensor mates form a natural transformation of colimit-preserving functors. At the ring,
composition with the unit mate and the sheaf left unitor is P applied to the module left
unitor; the equality is verified on pure tensors after transposing through the adjunction.
A free-module presentation then extends invertibility to arbitrary A.

Added the completely proved generic theorem `ModuleCat.isIso_app_of_rankOne` in
`Sheaf.Algebra.Category.ModuleCat.CocontinuousGenerator`. Its proof constructs the coproduct
of rank-one free modules and the presentation R^(ker g) → R^(M) → M explicitly and uses
preservation of the resulting coequalizer. Its statement does not assume additivity.

The main module privately imports this new module, the Mathlib closed structure on modules,
and the braided closed-category API. Private helpers identify compatible sections with
sections on the top open and prove the unit-mate assertion. The DAG records the new route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.globalTensorPullback_mates_isIso`
(node `lem-sc-global-tensor-pullback-mates-isiso`).

Added zero holes. `ModuleCat.isIso_app_of_rankOne`
(node `lem-sc-modulecat-cocontinuous-generator`) is fully proved.
There is no `sorry` in either delivered Lean module. Existing deferred theorems in imported
modules, including the sheaf tensor-closed structure, are unchanged.

## No longer needed

No original import or original proof-dependency node is removed:
`Sheaf.Paper.ModuleCupNaiveMap` remains necessary for the section tensor map.

This proof does not use point evaluation, construction of inverse image/change of rings,
or uniqueness/transport of left adjoints as proposed in the original proof plan. In
particular it does not import `Sheaf.Topology.PointModuleEvaluationEquivalence`,
`Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived`, or
`Sheaf.Paper.GlobalSectionsLaxMonoidalData`. These are unnecessary for this theorem;
no assertion is made that other target branches cease to need those modules.
No existing modules are claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original sole proof dependency defines the section tensor map but supplies no theorem
for the claimed local pullback isomorphism or its transport. The free-presentation route
avoids that missing step. The blueprint unit's realized statement/steps are unchanged.

The published compiled library did not contain `GlobalSectionsLaxMonoidalData` when checked.
The final proof avoids it entirely rather than restating its theorem. LeanSearch returned
an Internal Server Error; this search is recorded as unavailable, with no absence verdict.
LeanFinder, Loogle and source searches supplied the supporting APIs.

## New nodes

`lem-sc-modulecat-cocontinuous-generator` records detection of invertibility of natural
transformations of cocontinuous functors from modules on the rank-one free module. It is
proved in the new module, with a complete coproduct/cokernel argument in its docstring and
node. The source is the analogous presheaf-generator proof in the existing source library;
this specialization is marked agent-written. Searches found supporting colimit and
free-module APIs but no exact ordinary-module theorem. No change record is needed: no
existing statement, definition, signature or visibility was changed.

## Second reading by M4

1. Compared the delivered main module with the repository version. The existing theorem
   signature and all existing declarations are unchanged; only proof-local imports and
   proof terms were added. The generator theorem is a separate declaration with a matching
   node.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The
   delivered Lean files contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. No definition contains postponed data.
3. Checked the new generator statement against its proof and edge cases, including the
   zero and empty free modules. It is strictly more general than the application and does
   not duplicate an existing declaration; its source and search records are present.
4. The proof follows the shortest route from the imported section tensor map: the unit mate
   is proved by Hom-bijections, and tensor mates are extended from the rank-one free module
   by colimit preservation. The original proof dependency remains necessary and all private
   imports are used.
5. The DAG proof, proof dependencies, proof origin, and realized unit route agree with the
   Lean proof. No target or definition statement changed.

I changed only this report section; no Lean proof or DAG content required repair.
