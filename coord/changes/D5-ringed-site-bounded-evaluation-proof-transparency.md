# CategoryTheory.RingedSiteBoundedEvaluation.assembly

## Reason

Complete the single assembly proof. Preflight conservatively classifies the added
file-level commands as an interface change and requires this record. They control
elaboration of the new private helpers: folding the Hom complex, coefficient sheaf,
sheafification, and tensor comparisons avoids expensive definitional reductions.
All attributes below are explicitly local. There is no public declaration signature,
definition body, public import, global attribute, or notation declaration change.

The only adapted module is
`Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly`, held by D5.
No source-library module is changed.

## Old

The original file has no `open scoped TensorProduct` and none of the proof-local
attribute commands listed below. Its existing `autoImplicit`, `synthInstance.maxSize`,
and `backward.isDefEq.respectTransparency` options remain unchanged. The public
`assembly` signature is retained verbatim; its old proof is `by sorry`.

## New

The additional scoped opening is:

```lean
open scoped TensorProduct
```

The proof-local transparency commands, in source order, are:

```lean
attribute [local irreducible] homComplex homComplexFunctor homComplexπ
attribute [local irreducible] SheafOfModules.monoidalCategory
set_option allowUnsafeReducibility true in
attribute [local reducible] dual total inclusion unitComplex
  CochainComplex.ιMapBifunctor CochainComplex.mapBifunctor
  sourceFamily targetFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] sheafCompose
  PresheafOfModules.sheafification PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] inverseCounit
attribute [local semireducible] sheafCompose PresheafOfModules.sheafification
  PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] evaluationPresheaf evaluationBilinear evaluationSection
attribute [local semireducible] SheafOfModules.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] tensorLift moduleEvaluation
attribute [local irreducible] evaluationComponent
attribute [local irreducible] evaluationDegree
attribute [local semireducible] SheafOfModules.monoidalCategory
```

Here `inverseCounit`, `evaluationPresheaf`, `evaluationBilinear`, `evaluationSection`,
`tensorLift`, `moduleEvaluation`, `evaluationComponent`, and `evaluationDegree` are
new proved/concrete private helpers. The temporary reducibility option only permits
local changes of elaboration transparency; it introduces no unsafe declaration.
The kernel checks the completed proof. Local attributes and scoped openings are
not exported to importers. No target meaning changes or statement review is reopened.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly
--uses CategoryTheory.RingedSiteBoundedEvaluation.assembly` reports zero downstream
modules and only the item itself as a declaration-name hit. The DAG parent
`lem-sfb-ringed-site-strict-perfect-hom` remains a planned user; its required
assembly interface is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly | D5 | Complete assembly proof; new private helpers and local elaboration controls; public signatures unchanged. |

The clean file compiled in 56.6 seconds with the normal heartbeat budget. Delivery
compilation and axiom checking also passed before preflight requested this record.
No consumer adaptation is needed, because the exported interface is unchanged.

## Status

landed 20261021T193044-L-838948 2026-10-21 (merge of deliver/D5/Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly)
