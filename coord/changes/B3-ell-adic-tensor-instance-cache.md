# AlgebraicGeometry.ProEtale.moduleTensorLeft_smallColimits

## Reason

Repeated synthesis of preservation of colimits for tensor functors in the graded
tensor construction made elaboration of the original derived-functor expressions
expensive. Four local, named, proof-valued instances give direct routes to the
standard preservation results. No existing statement or non-theorem definition
body is changed. No coefficient data or additional hypothesis is introduced.
The integral triangulation theorem is given higher local priority; it proves the
same `IsTriangulated` proposition for the original integral coefficient property.
Its instance proof is proof-irrelevant. The interface probe records inferred
instance-expression changes in the localization declaration as well as the new
helper declarations; the localization statement itself is verbatim upstream.

## Old

There were no named local tensor-preservation instances here; instance search used
the existing general tensor adjunction and colimit-preservation instances.
The public declarations retain their verbatim upstream signatures and bodies,
except for the completed proof of the localization instance.

## New

Within the original `AlgebraicGeometry.ProEtale` namespace and its original
parameters `X`, `ℓ`, and `E`:

```lean
local instance moduleTensorLeft_smallColimits
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

local instance moduleTensorRight_smallColimits
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
  infer_instance

-- These direct instances avoid inspecting a graded tensor diagram during synthesis.
local instance moduleTensorLeft_preservesColimit
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {I : Type} [SmallCategory I]
    (D : I ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :
    PreservesColimit D (tensorLeft M) := by
  infer_instance

local instance moduleTensorRight_preservesColimit
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {I : Type} [SmallCategory I]
    (D : I ⥤ Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :
    PreservesColimit D (tensorRight M) := by
  infer_instance
```

The left small-colimit instance follows from `ihom.adjunction`; the other three
are inferred from existing Mathlib instances. These are proofs of Prop-valued
classes, so proof irrelevance identifies their data wherever the unchanged
public definitions use them. The declarations are local instances to this file;
their names remain public because public functor definitions can use their proofs.

## Users

`tools/downstream.py` was run on this module and the preservation, restricted
functor, compatibility, localization and rationalization names. The only
external downstream module is the import-only root aggregator `WeilConjectures`.
All name uses are inside this item module, which compiles as a whole in 33.0 seconds.
No external consumer needs adaptation. The new helper names have no pre-existing
consumers.

| module | current holder | effect |
| --- | --- | --- |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | B3 | Four proof-valued local instance helpers and the completed localization proof; existing public signatures and non-theorem bodies are verbatim. |
| WeilConjectures | unclaimed | Imports this module only; no adaptation. |

## Status

landed 20261018T071135-L-1663793 2026-10-18 (merge of deliver/B3/WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization)
