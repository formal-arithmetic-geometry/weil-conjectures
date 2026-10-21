# WeilConjectures.coefficientTensorAdditive

## Reason

Stage-3 preflight flags the added local attribute command as a change to the module
interface. This record documents the proof environment. No existing public declaration,
instance body, signature, public import or exported attribute changes. All added helpers
are private and proved. The item is held by S5; no other module is edited.

The generic scalar-extension adjunction supplies additivity at the module universe
`max u v`, where the fixed-universe instance is insufficient. Local typeclass search
uses this helper while proving exactness. Its attribute does not propagate to importers.

## Old

There is no declaration `coefficientTensorAdditive` and no attribute referring to it.
The original elaboration options are exactly:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
```

All existing public declaration signatures and non-theorem bodies are retained verbatim.

## New

```lean
private theorem coefficientTensorAdditive {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : (ModuleCat.extendScalars.{u, u, max u v} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive

attribute [local instance] coefficientTensorAdditive
```

The additional elaboration option is:

```lean
set_option backward.isDefEq.respectTransparency.types false
```

This controls proof elaboration only. No compiler timeout, heartbeat limit or kernel
checking option is changed. The module contains no diagnostic profiling or trace commands.
All new imports are private proof imports. No target-used definition changes meaning.

## Users

`python3 tools/downstream.py Sheaf.Paper.CoefficientComplexRationalization --uses
coefficientTensorAdditive coefficientComplexTensors_exact coefficientComplexBeta_existsUnique
coefficientComplexIntegerIdentity coefficientComplexIntegerComp coefficientComplexComparison_spec
coefficientComplexRationalization` reports zero downstream Lean modules. The private helper
has zero textual users in the repository version; each of the six public theorem names is
used only in this item module. The node remains needed by its DAG parents; none is withdrawn.
The six existing theorem signatures are unchanged, so their future consumers require no
adaptation. The single-file compile and the delivery axiom and server compile checks pass.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientComplexRationalization | S5 | Private proof support; existing public API unchanged. |

## Status

landed 20261021T134539-L-1350111 2026-10-21 (merge of deliver/S5/Sheaf.Paper.CoefficientComplexRationalization)
