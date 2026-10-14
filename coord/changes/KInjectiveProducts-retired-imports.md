# KInjectiveProducts retired imports

## Reason

Repair landing 20261014T090919-L-366279 at broken tip
1594522f4d7fb327c27776cbef1826a99222bb38. Removing all public imports left
this empty compatibility module without the elaboration commands used by the
global build's axiom/sorry probe. The reported errors were `unknown namespace
Command` and a request to include `Lean.Elab.Command`.

Restore the exact three public Mathlib imports from before that landing.
The duplicate theorem remains retired; no declaration, target statement,
proof, definition, axiom rule or existing docstring is changed.

## Old

No imports (the broken landed version).

## New

```lean
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
```

## Users

Source search in the fresh snapshot finds no Lean module importing this
compatibility module. The global build generates a BatchProbe consumer, whose
elaboration depends on the public import environment. Restoring the original
interface repairs that consumer without editing any build tool or other module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KInjectiveProducts | XR33076d633fce5c89 | Original public imports restored; generated probe commands available again. |

## Status

landed 20261014T092934-L-608757 2026-10-14 (merge of deliver/XR33076d633fce5c89/Sheaf.Algebra.Homology.KInjectiveProducts)
