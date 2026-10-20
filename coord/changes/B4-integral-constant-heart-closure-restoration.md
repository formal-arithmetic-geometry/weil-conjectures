# AlgebraicGeometry.ProEtale.isConstantModelConstructible_serre_padicIntegers

## Reason

Restore the assigned quarantined module after upstream sync. Its existing
complete proof fails because Mathlib's kernel, cokernel and extension closure
classes are unavailable through the current imports. Adding their defining
modules as proof imports repairs elaboration.

## Old

The exact baseline is
`quarantine/Sheaf/Paper/IntegralConstantModelHeartClosure.lean` from the assigned
`coord/rework.tsv` row. It has no holes. Its proof imports end with:

```lean
import Mathlib.Algebra.Field.ULift
```

The original `obtain ⟨hk, hc, he⟩ := integralConstructible_serre ℓ E.val X`
fails at line 290 with `Tactic generalize failed: result is not type correct`.
Taking a projection instead reports the unavailable constant
`CategoryTheory.ObjectProperty.IsClosedUnderKernels`.

## New

Restore every baseline declaration, signature, body and public import verbatim.
Add only these proof imports after the existing proof imports:

```lean
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
```

The original proof then compiles cleanly in 11.5 seconds. There is no definition
or statement change, no new instance, no added hole, and no changed target.
The DAG proof and Lean attachment already describe the restored proof exactly.

## Users

The live module is quarantined, so `tools/downstream.py` reports it unknown.
A direct search of all Lean sources in `lean/` and `quarantine/` found the
following direct archived importers. None is edited or requires adaptation:
all public imports, theorem signatures, attributes and definitions are identical
to the archived baseline. Holder is not relevant to this import-only repair;
no other group's module is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralConstantModelHeartClosure | B4 | Restored; two proof imports repair compilation. |
| Sheaf.SixFunctors.FieldTensor | Not adapted | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Not adapted | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | Not adapted | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | Not adapted | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | Not adapted | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | Not adapted | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | Not adapted | Identical public interface; no adaptation. |

There are seven distinct direct importing modules (the eighth search hit is the
item's own theorem declaration). No current live importer was found.

## Status

landed 20261020T154038-L-3032519 2026-10-20 (merge of deliver/B4/Sheaf.Paper.IntegralConstantModelHeartClosure)
