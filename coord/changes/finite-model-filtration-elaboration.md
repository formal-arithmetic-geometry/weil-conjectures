# FiniteModelStratumFiltration elaboration context

## Reason

Preflight classifies the added module-level elaborator option and private smallness
instance as a scope/interface change. Record them explicitly for independent review.
The instance caches Mathlib's canonical `essentiallySmallSelf` proof, preventing
unrelated Noetherian-category instances from expanding search. The option permits
backward definitional-equality attributes during elaboration. Neither changes an
existing definition, theorem signature, visibility, or target meaning. All three
original definitions and the original public theorem statement are unchanged.

## Old

```lean
set_option autoImplicit false

universe u
```

## New

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

private instance (priority := 2000) essentiallySmallSelfInstance
    (C : Type (u + 1)) [CategoryTheory.Category.{u} C] :
    CategoryTheory.EssentiallySmall.{u + 1} C :=
  CategoryTheory.essentiallySmallSelf.{0} C
```

The new `Sheaf.Paper.OpenFiltrationSuccessor` module uses the same private
instance and elaboration option. The proof of `pointModulePullbackIso` additionally
uses `set_option backward.isDefEq.respectTransparency false in`; this option is
scoped to that private proof alone. It changes no mathematical declaration type.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteModelStratumFiltration | K2 | Proof elaboration only; existing public interface preserved. |
| Sheaf.Paper.OpenFiltrationSuccessor | K2 (new module) | Same private elaboration setup; new proved successor theorem. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unchanged consumer, no adaptation | Existing theorem and definitions retain their signatures and bodies. |
| Sheaf.Paper.CondensedERealization | unchanged consumer, no adaptation | Existing theorem and definitions retain their signatures and bodies. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unchanged consumer, no adaptation | Existing theorem and definitions retain their signatures and bodies. |

The last three modules are the direct importers in the current source tree.
No existing declaration mentions the new private instance. There is no definition
or statement change requiring a consumer adaptation or a renewed target-statement
review. The completed `tools/downstream.py Sheaf.Paper.FiniteModelStratumFiltration
--uses openFiltrationPiece openFiltrationCounit openFiltrationStratum
exists_finiteModelStratumFiltration essentiallySmallSelfInstance` scan finds 98
transitive importers. Each of the four existing public names occurs only in the
item module, and no downstream module mentions `essentiallySmallSelfInstance`.
Consequently none needs a source adaptation. The three direct consumers listed
above retain their existing interfaces and imports.

## Status

landed 20261019T005311-L-2750372 2026-10-19 (merge of deliver/K2/Sheaf.Paper.FiniteModelStratumFiltration)
