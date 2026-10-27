# CategoryTheory.completed_localized_adjunction_square

## Reason

The completed proof constructs localized functors using private tensor helpers. Stage-3
preflight classifies the added section, variables and open command as a context change and
requires this record. All added definitions, lemmas and instances are private. Every public
statement and every public import is unchanged. No downstream adaptation is needed.

## Old

The module-level context immediately inside `namespace CategoryTheory` was empty:

```lean
namespace CategoryTheory
```

## New

The following context surrounds the private helpers and is closed before the original theorem:

```lean
namespace CategoryTheory

section TensorConstruction

variable {A : Type r} [CommRing A] (t : A)
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear A C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [Linear A D]
  {E : Type uC'} [Category.{vC'} E] [Preadditive E]
  [Linear (Localization.Away t) E]

open ScalarLocalization
```

The section ends with `end TensorConstruction`. Its declarations are private:
`tensorMap`, `tensorMap_tmul`, `tensorMap_additive`, `tensorMap_linear`,
`tensorLiftHom`, `tensorLiftHom_tmul`, `tensorLift`, `tensorLift_tmul`,
`tensorLift_additive`, `tensorLift_linear`, and `tensorNaturality`.
The four instances are private instances on private functor constructions. No existing
public definition, signature, attribute or instance is modified.

## Users

`tools/downstream.py Sheaf.CategoryTheory.CompletedLocalizedAdjunctionSquare --uses
CategoryTheory.completed_localized_adjunction_square` reports zero downstream modules.
The declaration search finds only the defining module. The unfinished DAG parent still needs
the theorem, whose statement and attachment are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CompletedLocalizedAdjunctionSquare | G2 | Original theorem proved; private helpers only; public signature unchanged. |

## Status

landed 20261023T102744-L-2967542 2026-10-23 (merge of deliver/G2/Sheaf.CategoryTheory.CompletedLocalizedAdjunctionSquare)
