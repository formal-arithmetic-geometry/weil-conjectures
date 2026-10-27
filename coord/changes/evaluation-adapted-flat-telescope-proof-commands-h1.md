# CochainComplex.exists_evaluation_adapted_flat_telescope

## Reason

The proof needs monoidal notation, zero-object notation and the abelian finite-biproduct
instance while constructing the private categorical telescope and resolution helpers.
The command-surface check requires a record for these commands. They add no exported
notation, instance or declaration: the instance attribute is explicitly local and the
variable section is closed before the public theorem. Every added helper is private and
proved. The theorem signature and all original public imports are verbatim unchanged.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex
```

There was no local resolution-variable section and no local biproduct instance attribute.

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

open MonoidalCategory
open scoped ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts
```

The helper `totalπ_epi` is inside this closed section:

```lean
section
variable {A B : Type*} [Category A] [Category B] [Abelian A]
  [Preadditive B] [HasZeroObject B] [HasFiniteCoproducts B]
  {ι : B ⥤ A} [ι.Full] [ι.Faithful] [ι.Additive]
  (Λ : Abelian.LeftResolution ι) [Λ.F.PreservesZeroMorphisms]
```

Its section ends immediately after the proved private helper. Two declarations use
`set_option backward.isDefEq.respectTransparency false in` locally for the canonical
cokernel construction and the total-augmentation computation. No file-level elaboration
option was added. Private proof imports supply the independent-universe flat-resolution,
tensor-colimit and bounded-flat APIs; the original public import list is unchanged.

## Users

`python3 tools/downstream.py Sheaf.Algebra.Homology.EvaluationAdaptedFlatTelescope
--uses exists_evaluation_adapted_flat_telescope` reports zero downstream modules and only
the defining module as a textual user. A source search also finds no current importer or
consumer. This does not withdraw the theorem: its unfinished DAG parent still needs it.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.EvaluationAdaptedFlatTelescope | H1 | Its proof now compiles; all public signatures and public imports are unchanged. |

No consumer adaptation or target statement review is needed: these commands only affect
proof elaboration within this file.

## Status

landed 20261023T231324-L-3576711 2026-10-23 (merge of deliver/H1/Sheaf.Algebra.Homology.EvaluationAdaptedFlatTelescope)
