# AlgebraicGeometry.ProEtale.flat_of_finiteCoefficientEtaleRealization_locallyFree

## Reason

The direct proof uses limits and opposite-category notation, together with a local
elaboration transparency option. The source-level interface scanner conservatively
classifies these module commands as an interface change. No declaration signature,
public import, notation declaration, instance or definition is changed. Namespace
opens and the elaborator option only affect elaboration inside this module; they
add no importer-visible names. All new helper declarations are private and proved.

## Old

```lean
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
```

## New

```lean
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
```

The public theorem has exactly its original signature. Its proof uses the private
import `WeilConjectures.CategoryTheory.Sites.FlatLocalRelations`; the three original
public imports remain verbatim.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteLocallyFreeEtaleFlat
--uses flat_of_finiteCoefficientEtaleRealization_locallyFree` reports the following
modules. The only downstream consumer applies the same theorem with the same
arguments, so its proof remains valid. No consumer adaptation is required. No
target statement or definition is changed; semantic target review is not reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteLocallyFreeEtaleFlat | P9 | Complete the original proof; add private helpers and proof context. |
| Sheaf.AlgebraicGeometry.OpenProjectionSourcePlus | unclaimed | Identical public theorem signature; its existing application is unchanged. |

## Status

landed 20261023T103155-L-3067767 2026-10-23 (merge of deliver/P9/Sheaf.AlgebraicGeometry.FiniteLocallyFreeEtaleFlat)
