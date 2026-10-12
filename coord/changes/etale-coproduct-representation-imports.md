# AlgebraicGeometry.Scheme.etaleCoproduct_representation: imports and proof commands

## Reason

The completed proof obtains representable sheafhood directly from Mathlib's
subcanonical APIs, so it no longer uses the auxiliary Sheaf module.
The Cover.Sigma import was unnecessary for both the statement and the proof.
Products in functor categories and the pro-etale subcanonical theorem are now
imported for the proof. Additional open namespaces and elaboration options support
private helpers only. The theorem's statement, name, universes, and hypotheses are
unchanged. No target definition or target statement changes meaning.

## Old

```lean
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import Mathlib.AlgebraicGeometry.Cover.Sigma
import Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
```

```lean
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme
```

## New

```lean
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
```

```lean
open CategoryTheory Limits Opposite Functor

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleCoproductRepresentation --uses
etaleCoproduct_representation` found the following two modules mentioning the
unchanged theorem. There are 183 modules in the transitive import closure, but only
one direct importer. That importer already explicitly imports Cover.Sigma, and the
removed Sheaf import was proof-only. No downstream adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleCoproductRepresentation | H2 | Proof completed; signature unchanged. |
| Sheaf.AlgebraicGeometry.FiniteLocalModelsDescentDatumExistence | No claim listed in the local claim records | Calls the unchanged theorem. Already imports Mathlib.AlgebraicGeometry.Cover.Sigma itself, so its statement and proof retain that API. |

No public declaration, definition, attribute, or instance was added. All helpers
are private, and the local open commands and options do not affect importers.

## Status

landed 20261012T113946-L-820580 2026-10-12 (merge of deliver/H2/Sheaf.AlgebraicGeometry.EtaleCoproductRepresentation)
