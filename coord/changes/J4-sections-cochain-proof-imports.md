# Sheaf.Paper.SectionsScalarCochainCoherence public imports

## Reason

Remove the unused cochain monoidal-structure re-export. Scalar extension in this module is
termwise application of the ordinary extension functor and of the existing sheafified
change-of-rings construction. Neither the statement nor its proof uses the monoidal
structure on unbounded complexes. Keeping its instances in the elaboration environment
also makes the large coherence statement substantially slower to elaborate.

Every existing public declaration signature is unchanged. The separate change record
J4-sections-pure-transport.md describes the equivalent computation of `pure`. The
specialized common-universe tensor-section calculus is an unused private proof import
and is removed separately. The proof instead uses the ordinary scalar adjunction and
module sheafification, preserving the independent universes of the existing statement.

## Old

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
```

## New

The unused public import is removed. The retained public imports are:

```lean
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.Additive
```

## Users

`tools/downstream.py Sheaf.Paper.SectionsScalarCochainCoherence --uses
CategoryTheory.SectionsScalarCochain.coherence` reports zero downstream modules;
the declaration name occurs only in its own module. This packet does not withdraw
any module or node, and preserves the attachment needed by unfinished DAG parents.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SectionsScalarCochainCoherence | J4 | Proves the existing theorem; removes an unused re-export. |

## Status

landed 20261024T190135-L-3958391 2026-10-24 (merge of deliver/J4/Sheaf.Paper.SectionsScalarCochainCoherence)
