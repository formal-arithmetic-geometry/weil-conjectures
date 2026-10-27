# AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsAdjunctionExtension

## Reason

Prove the existing theorem by explicit sectionwise maps and normalized adjunctions.
The original seven public data constructions and the theorem signature are unchanged.
Remove five unused public imports. The open-section unit equation is proved directly
from the generic uniqueness-of-left-adjoints equation, and naturality in the modules
is proved directly with the Hom equivalence. A private Mathlib adjunction import
supplies the proof-only unit identity. All new helpers and reducibility attributes
are private or local to this file. No shared definition is changed.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
public import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
```

The theorem body was `by sorry`.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.Unique
```

The theorem has a complete proof. The original public declaration signatures and
all seven public definition bodies are retained verbatim. The tensor definitions
are kept folded locally while proving the open-section unit equation. A private typed
alias names exactly the original chosen adjunction to reduce elaboration overhead.
The open-unit equation is proved for an arbitrary left adjoint before specializing
to the concrete tensor functor.

## Users

Read-only `tools/downstream.py --direct --uses` found the following two direct
importers; neither mentions any of this module's eight public declarations.
Both are compiled unchanged against the delivery before submission. No adaptation
or additional claim is needed; no target statement or definition changes meaning.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleTensorSectionsAdjunctionExtension | W3 | Proved theorem and pruned imports. |
| Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom | unchanged; not adapted | Compile against reduced imports. |
| Sheaf.AlgebraicGeometry.SchemeEtaleRelativeDifferentialsComparison | unchanged; not adapted | Compile against reduced imports. |

## Status

landed 20261026T083417-L-2345871 2026-10-26 (merge of deliver/W3/Sheaf.AlgebraicGeometry.EtaleTensorSectionsAdjunctionExtension)
