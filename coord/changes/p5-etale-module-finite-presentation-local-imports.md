# AlgebraicGeometry.Scheme.Modules.etale_module_finite_presentation_local

## Reason

The proof only needs the concrete tensorPullback functor and its existing adjunction,
not the additional section-normalized adjunction API. The statement assumes quasi-coherence,
not the separate quasi-coherent-finite-type predicate. Remove these unused dependencies and
the redundant direct import of Generators. The public theorem signature is unchanged.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.Descent
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Descent
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.EtaleModuleFinitePresentationLocal | P5 | Prove the existing theorem; private proved comparison helpers. |
| Sheaf.TraceFormula.ElementaryDevissageFinitePresentation | unclaimed | Sole direct importer; no change needed. It already imports CoherentFiniteType directly and obtains tensorPullback publicly from ElementaryModuleDevissage. It uses none of the removed normalized adjunction declarations. Generators remains available through Quasicoherent. |

The source-only downstream scan lists ten downstream modules, with no textual use of the
item theorem outside the item yet (the parent proof remains unfinished). There are no
adapted modules. All downstream access to the removed exports passes through the sole
direct importer, whose own explicit imports supply its statement dependencies.

## Status

landed 20261023T123938-L-1298183 2026-10-23 (merge of deliver/P5/Sheaf.TraceFormula.EtaleModuleFinitePresentationLocal)
