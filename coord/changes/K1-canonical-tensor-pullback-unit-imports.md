# SheafOfModules.canonicalRingedTensorComparison_unit_exists

## Reason

The unit existence theorem is proved directly from the supplied algebraic inverse-image
and normalized pure-tensor data. It needs no derived category or K-flat argument and no
construction of a different tensor comparison. Keep only the data module public; import
the section calculus and the existing scalar-extension helper theorems privately.
The existing theorem's full signature, visibility, and meaning are unchanged.

## Old

The import header was:

```lean
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
```

## New

The import header is:

```lean
public import Sheaf.Paper.RingedTopoiTensorComparisonData
import Sheaf.Paper.RingedTopoiTensorSections
import all Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
```

Five new private, fully proved helpers supply the right-unitor formula, the inverse-image
and scalar-extension unit isomorphisms, the formula for q, and extensionality after q.
They add no public API, instance, or attribute. The theorem has no remaining sorry and its
axioms are exactly propext, Classical.choice, and Quot.sound.

## Users

The downstream declaration-name check finds only the item and its parent below. A direct
import search finds exactly one external importer: the parent imports this module privately
and already explicitly imports every public dependency removed here. Consequently every
other module receives the same public declarations through the parent's existing imports.
No consumer statement, definition, signature, or proof needs adaptation; no target's meaning
changes. The downstream import closure contains 1910 modules, but no further direct or named
consumer relies on this header.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitExistence | K1 | One proof completed; public signature unchanged. |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullback | Not adapted; existing live claim retained | Private importer; all removed public imports already explicit in its own header. |

The unchanged parent was checked against the overlay. It fails during imports with
`import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed failed, environment
already contains 'SheafOfModules.tensorClosed' from
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`. This is before the import of this
item. A separate baseline copy without the sandbox overlay has the same import failure.
It is an existing compiled-import conflict, not a forced adaptation caused by this change.
The item itself compiles within the unchanged 60-second limit (26.6 seconds for the complete
proof; 25.4 seconds with the axiom probe).

## Status

landed 20261019T192758-L-1866923 2026-10-19 (merge of deliver/K1/Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitExistence)
