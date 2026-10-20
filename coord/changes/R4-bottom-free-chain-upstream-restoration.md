# bottomFreeChain_derived_square: restore the adopted upstream interfaces

## Reason

Restore the complete zero-hole archive recorded in coord/rework.tsv. Its obsolete Sheaf
imports conflict with, or no longer expose, the adopted upstream interfaces. The private
counit helper must use IsKFlatTensor, which the source derivedPullback_spec and bounded-flat
theorem share. Its unused universal-property conjunct is removed from the helper's result;
the source universal-property theorem itself is unchanged.

The public bottomFreeChain_derived_square signature is byte-for-byte the archive's. Its
bounded-flat, counit and naturality argument is retained. To avoid expensive normalization
of concrete tensor-pullback and site-equivalence definitions, a private chartEquivalence
contains the actual Modules.overEquiv construction, with a proved equality API and an
irreducible attribute. Both uses of the canonical functors are transported through this
equality explicitly. Invertibility checks use
explicit isomorphism components instead of dsimp. Local caches preserve the actual abelian
structures and exactness instances. Computed comparisons are retained behind their typed
interfaces, and source restriction instances take priority over generic composition and
additivity searches. All local instances are proved or existing instances; no data or
proof hole is introduced. The complete final packet compiled and exported in import order without warnings:
35.3 s for the square and 39.1 s for the direct consumer.

Also restore the unclaimed quarantined direct consumer BottomFreeChainPullbackComparison.
Its original archive fails against the restored item with unknown Scheme and
HasDerivedCategory, reported as privately imported, because its own public Sheaf
DerivedPullback import is retired. Redirect that import to the source and lower the local
priority of generic instance searches. Its public theorem signature and proof body remain
verbatim. This is an unclaimed consumer repair, not a forced adaptation of a held module.

Retarget the bounded-flat node's Lean attachment to the existing adopted source theorem
with conclusion IsKFlatTensor. Its mathematical statement and proof are unchanged. No
source-library file, target statement or definition is modified.

## Old

Archived item imports:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.PerfectHomTransport
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
```

Archived private helper signature:

```lean
private theorem tensorCounit {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ (_ : (Modules.tensorPullback g).Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        (Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))),
      (derivedPullback g).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) ∧
      ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
```

The bounded-flat attachment named
Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat and conclusion K.IsAcyclicTensorKFlat.
The parent publicly imported Sheaf.AlgebraicGeometry.DerivedPullback. Both modules gave
generic additivity/composition instances the default local priority.

## New

Restored item imports:

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.PerfectHomTransport
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
```

New private data construction and equation (the old module used the concrete expression
inline):

```lean
private noncomputable def chartEquivalence {Y : Scheme.{u}} (V : Y.Opens) :
    SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V) ≌
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) := Modules.overEquiv V

private theorem chartEquivalence_eq {Y : Scheme.{u}} (V : Y.Opens) :
    chartEquivalence V = Modules.overEquiv V := rfl

attribute [irreducible] chartEquivalence
```

Private helper signature:

```lean
private theorem tensorCounit {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ (_ : (Modules.tensorPullback g).Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        (Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))),
      ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
```

The bounded-flat attachment names
WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat and conclusion
K.IsKFlatTensor. The parent publicly imports
WeilConjectures.AlgebraicGeometry.DerivedPullback. Generic local instances have priority 100;
the item's existing source moduleOverFunctor_additive, moduleOverFunctor_limits and
moduleOverFunctor_colimits instances have local priority 2000. This changes search order
only; all existing public theorem signatures and all definitions are preserved.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare | R4 | Restore complete proof and migrate private counit API; public signature retained. |
| Sheaf.AlgebraicGeometry.BottomFreeChainPullbackComparison | unclaimed, quarantined | Restore direct consumer, migrate public import and adjust local search priorities; theorem and proof body unchanged. |

The absent item has no live Lean importers. tools/downstream.py reports unknown module for
it; searches of both live roots and quarantine identify the direct archived user above.
No quarantined consumer is withdrawn. Further archived consumers remain their own
restoration items. Changing the bounded-flat attachment changes no Lean declaration, so
existing users of either twin require no adaptation. Neither twin is modified or removed.
No target's meaning changes.

## Status

landed 20261020T211820-L-3505528 2026-10-20 (merge of deliver/R4/Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare)
