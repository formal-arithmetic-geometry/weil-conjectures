# CategoryTheory.exists_ext_rightDerived_cocycle_comparison

## Reason

The existing public Ext/derived-Hom and site-cohomology comparisons do not expose their
values on resolution cocycles. Add the strictly smaller single-category normalization
statement needed to combine those computations across a continuous map. The existing
terminal-resolution theorem keeps its signature and is proved from this new statement.

## Old

The new theorem was absent. The existing declaration
`CategoryTheory.exists_topological_terminal_resolution_ext_comparison` had its unchanged
signature and the proof `:= by sorry`.

## New

```lean
theorem exists_ext_rightDerived_cocycle_comparison
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
    [HasInjectiveResolutions C] (A : C) (H : C ⥤ AddCommGrpCat.{v}) [H.Additive]
    (e : preadditiveCoyoneda.obj (op A) ≅ H) :
    ∃ x : ∀ n : ℕ, H.rightDerived n ≅ (Abelian.extFunctor n).obj (op A),
      ∀ (Y : C) (I : InjectiveResolution Y) (p : ℕ)
        (s : A ⟶ I.cocomplex.X p) (hs : s ≫ I.cocomplex.d p (p + 1) = 0)
        (c : ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles p)
        (hc : ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles p c =
          e.hom.app (I.cocomplex.X p) s),
        (I.isoRightDerivedObj H p).hom ((x p).inv.app Y (I.extMk s (p + 1) rfl hs)) =
          ((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ p c
```

The new theorem is the sole added sorry, in a module of its own. The original module uses
canonical instances directly; the earlier attempt's local instance caches have been removed.
Existing statements and public imports remain identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.TopologicalTerminalResolutionExtComparison | T1 | Applies the new normalization theorem at X and Z, then proves terminal transport and the homology formula. |

No pre-existing module uses the newly added declaration. Existing
importers use the same terminal-resolution theorem with its unchanged signature and need
no adaptation. No target statement or target definition changes.

## Status

landed 20261013T015615-L-3027390 2026-10-13 (merge of deliver/T1/Sheaf.Topology.TopologicalTerminalResolutionExtComparison)
