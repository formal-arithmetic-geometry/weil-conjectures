# AlgebraicGeometry.Scheme.Modules.scalar_moduleCohomologyPullback_comparison

## Reason

The delivery tool's static check classifies changes to file-level open, variable, and
attribute commands as a change to what importers see. The proof needs additional
universes for its private generic Ext calculation, Opposite and TopologicalSpace names,
and local typeclass registrations. All registrations added here are local; all new
helper declarations are private. The two public imports, theorem name, binders,
universes, hypotheses, and conclusion are preserved. No definition used by a target
changes. This record documents the proof context for independent review.

## Old

theorem scalar_moduleCohomologyPullback_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : X.Modules) (n : ℕ)
    (x : scalarCohomology f F n) :
    scalarCohomologyPullback f g a h F n x = moduleCohomologyPullback a F n x

## New

theorem scalar_moduleCohomologyPullback_comparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) (h : a ≫ f = g) (F : X.Modules) (n : ℕ)
    (x : scalarCohomology f F n) :
    scalarCohomologyPullback f g a h F n x = moduleCohomologyPullback a F n x

The signature is unchanged. Its previous proof was by sorry; its new proof compares
the actual module-resolution choices with scalar Ext cocycles. The local instances
and private helpers are scoped within the module and supply no new public API.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison | B2 | theorem proved, signature preserved |
| Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison | not checked; no adaptation | importing this theorem needs no source change |

No other existing module is included or adapted by the delivery.

## Status

landed 20261014T104636-L-1525798 2026-10-14 (merge of deliver/B2/Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison)
