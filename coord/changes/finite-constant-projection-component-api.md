# finiteConstantProjectionComponent_isIso

## Reason

The finite-coefficient direct-image argument needs the canonical projection component
before the constant-pullback identification. Unfolding the complete composite
`finiteConstantProjectionMap` to cancel the final isomorphisms makes kernel checking
repeat expensive derived-functor reductions. The original proof already establishes
exactly this component as its intermediate `hα`. Name that intermediate as a proved
private theorem in the same module; both the existing theorem and the new consumer
use it. The module is unclaimed. This preserves every existing public signature,
attribute, import and definition, and retains its complete proof. No source-library
module is changed.

## Old

```lean
theorem isIso_finiteConstantProjectionMap
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (hcd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ),
      N < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))
    (K : DerivedCategoryModule A X)
    (hK : ∃ b : ℤ, ∀ q : ℤ, b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (M : ModuleCat.{u + 1} A) [Module.FinitePresentation A M] :
    IsIso ((finiteConstantProjectionMap A f K).app M)
```

The theorem's original proof first proves `hα`, the projection component is invertible,
and then composes with constant-pullback identifications.

## New

The existing public signature above stays verbatim. The original proof up to `hα`
is named by this private declaration:

```lean
private theorem finiteConstantProjectionComponent_isIso
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (hcd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ),
      N < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))
    (K : DerivedCategoryModule A X)
    (hK : ∃ b : ℤ, ∀ q : ℤ, b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (M : ModuleCat.{u + 1} A) [Module.FinitePresentation A M] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)))
```

The original public theorem applies this helper and retains its original final
composition proof. The item uses `import all` to access the proved private API;
other importers see no additional public declarations.

## Users

`tools/downstream.py ... --uses finiteConstantProjectionMap
isIso_finiteConstantProjectionMap` lists the following textual consumers. All
343 transitive downstream modules retain the same public interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula | unclaimed | Names the existing intermediate proof, then applies it in the unchanged public theorem. |
| Sheaf.Paper.DirectImageTorAmplitude | unclaimed | No change; both used public declarations and all definitions remain identical. |
| Sheaf.Paper.FiniteCoefficientDirectImage | C4 | New proof consumer of the private component theorem; existing public signatures unchanged. |

## Status

landed 20261020T233102-L-892381 2026-10-20 (merge of deliver/C4/Sheaf.Paper.FiniteCoefficientDirectImage)
