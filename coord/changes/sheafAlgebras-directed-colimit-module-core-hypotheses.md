# CategoryTheory.sheafAlgebras_directed_colimit_module_core

## Reason

Repair E7 from reviewer X-e2fff: an arbitrary cocone need not be a module colimit.
Require the sectionwise ring colimit and identify the supplied legs with its
sheafified coprojections. This is the exact requested statement correction.

## Old

```lean
theorem sheafAlgebras_directed_colimit_module_core
    (X : Type u) [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ Under O)
    (p : Cocone (F ⋙ Under.forget O ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat))
    (σ : O ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt)
    (ι : F ⟶ (Functor.const I).obj (Under.mk σ)) :
    Nonempty (IsColimit
      ((commAlgebraSheafModuleFunctor O).mapCocone (Cocone.mk (Under.mk σ) ι)))
```

## New

```lean
theorem sheafAlgebras_directed_colimit_module_core
    (X : Type u) [TopologicalSpace X]
    (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ Under O)
    (p : Cocone (F ⋙ Under.forget O ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat))
    (σ : O ⟶ (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj p.pt)
    (ι : F ⟶ (Functor.const I).obj (Under.mk σ))
    (hp : ∀ U : Opens X, Nonempty (IsColimit
      (((evaluation (Opens X)ᵒᵖ CommRingCat).obj (Opposite.op U)).mapCocone p)))
    (hι : ∀ i : I, (ι.app i).right.hom = p.ι.app i ≫
      toSheafify (Opens.grothendieckTopology X) p.pt) :
    Nonempty (IsColimit
      ((commAlgebraSheafModuleFunctor O).mapCocone (Cocone.mk (Under.mk σ) ι)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SheafAlgebrasDirectedColimitModuleCore | V3 | Add hp and hι binders. |
| Sheaf.CategoryTheory.SheafAlgebrasDirectedColimit | unclaimed | Forced adaptation: pass existing hp and hι at line 81. Signature and visibility unchanged. |

The downstream declaration-use scan found only the core and the caller above.
No target statement or definition changes. The caller's statement already requires
hp and concludes the canonical-leg identity hι; its meaning is unchanged.
The target statements therefore do not require a definition-meaning review.
The blueprint unit route is unchanged.

## Status

landed 20261012T135330-L-1698480 2026-10-12 (merge of deliver/V3/Sheaf.CategoryTheory.SheafAlgebrasDirectedColimitModuleCore)
