# AlgebraicGeometry.Etale.higherDirectImageRawTrianglePullback

## Reason

The completed proof repeatedly exceeded the 60-second single-file limit during checking
of the specialized derived-category expression. Factor the existing construction through
`rawTriangleMap`, a generic composite of the same four morphisms, and state the proved
private naturality calculation using that construction. The public definition now
instantiates the generic construction. This shares the construction between the data and
proof instead of repeatedly comparing expanded specialized expressions. The diagnostic
file compiled in 53.9 seconds; its one whitespace warning was removed afterward.

This is a definitional refactor: unfolding `rawTriangleMap`, `Functor.whiskerLeft_app`
and `Functor.comp_obj` gives the old body, with identical factors and ordering.
No existence witness, assumption, or mathematical notion is added. Every existing
signature, visibility, and import stays identical. No target or definition used to
form a target statement changes mathematically. There are no forced adaptations. A separate compiled `rfl` check establishes equality
with the verbatim old composite for every parameter; it is preserved under
`scratchpad/definition-check/lean/Sheaf/AlgebraicGeometry/RawTriangleDefinitionCheck.lean`.

## Old

```lean
noncomputable def higherDirectImageRawTrianglePullback
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale)
    (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (higherDirectImagePresheaf Λ h' q K').obj (op U) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom.app _) ≫
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    D+((a)^*[ModuleCat.{u + 1} Λ]).map z ≫
    (D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
    (shiftFunctor _ q).map v
```

## New

```lean
/-- The map on represented classes obtained from two comparison natural transformations
and a fixed coefficient morphism. This is the categorical formula for raw triangle pullback;
its factors are the comparisons used in Stacks Project, Tags 03Q8 and 09Z1. -/
def rawTriangleMap
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    [Preadditive D'] [Preadditive E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F)
    (U : C) {K : D'} {K' : E'}
    (z : ((H ⋙ A).op ⋙ preadditiveYoneda.obj K).obj (op U))
    (s : F.obj K ⟶ K') :
    ((H' ⋙ B).op ⋙ preadditiveYoneda.obj K').obj (op U) :=
  B.map (c.app U) ≫ e.app (H.obj U) ≫ F.map z ≫ s

/-- Pullback of a derived class, followed by a specified coefficient morphism. The
coefficient morphism is given data, and no witness is chosen from an existence theorem. -/
noncomputable def higherDirectImageRawTrianglePullback
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale)
    (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (higherDirectImagePresheaf Λ h' q K').obj (op U) :=
  rawTriangleMap
    ((freeSheaf Λ S) ⋙ (h)^*[ModuleCat.{u + 1} Λ])
    ((freeSheaf Λ S) ⋙ (h')^*[ModuleCat.{u + 1} Λ])
    ((a)^*[ModuleCat.{u + 1} Λ])
    (DerivedCategory.Plus.singleFunctor _ 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    D+((a)^*[ModuleCat.{u + 1} Λ])
    (Functor.whiskerLeft (freeSheaf Λ S)
      (upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom)
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv
    U z ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
      (shiftFunctor _ q).map v)
```

## Users

`tools/downstream.py ... --uses higherDirectImageRawTrianglePullback` lists these
three modules using the name. The other 205 transitive importers do not mention it;
they retain the same declarations and the same definition after unfolding.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality | E4 | Same definition after unfolding `rawTriangleMap`; signatures unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTransitionToHom | W3 | Same definition after unfolding `rawTriangleMap`; signatures unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback | B3 | Same definition after unfolding `rawTriangleMap`; signatures unchanged. |

## Status

landed 20261013T131322-L-4032748 2026-10-13 (merge of deliver/B3/Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback)
