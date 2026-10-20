# CategoryTheory.pointSystemRefinementMap

## Reason

The one-cover refinement has preorder indices. The canonical colimit map is needed for
preorders, and in a module of its own so that the posetal replacement and the chain
construction can use it without an import cycle.

`CategoryTheory.pointSystemRefinementMap` is moved, with its signature (PartialOrder
indices) and its body byte for byte unchanged, from `Sheaf.CategoryTheory.PointSystemRefineAll`
to the new module `Sheaf.CategoryTheory.PointSystemRefinementMap`, which the old module
imports publicly (`public import`), so every importer of the old module still sees it.
The preorder generalization is a NEW declaration `CategoryTheory.pointSystemRefinementMapOfPreorder`
with the same body; `pointSystemRefinementMap_eq_ofPreorder` (proved by `rfl`) identifies the
two on partial orders. The assigned theorem signature is byte-for-byte unchanged; no
Challenge target changes.

(Reviewer correction, 2026-10-21: the delivered version changed the signature of
`pointSystemRefinementMap` itself from `[PartialOrder J] [PartialOrder I]` to
`[Preorder J] [Preorder I]`. That broke its user `Sheaf.CategoryTheory.Sites.PointSystemSaturation`,
which passes the instance explicitly, `@pointSystemRefinementMap C _ (sys n).I (sys n).order …`
(line 178: "Application type mismatch: (sys n).order has type PartialOrder (sys n).I but is
expected to have type Preorder (sys n).I"). The old signature is restored and the
generalization renamed.)

## Old

In `Sheaf.CategoryTheory.PointSystemRefineAll`:

```lean
noncomputable def pointSystemRefinementMap
    {C : Type u} [Category.{v} C]
    {J : Type w} [PartialOrder J] {I : Type r} [PartialOrder I]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
    (h : V = e.monotone.functor ⋙ U) (P : Cᵒᵖ ⥤ Type t)
    [HasColimit (V ⋙ P)] [HasColimit (e.monotone.functor ⋙ (U ⋙ P))]
    [HasColimit (U ⋙ P)] : colimit (V ⋙ P) ⟶ colimit (U ⋙ P) :=
  colimMap (Functor.whiskerRight (eqToHom h) P ≫
    (Functor.associator e.monotone.functor U P).hom) ≫
      colimit.pre (U ⋙ P) e.monotone.functor
```

## New

In `Sheaf.CategoryTheory.PointSystemRefinementMap`, publicly re-exported from the old module:
the same declaration, unchanged, and in addition

```lean
noncomputable def pointSystemRefinementMapOfPreorder
    {C : Type u} [Category.{v} C]
    {J : Type w} [Preorder J] {I : Type r} [Preorder I]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
    (h : V = e.monotone.functor ⋙ U) (P : Cᵒᵖ ⥤ Type t)
    [HasColimit (V ⋙ P)] [HasColimit (e.monotone.functor ⋙ (U ⋙ P))]
    [HasColimit (U ⋙ P)] : colimit (V ⋙ P) ⟶ colimit (U ⋙ P) :=
  colimMap (Functor.whiskerRight (eqToHom h) P ≫
    (Functor.associator e.monotone.functor U P).hom) ≫
      colimit.pre (U ⋙ P) e.monotone.functor

theorem pointSystemRefinementMap_eq_ofPreorder … :
    pointSystemRefinementMap V U e h P = pointSystemRefinementMapOfPreorder V U e h P := rfl
```

with the lemmas `pointSystemRefinementMapOfPreorder_ι`, `_eq`, `_comp`, `_naturality`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.PointSystemRefineAll | K3 | Definition moved and publicly re-exported; theorem statement unchanged. |
| Sheaf.CategoryTheory.Sites.PointSystemSaturation | claimed by nobody; unchanged | Uses `CategoryTheory.pointSystemRefinementMap` (also with explicit `PartialOrder` instances and `simp only [pointSystemRefinementMap]` unfolding); the signature and body are unchanged and it is reached through the public import of the old module. Compiled against the corrected delivery. |
| Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints | not determined; unchanged | No direct use. |
| Sheaf.CategoryTheory.Sites.FinitarySliceEnoughPoints | not determined; unchanged | No direct use. |
| Sheaf.Paper.FinitarySiteEnoughPoints | not determined; unchanged | No direct use. |

The new modules PointSystemChain, PointSystemExtensions, PointSystemPosetalRefine and
PointSystemRefinementChainExists use `pointSystemRefinementMapOfPreorder`. There are no
forced adaptations.

## Status

landed 20261020T221232-L-4162099 2026-10-20 (merge of deliver/K3/Sheaf.CategoryTheory.PointSystemRefineAll)
