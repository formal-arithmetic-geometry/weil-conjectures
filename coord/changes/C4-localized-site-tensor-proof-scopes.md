# SheafOfModules.exists_localizedSiteTensorRestriction

## Reason

The stage-3 static checker classifies added `section`, `variable`, `open` and local
attribute commands as an interface change. This record documents those commands:
they organize private helpers used to construct and prove the canonical comparison.
The theorem signature and all public imports are unchanged. No existing definition
is changed. The private isomorphism lemma is registered only with `[local instance]`
inside `namespace SheafOfModules`, which ends at the end of this module.

## Old

The original public signature is:

```lean
theorem exists_localizedSiteTensorRestriction
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}]
    (A : Sheaf J CommRingCat.{r}) (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{m}] :
    ∃ e : ∀ F G : ringedSiteModules.{m}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A),
        ((siteSheafTensorRight G).obj F).over U ≅
          (siteSheafTensorRight (A := A.over U) (G.over U)).obj (F.over U),
      (∀ (F F' G G' : ringedSiteModules.{m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
          (f : F ⟶ F') (g : G ⟶ G'),
        (((siteSheafTensorRight G).map f ≫ siteSheafTensorSecondMap F' g).over U) ≫
            (e F' G').hom =
          (e F G).hom ≫
            (siteSheafTensorRight (A := A.over U) (G.over U)).map (f.over U) ≫
              siteSheafTensorSecondMap (A := A.over U) (F'.over U) (g.over U)) ∧
      (∀ (F G : ringedSiteModules.{m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
          (V : Over U) (x : F.val.obj (op V.left)) (y : G.val.obj (op V.left)),
        ((e F G).hom.val.app (op V)) (siteSheafTensorTmul F G (op V.left) x y) =
          siteSheafTensorTmul (A := A.over U) (F.over U) (G.over U) (op V) x y) ```

The original context has `open CategoryTheory Opposite` and the namespace
`SheafOfModules`; the theorem proof is `by sorry`.

## New

The public signature is verbatim:

```lean
theorem exists_localizedSiteTensorRestriction
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}]
    (A : Sheaf J CommRingCat.{r}) (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{m}] :
    ∃ e : ∀ F G : ringedSiteModules.{m}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A),
        ((siteSheafTensorRight G).obj F).over U ≅
          (siteSheafTensorRight (A := A.over U) (G.over U)).obj (F.over U),
      (∀ (F F' G G' : ringedSiteModules.{m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
          (f : F ⟶ F') (g : G ⟶ G'),
        (((siteSheafTensorRight G).map f ≫ siteSheafTensorSecondMap F' g).over U) ≫
            (e F' G').hom =
          (e F G).hom ≫
            (siteSheafTensorRight (A := A.over U) (G.over U)).map (f.over U) ≫
              siteSheafTensorSecondMap (A := A.over U) (F'.over U) (g.over U)) ∧
      (∀ (F G : ringedSiteModules.{m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
          (V : Over U) (x : F.val.obj (op V.left)) (y : G.val.obj (op V.left)),
        ((e F G).hom.val.app (op V)) (siteSheafTensorTmul F G (op V.left) x y) =
          siteSheafTensorTmul (A := A.over U) (F.over U) (G.over U) (op V) x y) ```

The proof is complete. Its private helpers occupy the sections
`SheafificationComparison` and `TensorComparison`, with explicit variables for their
existing site, sheafification and module parameters. Both sections end before the
public theorem. `Functor` is opened for the local whiskering expressions.
`tensorOverComparison_isIso` is a proved private lemma, registered by
`attribute [local instance] tensorOverComparison_isIso` inside the namespace.
Each transparency option is scoped to its following declaration with `in`.
Private helpers do not occur in a public signature or a public definition.

## Users

`tools/downstream.py Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
--uses SheafOfModules.exists_localizedSiteTensorRestriction` reports 926 transitive
importers and no downstream module mentioning the theorem. The sole textual use is
its declaration in the item. All public imports and the sole pre-existing signature
are unchanged, and the added instance registration is local; no consumer needs an
adaptation. No target statement or definition it uses changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction | C4 | Complete proof; private helpers and local commands only. |

## Status

landed 20261019T002514-L-2143542 2026-10-19 (merge of deliver/C4/Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction)
