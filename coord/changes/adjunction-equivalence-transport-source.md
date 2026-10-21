# CategoryTheory.exists_unique_laxMonoidal_adjunction_equivalence_transport

## Reason

Repair the returned delivery against the current source. The module was added
to the main branch by `45eba2ae8c4` after the original delivery base; it is now
present and contains one theorem with `sorry`. Reapply the complete proof to
that file. The earlier record's source-absence description is obsolete.

## Old

The current source has the following signature, verbatim, with body `:= by sorry`:

```lean
theorem exists_unique_laxMonoidal_adjunction_equivalence_transport
    {A : Type u₁} [Category.{v₁} A] [MonoidalCategory A]
    {B : Type u₂} [Category.{v₂} B] [MonoidalCategory B]
    {A' : Type u₃} [Category.{v₃} A'] [MonoidalCategory A']
    {B' : Type u₄} [Category.{v₄} B'] [MonoidalCategory B']
    (E : A ⥤ A') [E.Full] [E.Faithful] [E.EssSurj] (e : E.CoreMonoidal)
    (F : B ⥤ B') [F.Full] [F.Faithful] [F.EssSurj] (f : F.CoreMonoidal)
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    (L' : A' ⥤ B') (R' : B' ⥤ A') (adj' : L' ⊣ R')
    (β : R ⋙ E ≅ F ⋙ R') (γ : L ⋙ F ≅ E ⋙ L')
    (hcompat : ∀ (X : A) (Y : B) (h : L.obj X ⟶ Y),
      E.map (adj.homEquiv X Y h) ≫ β.hom.app Y =
        adj'.homEquiv (E.obj X) (F.obj Y) (γ.inv.app X ≫ F.map h))
    [R'.LaxMonoidal] :
    ∃ r : R.LaxMonoidal,
      (e.εIso.hom ≫ E.map (@Functor.LaxMonoidal.ε B _ _ A _ _ R r) ≫
          β.hom.app (𝟙_ B) =
        Functor.LaxMonoidal.ε R' ≫ R'.map f.εIso.hom) ∧
      (∀ Y Z : B,
        (e.μIso (R.obj Y) (R.obj Z)).hom ≫
            E.map (@Functor.LaxMonoidal.μ B _ _ A _ _ R r Y Z) ≫ β.hom.app (Y ⊗ Z) =
          (β.hom.app Y ⊗ₘ β.hom.app Z) ≫
            Functor.LaxMonoidal.μ R' (F.obj Y) (F.obj Z) ≫ R'.map (f.μIso Y Z).hom) ∧
      (∀ s : R.LaxMonoidal,
        (e.εIso.hom ≫ E.map (@Functor.LaxMonoidal.ε B _ _ A _ _ R s) ≫
            β.hom.app (𝟙_ B) =
          Functor.LaxMonoidal.ε R' ≫ R'.map f.εIso.hom) →
        (∀ Y Z : B,
          (e.μIso (R.obj Y) (R.obj Z)).hom ≫
              E.map (@Functor.LaxMonoidal.μ B _ _ A _ _ R s Y Z) ≫ β.hom.app (Y ⊗ Z) =
            (β.hom.app Y ⊗ₘ β.hom.app Z) ≫
              Functor.LaxMonoidal.μ R' (F.obj Y) (F.obj Z) ≫ R'.map (f.μIso Y Z).hom) →
        s = r) ∧
      (∀ X Y : A,
        F.map ((@Adjunction.leftAdjointOplaxMonoidal A _ _ B _ _ L R adj r).δ X Y) =
          γ.hom.app (X ⊗ Y) ≫ L'.map (e.μIso X Y).inv ≫
            adj'.leftAdjointOplaxMonoidal.δ (E.obj X) (E.obj Y) ≫
            (γ.inv.app X ⊗ₘ γ.inv.app Y) ≫ (f.μIso (L.obj X) (L.obj Y)).hom) ∧
      (F.map (@Adjunction.leftAdjointOplaxMonoidal A _ _ B _ _ L R adj r).η =
        γ.hom.app (𝟙_ A) ≫ L'.map e.εIso.inv ≫
          adj'.leftAdjointOplaxMonoidal.η ≫ f.εIso.hom) ∧
      (((∀ U V : A', IsIso (adj'.leftAdjointOplaxMonoidal.δ U V)) ∧
          IsIso adj'.leftAdjointOplaxMonoidal.η) →
        (∀ X Y : A,
          IsIso ((@Adjunction.leftAdjointOplaxMonoidal A _ _ B _ _ L R adj r).δ X Y)) ∧
        IsIso (@Adjunction.leftAdjointOplaxMonoidal A _ _ B _ _ L R adj r).η)
```

## New

The signature, public imports, visibility and existing docstrings are unchanged.
Replace the theorem's `sorry` by a complete proof. Add the proved private
`liftLax` construction and the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor`. No public declaration
or definition interface is added or changed. There are zero remaining holes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Monoidal.AdjunctionEquivalenceTransport | T2 | Complete proof of its unchanged theorem. |

`tools/downstream.py --uses` reports zero downstream modules and only the
item's own declaration as a text use. Searches of both library roots and
quarantine likewise find no external Lean consumers. The DAG parents
`def-pd-proetale-section-module-functors` and
`lem-pd-section-ordinary-oplax-normalization` keep their existing dependencies.
No target statement, definition or consumer requires adaptation.

## Status

landed 20261021T120536-L-3907892 2026-10-21 (merge of deliver/T2/Sheaf.CategoryTheory.Monoidal.AdjunctionEquivalenceTransport)
