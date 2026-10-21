# CategoryTheory.RingedHomColimitTransport.source_transport

## Reason

Fill the existing theorem proof. Preflight classifies the added section commands
and local attributes as an interface change, so this record documents them.
`noncomputable section` permits private functor constructions. The local
`irreducible` attributes on `homComplexFunctor`, `homComplexπ`, and
`derivedInternalHomOfUniverses` prevent unfolding large chosen constructions
while proving component identities. They are local to this module. The added
private declarations are fully proved. All public imports, signatures, and
non-proof definition bodies remain verbatim; no consumer adaptation is needed.

## Old

```lean
theorem source_transport [IsFiltered I] :
    ∃ (G : (D.{c, v, r, w} J R)ᵒᵖ ⥤
        (I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R)
      (rho : DerivedCategory.Q.op ⋙ G ≅ strictColimit.{c, v, r, w} J R)
      (alpha : G ⟶ target.{c, v, r, w} J R)
      (t : ∀ (A : D.{c, v, r, w} J R) (n : ℤ),
        G.obj (op (A⟦n⟧)) ≅ G.obj (op A) ⋙ shiftFunctor _ (-n)),
      (∀ (L : Complex.{c, v, r} J R) (N : I ⥤ Complex.{c, v, r} J R),
        (alpha.app (op (DerivedCategory.Q.obj L))).app N =
          (rho.hom.app (op L)).app N ≫
            DerivedCategory.Q.map (colimit.post N
              (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L)) ≫
            (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L
              (colimit N)).inv) ∧
      (∀ (A A' : D.{c, v, r, w} J R) (e : A ≅ A')
        (N : I ⥤ Complex.{c, v, r} J R),
        (G.mapIso e.op).hom.app N ≫ (alpha.app (op A)).app N =
          (alpha.app (op A')).app N ≫
            ((target.{c, v, r, w} J R).mapIso e.op).hom.app N) ∧
      (∀ (A : D.{c, v, r, w} J R) (n : ℤ)
        (N : I ⥤ Complex.{c, v, r} J R),
        (alpha.app (op (A⟦n⟧))).app N ≫
            (sourceShift.{c, v, r, w} J R A n).inv.app
              (DerivedCategory.Q.obj (colimit N)) =
          (t A n).hom.app N ≫ ((alpha.app (op A)).app N)⟦-n⟧') ∧
      (∀ (L : Complex.{c, v, r} J R) (n : ℤ),
        ∃ sigma : WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R (L⟦n⟧) ≅
            WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L ⋙
              shiftFunctor _ (-n),
          (∀ M : Complex.{c, v, r} J R,
            LeftFormula.{c, v, r} J R L
              ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M) n
              (sigma.symm.app M)) ∧
          ∀ N : I ⥤ Complex.{c, v, r} J R,
            (rho.inv.app (op (L⟦n⟧))).app N ≫
                (G.map ((DerivedCategory.Q.commShiftIso n).inv.app L).op).app N ≫
                (t (DerivedCategory.Q.obj L) n).hom.app N =
              DerivedCategory.Q.map (colim.map (Functor.whiskerLeft N sigma.hom) ≫
                  (preservesColimitIso (shiftFunctor (Complex.{c, v, r} J R) (-n))
                    (N ⋙ WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r}
                      J R L)).inv) ≫
                (DerivedCategory.Q.commShiftIso (-n)).hom.app
                  (colimit (N ⋙ WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r}
                    J R L)) ≫
                ((rho.inv.app (op L)).app N)⟦-n⟧')
```

The proof body was `by sorry`. No local irreducibility attributes or private
proof helpers were present.

## New

```lean
theorem source_transport [IsFiltered I] :
    ∃ (G : (D.{c, v, r, w} J R)ᵒᵖ ⥤
        (I ⥤ Complex.{c, v, r} J R) ⥤ D.{c, v, r, w} J R)
      (rho : DerivedCategory.Q.op ⋙ G ≅ strictColimit.{c, v, r, w} J R)
      (alpha : G ⟶ target.{c, v, r, w} J R)
      (t : ∀ (A : D.{c, v, r, w} J R) (n : ℤ),
        G.obj (op (A⟦n⟧)) ≅ G.obj (op A) ⋙ shiftFunctor _ (-n)),
      (∀ (L : Complex.{c, v, r} J R) (N : I ⥤ Complex.{c, v, r} J R),
        (alpha.app (op (DerivedCategory.Q.obj L))).app N =
          (rho.hom.app (op L)).app N ≫
            DerivedCategory.Q.map (colimit.post N
              (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L)) ≫
            (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L
              (colimit N)).inv) ∧
      (∀ (A A' : D.{c, v, r, w} J R) (e : A ≅ A')
        (N : I ⥤ Complex.{c, v, r} J R),
        (G.mapIso e.op).hom.app N ≫ (alpha.app (op A)).app N =
          (alpha.app (op A')).app N ≫
            ((target.{c, v, r, w} J R).mapIso e.op).hom.app N) ∧
      (∀ (A : D.{c, v, r, w} J R) (n : ℤ)
        (N : I ⥤ Complex.{c, v, r} J R),
        (alpha.app (op (A⟦n⟧))).app N ≫
            (sourceShift.{c, v, r, w} J R A n).inv.app
              (DerivedCategory.Q.obj (colimit N)) =
          (t A n).hom.app N ≫ ((alpha.app (op A)).app N)⟦-n⟧') ∧
      (∀ (L : Complex.{c, v, r} J R) (n : ℤ),
        ∃ sigma : WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R (L⟦n⟧) ≅
            WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L ⋙
              shiftFunctor _ (-n),
          (∀ M : Complex.{c, v, r} J R,
            LeftFormula.{c, v, r} J R L
              ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj M) n
              (sigma.symm.app M)) ∧
          ∀ N : I ⥤ Complex.{c, v, r} J R,
            (rho.inv.app (op (L⟦n⟧))).app N ≫
                (G.map ((DerivedCategory.Q.commShiftIso n).inv.app L).op).app N ≫
                (t (DerivedCategory.Q.obj L) n).hom.app N =
              DerivedCategory.Q.map (colim.map (Functor.whiskerLeft N sigma.hom) ≫
                  (preservesColimitIso (shiftFunctor (Complex.{c, v, r} J R) (-n))
                    (N ⋙ WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r}
                      J R L)).inv) ≫
                (DerivedCategory.Q.commShiftIso (-n)).hom.app
                  (colimit (N ⋙ WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r}
                    J R L)) ≫
                ((rho.inv.app (op L)).app N)⟦-n⟧')
```

The proof is complete. The local attributes and noncomputable section affect
elaboration of its private helpers only. The public definitions `strictColimit`
and `target` retain their original signatures and bodies verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RHomColimitSourceTransport | U5 | Existing hole filled; public interface unchanged. |
| Sheaf.Paper.RHomColimitCohomologyLadder | unclaimed | Calls the same theorem with the same signature; no edit. |

`tools/downstream.py --uses` lists precisely these two theorem users. The
transitive module consumers `Sheaf.Paper.CondensedLocalizationHom` and
`Sheaf.Paper.StratifiedDualizableHomContinuity` are likewise unaffected. No
upstream/source-library module or definition is changed.

## Status

landed 20261021T165940-L-2312331 2026-10-21 (merge of deliver/U5/Sheaf.Algebra.Homology.RHomColimitSourceTransport)
