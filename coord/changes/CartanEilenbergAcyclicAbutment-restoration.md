# CategoryTheory.exists_cartanEilenberg_acyclic_abutment

## Reason

Restore the quarantined module assigned by `coord/rework.tsv` (the cluster restore
removed its library file). The archived theorem already has a complete assembly
proof from the three declared dependencies. Preserve its full signature, proof,
public imports, private imports, node attachment and dependency route. No
statement or definition changes, and no target meaning changes.

## Old

The library file is absent. Its preserved source is
`quarantine/Sheaf/CategoryTheory/CartanEilenbergAcyclicAbutment.lean`.

## New

Restore that source verbatim, including this theorem signature:

```lean
theorem exists_cartanEilenberg_acyclic_abutment
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (E : A ⥤ E₂CohomologicalSpectralSequence C)
    (L : ∀ P : CartanEilenbergPresentation F, DecreasingFiltration (P.total G))
    (c : ∀ X : A, E.obj X ≅ (F.grothendieckSpectralObject G X).E₂SpectralSequence)
    (hL : ∀ (P : CartanEilenbergPresentation F) (p n : ℤ),
        (L P).complexStep p n =
          ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration n).step p)) :
    ∃ (h : ∀ (P : CartanEilenbergPresentation F) (n : ℕ),
        (P.total G).homology (n : ℤ) ≅ ((F ⋙ G).rightDerived n).obj P.X)
      (HF : ∀ (X : A) (n : ℕ), DecreasingFiltration (((F ⋙ G).rightDerived n).obj X)),
      (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q) (n : ℕ),
        HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
          ((CartanEilenbergPresentation.mappedFunctor G).map c.α)
            (ComplexShape.up ℤ)) (n : ℤ) ≫ (h Q n).hom =
          (h P n).hom ≫ ((F ⋙ G).rightDerived n).map c.f) ∧
      (∀ P : CartanEilenbergPresentation F,
        ∃ a : (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex).extend
            ComplexShape.embeddingUpNat ⟶ P.total G,
          (∀ n : ℕ, a.f (n : ℤ) =
            (HomologicalComplex.extendXIso
              (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
              ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
            G.map (F.map (P.J.cocomplex.extendXIso ComplexShape.embeddingUpNat
              (rfl : (n : ℤ) = n)).inv ≫ (P.e.f (n : ℤ)).f 0) ≫
            (HomologicalComplex.extendXIso
              ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (P.I.X (n : ℤ)))
              ComplexShape.embeddingUpNat (rfl : (0 : ℤ) = 0)).inv ≫
            HomologicalComplex₂.ιTotalOrZero
              ((CartanEilenbergPresentation.mappedFunctor G).obj P.I)
              (ComplexShape.up ℤ) (n : ℤ) 0 (n : ℤ)) ∧
          (∀ n : ℕ, HomologicalComplex.homologyMap a (n : ℤ) ≫ (h P n).hom =
            (HomologicalComplex.extendHomologyIso
              (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
              ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
              (P.J.isoRightDerivedObj (F ⋙ G) n).inv)) ∧
      (∀ (P : CartanEilenbergPresentation F) (p : ℤ) (n : ℕ),
        (HF P.X n).step p = imageSubobject
          (HomologicalComplex.homologyMap ((L P).step p).arrow (n : ℤ) ≫ (h P n).hom)) ∧
      (∀ (X : A) (p q : ℕ) (r : ℤ) (hr : 2 ≤ r),
        max (p : ℤ) ((q : ℤ) + 1) < r →
          Nonempty (((E.obj X).page r hr).X ((p : ℤ), (q : ℤ)) ≅
            (HF X (p + q)).gradedPiece (p : ℤ))) ∧
      (∀ (X Y : A) (f : X ⟶ Y) (n : ℕ) (p : ℤ),
        ∃ a : ((HF X n).step p : C) ⟶ ((HF Y n).step p : C),
          a ≫ ((HF Y n).step p).arrow =
            ((HF X n).step p).arrow ≫ ((F ⋙ G).rightDerived n).map f) ∧
      (∀ (P : CartanEilenbergPresentation F) (n p : ℕ),
        (HF P.X n).step (p : ℤ) =
          (Subobject.«exists» ((F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app P.X)).obj
            ((F.grothendieckSpectralObject G P.X).imageFiltration (n : ℤ)
              ((n : ℤ) + 1 - (p : ℤ))))
```

## Users

`tools/downstream.py` reports `unknown module(s)` because the assigned module is
absent. Source searches in `lean/Sheaf`, `lean/WeilConjectures` and `quarantine`
find the following sole direct importer and theorem user. The parent is also
quarantined; its proof still calls this theorem with its original signature.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.GrothendieckSpectralSequence | unclaimed in shared snapshot | Original archived theorem application preserved; no adaptation. |

No source-library module is edited. No definition changes and no consumer
adaptations are required. The existing DAG proof and attachment remain accurate.

## Status

landed 20261021T011019-L-2028779 2026-10-21 (merge of deliver/G2/Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment)
