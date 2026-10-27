# AlgebraicGeometry.ProEtale.SmoothExceptionalPasting.chainReassociationClause

## Reason

The expanded four chain tensor laws repeat large concrete monoidal instances. Profiles
show 21.8 seconds in the kernel for the definition alone and 87.3 seconds for the proof
against the old expanded instance. Factor the four laws through a generic predicate,
then use the induced oplax structure whose delta and eta are the recorded chain tensor
comparison and inverse cochain unit isomorphism. The generic laws are proved privately.
The threefold complex equation is likewise shared via the generic
`complexThreefoldComparisonCoherence`. Its parameters are the actual six functors
and four comparison transformations; unfolding it gives the original final
clause, with no new premise. There is no new assumption, data choice, axiom or hole.

## Old

```lean
def chainReassociationClause
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : Prop :=
  let F := (Etale.upperStar A h).mapHomologicalComplex (.up ℤ)
  (∀ K M N : CochainComplex (Sheaf Z.smallEtaleTopology A) ℤ,
    F.map (α_ K M N).hom ≫ chainTensorComparison A h K (M ⊗ N) ≫
        (𝟙 _ ⊗ₘ chainTensorComparison A h M N) =
      chainTensorComparison A h (K ⊗ M) N ≫
        (chainTensorComparison A h K M ⊗ₘ 𝟙 _) ≫
        (α_ (F.obj K) (F.obj M) (F.obj N)).hom) ∧
  (∀ K M : CochainComplex (Sheaf Z.smallEtaleTopology A) ℤ,
    F.map (CochainComplex.Monoidal.braiding K M).hom ≫ chainTensorComparison A h M K =
      chainTensorComparison A h K M ≫
        (CochainComplex.Monoidal.braiding (F.obj K) (F.obj M)).hom) ∧
  (∀ K : CochainComplex (Sheaf Z.smallEtaleTopology A) ℤ,
    F.map (λ_ K).hom = chainTensorComparison A h (𝟙_ _) K ≫
      ((Etale.upperStar A h).mapCochainComplexεIso.inv ⊗ₘ 𝟙 _) ≫ (λ_ (F.obj K)).hom) ∧
  (∀ K : CochainComplex (Sheaf Z.smallEtaleTopology A) ℤ,
    F.map (ρ_ K).hom = chainTensorComparison A h K (𝟙_ _) ≫
      (𝟙 _ ⊗ₘ (Etale.upperStar A h).mapCochainComplexεIso.inv) ≫ (ρ_ (F.obj K)).hom) ∧
  (∀ K : CochainComplex (Sheaf Z.smallEtaleTopology A) ℤ,
    Functor.mapHomologicalComplexCompNatTrans
        (Etale.upperStar A (g ≫ h)) (Etale.upperStar A f)
        (Etale.upperStar A ((f ≫ g) ≫ h))
        (Etale.upperStarComp A f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)).hom K ≫
      ((Etale.upperStar A f).mapHomologicalComplex (.up ℤ)).map
        (Functor.mapHomologicalComplexCompNatTrans (Etale.upperStar A h) (Etale.upperStar A g)
          (Etale.upperStar A (g ≫ h)) (Etale.upperStarComp A g h (g ≫ h) rfl).hom K) =
    Functor.mapHomologicalComplexCompNatTrans (Etale.upperStar A h)
        (Etale.upperStar A (f ≫ g)) (Etale.upperStar A ((f ≫ g) ≫ h))
        (Etale.upperStarComp A (f ≫ g) h ((f ≫ g) ≫ h) rfl).hom K ≫
      Functor.mapHomologicalComplexCompNatTrans (Etale.upperStar A g) (Etale.upperStar A f)
        (Etale.upperStar A (f ≫ g)) (Etale.upperStarComp A f g (f ≫ g) rfl).hom (F.obj K))
```

## New

```lean
def tensorComparisonCoherence
    {C E : Type*} [Category C] [Category E] [MonoidalCategory C] [MonoidalCategory E]
    (F : C ⥤ E) (δ : ∀ K M, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M)
    (η : F.obj (𝟙_ C) ⟶ 𝟙_ E)
    (s : ∀ K M : C, K ⊗ M ≅ M ⊗ K) (t : ∀ K M : E, K ⊗ M ≅ M ⊗ K) : Prop :=
  (∀ K M N, F.map (α_ K M N).hom ≫ δ K (M ⊗ N) ≫ (𝟙 _ ⊗ₘ δ M N) =
    δ (K ⊗ M) N ≫ (δ K M ⊗ₘ 𝟙 _) ≫ (α_ (F.obj K) (F.obj M) (F.obj N)).hom) ∧
  (∀ K M, F.map (s K M).hom ≫ δ M K = δ K M ≫ (t (F.obj K) (F.obj M)).hom) ∧
  (∀ K, F.map (λ_ K).hom = δ (𝟙_ C) K ≫ (η ⊗ₘ 𝟙 _) ≫ (λ_ (F.obj K)).hom) ∧
  (∀ K, F.map (ρ_ K).hom = δ K (𝟙_ C) ≫ (𝟙 _ ⊗ₘ η) ≫ (ρ_ (F.obj K)).hom)

def complexThreefoldComparisonCoherence
    {C0 C1 C2 C3 : Type*} [Category C0] [Category C1] [Category C2] [Category C3]
    [Preadditive C0] [Preadditive C1] [Preadditive C2] [Preadditive C3]
    (F : C0 ⥤ C1) (G : C1 ⥤ C2) (H : C2 ⥤ C3)
    (FG : C0 ⥤ C2) (GH : C1 ⥤ C3) (T : C0 ⥤ C3)
    [F.Additive] [G.Additive] [H.Additive] [FG.Additive] [GH.Additive] [T.Additive]
    (eFG : FG ⟶ F ⋙ G) (eGH : GH ⟶ G ⋙ H)
    (e1 : T ⟶ FG ⋙ H) (e2 : T ⟶ F ⋙ GH)
    : Prop :=
  ∀ K : CochainComplex C0 ℤ,
    Functor.mapHomologicalComplexCompNatTrans FG H T e1 K ≫
        (H.mapHomologicalComplex (.up ℤ)).map
          (Functor.mapHomologicalComplexCompNatTrans F G FG eFG K) =
      Functor.mapHomologicalComplexCompNatTrans F GH T e2 K ≫
        Functor.mapHomologicalComplexCompNatTrans G H GH eGH
          ((F.mapHomologicalComplex (.up ℤ)).obj K)

def chainReassociationClause
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : Prop :=
  let F := (Etale.upperStar A h).mapHomologicalComplex (.up ℤ)
  tensorComparisonCoherence F (Functor.OplaxMonoidal.δ F)
    (Functor.OplaxMonoidal.η F)
    (fun K M ↦ β_ K M)
    (fun K M ↦ β_ K M) ∧
  complexThreefoldComparisonCoherence
    (Etale.upperStar A h) (Etale.upperStar A g) (Etale.upperStar A f)
    (Etale.upperStar A (g ≫ h)) (Etale.upperStar A (f ≫ g))
    (Etale.upperStar A ((f ≫ g) ≫ h))
    (Etale.upperStarComp A g h (g ≫ h) rfl).hom
    (Etale.upperStarComp A f g (f ≫ g) rfl).hom
    (Etale.upperStarComp A f (g ≫ h) ((f ≫ g) ≫ h) (Category.assoc f g h)).hom
    (Etale.upperStarComp A (f ≫ g) h ((f ≫ g) ≫ h) rfl).hom
```

The new conjunction groups the first four equations together, with the same threefold
pullback equality as its second member. Unfolding `tensorComparisonCoherence`, and using
`Functor.mapCochainComplex_δ` and `Functor.mapCochainComplex_η`, gives exactly the old
five equations, up to associativity of logical conjunction. The braiding is now written `β_` using the explicitly prioritized
`CochainComplex.Monoidal.braidedCategory`; its braiding field is exactly the former
`CochainComplex.Monoidal.braiding`, with the same Koszul signs. The monoidal and braiding
maps are therefore the same canonical maps. The source definitions and all five existing theorem
signatures stay unchanged. The meanings of Challenge statements therefore stay unchanged.

## Users

`tools/downstream.py Sheaf.Paper.SmoothExceptionalTensorPasting --uses
chainReassociationClause` finds only this item as a textual user of the predicate.
All four downstream modules are listed here; none projects its conjunction fields,
and none needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SmoothExceptionalTensorPasting | M2 | Equivalent predicate representation; proof updated. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed in local records | Same mathematical assertion; no adaptation. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed in local records | Same mathematical assertion; no adaptation. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed in local records | Same mathematical assertion; no adaptation. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | D4 delivery landed | Same mathematical assertion; no adaptation. |

## Status

landed 20261026T001954-L-45953 2026-10-26 (merge of deliver/M2/Sheaf.Paper.SmoothExceptionalTensorPasting)
