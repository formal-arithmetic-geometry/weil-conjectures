# AlgebraicGeometry.ProEtale.SmoothExceptionalPasting.reassociationClause

## Reason

The four derived tensor laws repeat large concrete instance expressions. Share
these laws through a generic predicate at the same fixed objects, proving
the conversions from the source whiskering expressions generically. The two localization counit definitions also
cause expensive conversions; expanding these maps once in the predicate allows
direct use of the specialized source equation. These changes preserve every map
and quantifier. There is no new assumption, data choice or hole.

## Old

```lean
def reassociationClause
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) : Prop :=
  ((Etale.upperStar A h).leftDerivedFunctor).map (Etale.derivedTensorAssociator A Z K M N).hom ≫
      (Etale.leftDerivedUpperStarTensorIso A h K
        (((Etale.derivedTensor A Z).obj M).obj N)).hom ≫
      ((Etale.derivedTensor A Y).obj (((Etale.upperStar A h).leftDerivedFunctor).obj K)).map
        (Etale.leftDerivedUpperStarTensorIso A h M N).hom =
    (Etale.leftDerivedUpperStarTensorIso A h
      (((Etale.derivedTensor A Z).obj K).obj M) N).hom ≫
      ((Etale.derivedTensor A Y).map
        (Etale.leftDerivedUpperStarTensorIso A h K M).hom).app _ ≫
      (Etale.derivedTensorAssociator A Y
        (((Etale.upperStar A h).leftDerivedFunctor).obj K)
        (((Etale.upperStar A h).leftDerivedFunctor).obj M)
        (((Etale.upperStar A h).leftDerivedFunctor).obj N)).hom ∧
  ((Etale.upperStar A h).leftDerivedFunctor).map (symmetry A Z K M).hom ≫
      (Etale.leftDerivedUpperStarTensorIso A h M K).hom =
    (Etale.leftDerivedUpperStarTensorIso A h K M).hom ≫
      (symmetry A Y (((Etale.upperStar A h).leftDerivedFunctor).obj K)
        (((Etale.upperStar A h).leftDerivedFunctor).obj M)).hom ∧
  ((Etale.upperStar A h).leftDerivedFunctor).map (Etale.derivedTensorLeftUnitor A Z K).hom =
    (Etale.leftDerivedUpperStarTensorIso A h (𝟙_ _) K).hom ≫
      ((Etale.derivedTensor A Y).map
        (Etale.leftDerivedUpperStarUnitIso A h).hom).app _ ≫
      (Etale.derivedTensorLeftUnitor A Y (((Etale.upperStar A h).leftDerivedFunctor).obj K)).hom ∧
  ((Etale.upperStar A h).leftDerivedFunctor).map (Etale.derivedTensorRightUnitor A Z K).hom =
    (Etale.leftDerivedUpperStarTensorIso A h K (𝟙_ _)).hom ≫
      ((Etale.derivedTensor A Y).obj (((Etale.upperStar A h).leftDerivedFunctor).obj K)).map
        (Etale.leftDerivedUpperStarUnitIso A h).hom ≫
      (Etale.derivedTensorRightUnitor A Y (((Etale.upperStar A h).leftDerivedFunctor).obj K)).hom ∧
  (Etale.leftDerivedUpperStarComp A f (g ≫ h)
      ((f ≫ g) ≫ h) (Category.assoc f g h)).hom.app K ≫
      ((Etale.upperStar A f).leftDerivedFunctor).map ((Etale.leftDerivedUpperStarComp
        A g h).hom.app K) =
    (Etale.leftDerivedUpperStarComp A (f ≫ g) h).hom.app K ≫
      (Etale.leftDerivedUpperStarComp A f g).hom.app
        (((Etale.upperStar A h).leftDerivedFunctor).obj K) ∧
  (∀ B C : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A),
    ((Etale.leftDerivedUpperStarTensorComparison A (f ≫ g)).app B).app C ≫
        ((Etale.leftDerivedUpperStarComp A f g).hom.app B ⊗ₘ
          (Etale.leftDerivedUpperStarComp A f g).hom.app C) =
      (Etale.leftDerivedUpperStarComp A f g).hom.app (B ⊗ C) ≫
        (Etale.upperStar A f).leftDerivedFunctor.map
          (((Etale.leftDerivedUpperStarTensorComparison A g).app B).app C) ≫
        ((Etale.leftDerivedUpperStarTensorComparison A f).app _).app _) ∧
  (∀ C D : HomotopyCategory (Sheaf Z.smallEtaleTopology A) (.up ℤ),
    ((Etale.leftDerivedUpperStarTensorComparison A h).app
        (_root_.DerivedCategory.Qh.obj C)).app (_root_.DerivedCategory.Qh.obj D) ≫
        ((Etale.derivedTensorLeftDerivedUpperStarCounit A h).app C).app D =
      ((Etale.leftDerivedUpperStarDerivedTensorCounit A h).app C).app D ≫
        _root_.DerivedCategory.Qh.map
          (Functor.OplaxMonoidal.δ
            ((Etale.upperStar A h).mapHomotopyCategory (.up ℤ)) C D)) ∧
  (∀ C : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ),
    (Etale.leftDerivedUpperStarComp A f g).hom.app (_root_.DerivedCategory.Qh.obj C) ≫
        (Etale.upperStar A f).leftDerivedFunctor.map
          ((Etale.upperStar A g).leftDerivedFunctorCounit.app C) ≫
        (Etale.upperStar A f).leftDerivedFunctorCounit.app
          (((Etale.upperStar A g).mapHomotopyCategory (.up ℤ)).obj C) =
      (Etale.upperStar A (f ≫ g)).leftDerivedFunctorCounit.app C ≫
        _root_.DerivedCategory.Qh.map
          (Functor.mapHomotopyCategoryCompHom (Etale.upperStar A g)
            (Etale.upperStar A f) (Etale.upperStar A (f ≫ g))
            (Etale.upperStarComp A f g (f ≫ g) rfl) C))
```

## New

```lean
def tensorComparisonCoherenceAt
    {C E : Type*} [Category C] [Category E] [MonoidalCategory C] [MonoidalCategory E]
    (F : C ⥤ E) (δ : ∀ K M, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M)
    (η : F.obj (𝟙_ C) ⟶ 𝟙_ E)
    (s : ∀ K M : C, K ⊗ M ≅ M ⊗ K) (t : ∀ K M : E, K ⊗ M ≅ M ⊗ K)
    (K M N : C) : Prop :=
  (F.map (α_ K M N).hom ≫ δ K (M ⊗ N) ≫ (𝟙 _ ⊗ₘ δ M N) =
    δ (K ⊗ M) N ≫ (δ K M ⊗ₘ 𝟙 _) ≫ (α_ (F.obj K) (F.obj M) (F.obj N)).hom) ∧
  (F.map (s K M).hom ≫ δ M K = δ K M ≫ (t (F.obj K) (F.obj M)).hom) ∧
  (F.map (λ_ K).hom = δ (𝟙_ C) K ≫ (η ⊗ₘ 𝟙 _) ≫ (λ_ (F.obj K)).hom) ∧
  (F.map (ρ_ K).hom = δ K (𝟙_ C) ≫ (𝟙 _ ⊗ₘ η) ≫ (ρ_ (F.obj K)).hom)

def reassociationClause
    (A : Type uA) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (K M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) : Prop :=
  tensorComparisonCoherenceAt (Etale.upperStar A h).leftDerivedFunctor
    (fun K M ↦ ((Etale.leftDerivedUpperStarTensorComparison A h).app K).app M)
    (Etale.leftDerivedUpperStarUnitIso A h).hom
    (fun K M ↦ symmetry A Z K M) (fun K M ↦ symmetry A Y K M) K M N ∧
  (Etale.leftDerivedUpperStarComp A f (g ≫ h)
      ((f ≫ g) ≫ h) (Category.assoc f g h)).hom.app K ≫
      ((Etale.upperStar A f).leftDerivedFunctor).map ((Etale.leftDerivedUpperStarComp
        A g h).hom.app K) =
    (Etale.leftDerivedUpperStarComp A (f ≫ g) h).hom.app K ≫
      (Etale.leftDerivedUpperStarComp A f g).hom.app
        (((Etale.upperStar A h).leftDerivedFunctor).obj K) ∧
  (∀ B C : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A),
    ((Etale.leftDerivedUpperStarTensorComparison A (f ≫ g)).app B).app C ≫
        ((Etale.leftDerivedUpperStarComp A f g).hom.app B ⊗ₘ
          (Etale.leftDerivedUpperStarComp A f g).hom.app C) =
      (Etale.leftDerivedUpperStarComp A f g).hom.app (B ⊗ C) ≫
        (Etale.upperStar A f).leftDerivedFunctor.map
          (((Etale.leftDerivedUpperStarTensorComparison A g).app B).app C) ≫
        ((Etale.leftDerivedUpperStarTensorComparison A f).app _).app _) ∧
  (∀ C D : HomotopyCategory (Sheaf Z.smallEtaleTopology A) (.up ℤ),
    ((Etale.leftDerivedUpperStarTensorComparison A h).app
        (_root_.DerivedCategory.Qh.obj C)).app (_root_.DerivedCategory.Qh.obj D) ≫
        ((Etale.upperStar A h).leftDerivedFunctorCounit.app C ⊗ₘ
          (Etale.upperStar A h).leftDerivedFunctorCounit.app D) ≫
        Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh
          (((Etale.upperStar A h).mapHomotopyCategory (.up ℤ)).obj C)
          (((Etale.upperStar A h).mapHomotopyCategory (.up ℤ)).obj D) =
      (Etale.upperStar A h).leftDerivedFunctor.map
          (Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh C D) ≫
        (Etale.upperStar A h).leftDerivedFunctorCounit.app (C ⊗ D) ≫
        _root_.DerivedCategory.Qh.map
          (Functor.OplaxMonoidal.δ
            ((Etale.upperStar A h).mapHomotopyCategory (.up ℤ)) C D)) ∧
  (∀ C : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ),
    (Etale.leftDerivedUpperStarComp A f g).hom.app (_root_.DerivedCategory.Qh.obj C) ≫
        (Etale.upperStar A f).leftDerivedFunctor.map
          ((Etale.upperStar A g).leftDerivedFunctorCounit.app C) ≫
        (Etale.upperStar A f).leftDerivedFunctorCounit.app
          (((Etale.upperStar A g).mapHomotopyCategory (.up ℤ)).obj C) =
      (Etale.upperStar A (f ≫ g)).leftDerivedFunctorCounit.app C ≫
        _root_.DerivedCategory.Qh.map
          (Functor.mapHomotopyCategoryCompHom (Etale.upperStar A g)
            (Etale.upperStar A f) (Etale.upperStar A (f ≫ g))
            (Etale.upperStarComp A f g (f ≫ g) rfl) C))
```

The first four equations are grouped by `tensorComparisonCoherenceAt`. K, M, N
remain fixed, so this introduces no universal quantifier. Unfolding the predicate,
using `id_tensorHom`, `tensorHom_id`, `leftDerivedUpperStarTensorIso_hom`, and
the source associator/unitor identities, gives exactly the former four maps and laws.
The symmetry is still the original explicitly specified `symmetry`. The grouping
of conjunction changes; its assertions do not. The compositor associativity,
tensor/compositor compatibility and compositor localization clauses are unchanged
verbatim.
The tensor localization square now uses the explicit maps from
`leftDerivedUpperStarTensorComparison_app_app_comp`. They are exactly the old
`derivedTensorLeftDerivedUpperStarCounit` and
`leftDerivedUpperStarDerivedTensorCounit` components: the former expands to the
tensor product of the two pullback counits followed by Qh's lax tensor map;
the latter expands to the pullback of Qh's lax tensor map followed by the
pullback counit. The source theorem proves these two expansion identities
explicitly in its proof. Associativity of morphism composition identifies the
old and new displays. All object quantifiers and maps remain the same.
All existing theorem signatures and source-library definitions are unchanged.
Target meaning needs independent review under the definition-repair rule; the
mathematical assertion and the unit route are unchanged.

## Users

The downstream and textual-use scans find no external textual use of this
predicate. Reading the actual theorem uses confirms that consumers use the
base-pasting and tower-pasting theorems, and do not project coherence fields.
The current scan lists the two downstream modules below. Earlier scans also
listed ChartTargetOpenDescent and DifferenceCoordinateSectionIdentifications;
neither uses these fields. No consumer adaptation is necessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SmoothExceptionalTensorPasting | M2 | Same square with expanded counits; proof updated. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed in local records | Same assertion; no adaptation. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | D4 delivery landed | Same assertion; no adaptation. |

## Status

landed 20261026T001954-L-45953 2026-10-26 (merge of deliver/M2/Sheaf.Paper.SmoothExceptionalTensorPasting)
