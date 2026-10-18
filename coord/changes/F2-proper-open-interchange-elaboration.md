# AlgebraicGeometry.Etale.properOpenInterchangeCoherence

## Reason

The complete proof exceeded the 60-second limit while Lean compared two definitionally
equal additive structures on sheaf categories: the inherited abelian structure and the
native full-subcategory structure. Prefer `Abelian.toPreadditive` locally when elaborating
this file's derived APIs. With this alignment the complete file compiles without warnings
in 56.0 seconds, with its original statement text unchanged.

The static interface scanner conservatively flags the new `attribute` and `set_option`
commands. The attribute is local to the namespace, the backward elaboration options do not
change definitions, and the local unused-variable linter option accommodates the original
unused proof binders without renaming them. None exports a new instance or changes a
public definition. No target statement or mathematical meaning changes.

## Old

There was no local instance-priority command or backward elaboration option. The existing
public signature was:

```lean
theorem properOpenInterchangeCoherence (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
      (γ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p)),
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (J :
        HomotopyCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map ((lowerStar
        (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusUnit.app J) ≫
        (γ k i r p h).hom.app (DerivedCategory.Plus.Qh.obj J) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusFactorsh.hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomotopyCategoryPlus.obj J) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus (δ k i r p h).hom).app J) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusUnit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomotopyCategoryPlus.obj J) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).map ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlusFactorsh.inv.app J)) ∧
    (∀ {T₁ T₂ X : Scheme.{u}} (p : T₁ ⟶ T₂) [IsProper p]
      (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (h : j₁ ≫ p = j₂) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app K) ≫
        (γ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)).hom.app K =
      properOpenComparison Λ p j₁ j₂ h K) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) r₁) (lowerStar
        (ModuleCat.{u + 1} Λ) r₂) (lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂)).hom.app K) ≫
        (γ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h).hom.app K ≫
        (Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) p₁) (lowerStar
        (ModuleCat.{u + 1} Λ) p₂) (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂)).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (γ i j r₂ p₂ h₂).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r₁).obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₂).map ((γ k i r₁ p₁ h₁).hom.app K)) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (l : B ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroCompDerivedPlusIso Λ i j).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1}
        Λ) r).obj K) ≫
        (γ (k ≫ l) (i ≫ j) r q h).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) q).map ((extensionZeroCompDerivedPlusIso Λ
        k l).inv.app K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map ((γ k i r p
        h₁).hom.app K) ≫
        (γ l j p q h₂).hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        k).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {A B : Scheme.{u}} (k : A ⟶ B) [IsOpenImmersion k]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ k k (𝟙 A) (𝟙 B) ((Category.comp_id k).trans (Category.id_comp k).symm)).hom.app K ≫
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) B).hom.app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) A).hom.app K)) ∧
    (∀ {A C : Scheme.{u}} (r : A ⟶ C) [IsProper r]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ (𝟙 A) (𝟙 C) r r ((Category.id_comp r).trans (Category.comp_id r).symm)).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).map
        ((Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A)) (upperStarId
        (ModuleCat.{u + 1} Λ) A)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C)) (upperStarId
        (ModuleCat.{u + 1} Λ) C)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj K)) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ {A₁ B₁ C₁ D₁ :
        Scheme.{u}}
      (a : B₁ ⟶ B) (b : D₁ ⟶ D) (c : C₁ ⟶ C) (d : A₁ ⟶ A)
      (k₁ : A₁ ⟶ B₁) (i₁ : C₁ ⟶ D₁) (r₁ : A₁ ⟶ C₁) (p₁ : B₁ ⟶ D₁)
      [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
      (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sr : IsPullback d r₁ r c) (sp : IsPullback a p₁ p b)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.map ((γ k i r p h).hom.app K) ≫
        (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sp.toCommSq).app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₁).map
        ((extensionZeroBaseChangeDerivedPlusIso Λ sk).hom.app K) =
      (extensionZeroBaseChangeDerivedPlusIso Λ si).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u
        + 1} Λ) r).obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sr.toCommSq).app K) ≫
        (γ k₁ i₁ r₁ p₁ h₁).hom.app ((upperStar (ModuleCat.{u + 1} Λ) d).mapDerivedCategoryPlus.obj
        K))
```

## New

The following local elaboration commands precede the declarations:

```lean
attribute [local instance 2000] Abelian.toPreadditive
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
```

The original theorem is under `set_option linter.unusedVariables false in` and retains this
identical public signature:

```lean
theorem properOpenInterchangeCoherence (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    ∃ (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
      (γ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p)),
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (J :
        HomotopyCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map ((lowerStar
        (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusUnit.app J) ≫
        (γ k i r p h).hom.app (DerivedCategory.Plus.Qh.obj J) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusFactorsh.hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomotopyCategoryPlus.obj J) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus (δ k i r p h).hom).app J) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctorPlusUnit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomotopyCategoryPlus.obj J) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).map ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlusFactorsh.inv.app J)) ∧
    (∀ {T₁ T₂ X : Scheme.{u}} (p : T₁ ⟶ T₂) [IsProper p]
      (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (h : j₁ ≫ p = j₂) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app K) ≫
        (γ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp j₂).symm)).hom.app K =
      properOpenComparison Λ p j₁ j₂ h K) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) r₁) (lowerStar
        (ModuleCat.{u + 1} Λ) r₂) (lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂)).hom.app K) ≫
        (γ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h).hom.app K ≫
        (Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) p₁) (lowerStar
        (ModuleCat.{u + 1} Λ) p₂) (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂)).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (γ i j r₂ p₂ h₂).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r₁).obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₂).map ((γ k i r₁ p₁ h₁).hom.app K)) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (l : B ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroCompDerivedPlusIso Λ i j).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1}
        Λ) r).obj K) ≫
        (γ (k ≫ l) (i ≫ j) r q h).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) q).map ((extensionZeroCompDerivedPlusIso Λ
        k l).inv.app K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map ((γ k i r p
        h₁).hom.app K) ≫
        (γ l j p q h₂).hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        k).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {A B : Scheme.{u}} (k : A ⟶ B) [IsOpenImmersion k]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ k k (𝟙 A) (𝟙 B) ((Category.comp_id k).trans (Category.id_comp k).symm)).hom.app K ≫
        (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) B).hom.app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) A).hom.app K)) ∧
    (∀ {A C : Scheme.{u}} (r : A ⟶ C) [IsProper r]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (γ (𝟙 A) (𝟙 C) r r ((Category.id_comp r).trans (Category.comp_id r).symm)).hom.app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).map
        ((Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A)) (upperStarId
        (ModuleCat.{u + 1} Λ) A)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C)) (upperStarId
        (ModuleCat.{u + 1} Λ) C)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj K)) ∧
    (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ {A₁ B₁ C₁ D₁ :
        Scheme.{u}}
      (a : B₁ ⟶ B) (b : D₁ ⟶ D) (c : C₁ ⟶ C) (d : A₁ ⟶ A)
      (k₁ : A₁ ⟶ B₁) (i₁ : C₁ ⟶ D₁) (r₁ : A₁ ⟶ C₁) (p₁ : B₁ ⟶ D₁)
      [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
      (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sr : IsPullback d r₁ r c) (sp : IsPullback a p₁ p b)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (upperStar (ModuleCat.{u + 1} Λ) b).mapDerivedCategoryPlus.map ((γ k i r p h).hom.app K) ≫
        (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sp.toCommSq).app ((openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₁).map
        ((extensionZeroBaseChangeDerivedPlusIso Λ sk).hom.app K) =
      (extensionZeroBaseChangeDerivedPlusIso Λ si).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u
        + 1} Λ) r).obj K) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i₁).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sr.toCommSq).app K) ≫
        (γ k₁ i₁ r₁ p₁ h₁).hom.app ((upperStar (ModuleCat.{u + 1} Λ) d).mapDerivedCategoryPlus.obj
        K))
```

## Users

The downstream list is from `tools/downstream.py` with `--uses` for this declaration.
No existing module besides the item is adapted. The only direct existing consumer uses
the constructed derived isomorphism and compiles unchanged. The other listed modules are
transitive importers. Holder status was checked at preparation of this record.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | F2 | Local elaboration context only; identical public statement. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Transitive user only; no declaration or public import changes. No edits. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | unclaimed | Transitive user only; no declaration or public import changes. No edits. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Transitive user only; no declaration or public import changes. No edits. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | Transitive user only; no declaration or public import changes. No edits. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | Transitive user only; no declaration or public import changes. No edits. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | Compiles unchanged against the delivered module (19.3 seconds). No edits. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Transitive user only; no declaration or public import changes. No edits. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | Transitive user only; no declaration or public import changes. No edits. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | Transitive user only; no declaration or public import changes. No edits. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | unclaimed | Transitive user only; no declaration or public import changes. No edits. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Transitive user only; no declaration or public import changes. No edits. |

## Status

landed 20261018T112414-L-631734 2026-10-18 (merge of deliver/F2/Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence)
