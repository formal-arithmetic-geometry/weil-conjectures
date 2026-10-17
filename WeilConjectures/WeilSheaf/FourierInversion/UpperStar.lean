/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.UpperStarId
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarWeil

/-!
# Fourier inversion: pullback of Weil complexes

Composition and identity for the pullback of Weil complexes, and its compatibility with the
tensor product with a lisse Weil sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Pullback of Weil complexes is compatible with composition: `(f ≫ g)^* ≅ f^* ∘ g^*`. -/
theorem WeilComplex.nonempty_iso_upperStar_comp {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.upperStar (k₀ := k₀) (l := l) (f ≫ g) ≅
      WeilComplex.upperStar g ⋙ WeilComplex.upperStar f) :=
  ⟨WeilComplex.upperStarCompIso f g⟩

/-- Pullback of Weil complexes along the identity is the identity. -/
theorem WeilComplex.nonempty_iso_upperStar_id {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.upperStar (k₀ := k₀) (l := l) (𝟙 X) ≅ 𝟭 _) :=
  ⟨WeilComplex.upperStarIdIso X⟩


/-- The dual of the pullback of a lisse Weil sheaf is the pullback of its dual. -/
noncomputable def WeilSheaf.upperStarDualIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    ((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ≅
      (WeilSheaf.upperStar φ).obj (G.dual hG) :=
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.ihomFunctor k₀ l X ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj G.obj)).mapIso
        ((ObjectProperty.ι _).mapIso (WeilSheaf.upperStarAdicConstantIso φ)).symm ≪≫
      ((ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso φ G.obj hG).app
        (ProEtaleWeilSheaf.adicConstant k₀ l Y)).symm)

/-- Pullback of pro-étale Weil sheaves commutes with the internal hom out of the dual of a lisse
Weil sheaf. -/
noncomputable def ProEtaleWeilSheaf.ihomFunctorDualCompUpperStarIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    ProEtaleWeilSheaf.ihomFunctor k₀ l Y (G.dual hG).obj ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ ≅
      ProEtaleWeilSheaf.upperStar k₀ l φ ⋙ ProEtaleWeilSheaf.ihomFunctor k₀ l X
        (((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj :=
  ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso φ (G.dual hG).obj hG.dual ≪≫
    Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.ihomFunctorMapIsoLeft
      ((ObjectProperty.ι _).mapIso (WeilSheaf.upperStarDualIso φ G hG)))

/-- Pullback commutes with the tensor product with a lisse Weil sheaf:
`φ^*(G ⊗ K) ≅ φ^* G ⊗ φ^* K`. -/
theorem WeilComplex.nonempty_iso_tensorLisse_comp_upperStar {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    Nonempty (WeilComplex.tensorLisse G hG ⋙ WeilComplex.upperStar φ ≅
      WeilComplex.upperStar φ ⋙ WeilComplex.tensorLisse ((WeilSheaf.upperStar φ).obj G)
        (ProEtale.IsAdicLisseSheaf.upperStar _ hG)) := by
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (G.dual hG).obj hG.dual
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor
    (((WeilSheaf.upperStar φ).obj G).dual (ProEtale.IsAdicLisseSheaf.upperStar _ hG)).obj
    (ProEtale.IsAdicLisseSheaf.upperStar _ hG).dual
  exact ⟨((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (WeilComplex.ihomLisseCompιIso _ hG.dual) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory _) _ ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryNatIso
            (ProEtaleWeilSheaf.ihomFunctorDualCompUpperStarIso φ G hG) ≪≫
          Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorIsoMapDerivedCategory _).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (WeilComplex.ihomLisseCompιIso _ _).symm ≪≫
      (Functor.associator _ _ _).symm)⟩


end AlgebraicGeometry
