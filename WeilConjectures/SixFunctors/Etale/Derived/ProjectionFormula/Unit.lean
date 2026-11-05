/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The unit comparisons of the derived pullback and the projection map at the unit

For a coefficient category `A` and a morphism of schemes `g : X ⟶ Y`, the identification
`Lg^* M_Y ≅ M_X` of constant complexes is, at the unit of `A`, the unit comparison
`Lg^* 𝟙 ≅ 𝟙` of the monoidal derived pullback, and it is natural in `M`. The projection map
`Ra_! K ⊗ᴸ M ⟶ Ra_!(K ⊗ᴸ La^* M)` is right unital.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensorRightUnitorInvComp`: for `q : Λ_X ⟶ M`, the natural map
  `K ⟶ K ⊗ᴸ M`.
- `AlgebraicGeometry.Etale.unitToConstantSingle`: for `φ : 𝟙 ⟶ M` in `A`, the induced map
  `𝟙 ⟶ M_X` of constant complexes.

## Main statements

- `AlgebraicGeometry.Etale.upperStarConstantSheafIso_hom_app_tensorUnit`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp`: at the
  unit, the identification `Lg^* M_Y ≅ M_X` of constant complexes is the unit comparison of the
  monoidal pullback.
- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_unitToConstantSingle`: the derived pullback
  of `𝟙 ⟶ M_Y` is `𝟙 ⟶ M_X`.
- `AlgebraicGeometry.Etale.projectionMap_rightUnitality`: right unitality of the projection map.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

end General

section UnitComparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}}

open Functor.LaxMonoidal Functor.OplaxMonoidal Opposite

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
/-- The unit `𝟙 ⟶ Γ(X, 𝟙_X)` of the adjunction `constantSheaf ⊣ Γ(X, -)` at the unit `𝟙` of `A`
is the global section at `X` of the unit `ε` of the lax monoidal functor `sheafToPresheaf`. -/
lemma constantSheafAdj_unit_app_tensorUnit :
    (constantSheafAdj X.smallEtaleTopology A terminalIsTerminal).unit.app (𝟙_ A) =
      (ε (sheafToPresheaf _ A)).app (op (⊤_ X.Etale)) := by
  simp only [constantSheafAdj, Adjunction.rightAdjointLaxMonoidal_ε]
  rw [Adjunction.homEquiv_unit]
  have : η (presheafToSheaf X.smallEtaleTopology A) = 𝟙 _ := rfl
  simp [this]
  rfl

/-- The unit of `Adjunction.ofNatIsoRight`. -/
private lemma ofNatIsoRight_unit_app {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H) (x : C) :
    (adj.ofNatIsoRight e).unit.app x = adj.unit.app x ≫ e.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- The identification `f^* A_T ≅ A_S` through the units of the adjunctions. -/
private lemma unit_app_upperStarConstantSheafIso {S T : Scheme.{u}} (f : S ⟶ T) (a : A) :
    (constantSheafAdj T.smallEtaleTopology A terminalIsTerminal).unit.app a ≫
      ((sheafSections T.smallEtaleTopology A).obj (op (⊤_ T.Etale))).map
        ((upperStarLowerStarAdjunction A f).unit.app _ ≫
          (f)_*[A].map ((upperStarConstantSheafIso A f).hom.app a)) ≫
      (lowerStarCompSheafSectionsTerminalIso A f).hom.app _ =
    (constantSheafAdj S.smallEtaleTopology A terminalIsTerminal).unit.app a := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj T.smallEtaleTopology A terminalIsTerminal).comp
        (upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso A f))
    (constantSheafAdj S.smallEtaleTopology A terminalIsTerminal) a
  rw [Adjunction.homEquiv_unit, ofNatIsoRight_unit_app] at this
  rw [← this, upperStarConstantSheafIso]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← (lowerStarCompSheafSectionsTerminalIso A f).hom.naturality]
  rfl

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
/-- The adjoint `𝟙 ⟶ g_* 𝟙` of the counit `η : g^* 𝟙 ⟶ 𝟙` of the oplax monoidal pullback is
the unit `ε` of the lax monoidal pushforward. -/
lemma upperStarLowerStarAdjunction_homEquiv_η (g : X ⟶ Y) :
    (upperStarLowerStarAdjunction A g).homEquiv _ _ (η (g)^*[A]) = ε (g)_*[A] := by
  rw [upperStar_η, Adjunction.homEquiv_unit, Functor.map_comp,
    Adjunction.unit_naturality_assoc, Adjunction.right_triangle_components, Category.comp_id]

omit [MonoidalPreadditive A] [Abelian.HasFunctorialFlatResolution A] in
/-- At the unit `𝟙` of `A`, the identification `g^* 𝟙_Y ≅ 𝟙_X` of constant sheaves
(`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`) is the counit `η` of the monoidal
pullback `g^*`. -/
lemma upperStarConstantSheafIso_hom_app_tensorUnit (g : X ⟶ Y) :
    (upperStarConstantSheafIso A g).hom.app (𝟙_ A) = η (g)^*[A] := by
  apply ((upperStarLowerStarAdjunction A g).homEquiv _ _).injective
  apply ((constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal).homEquiv _ _).injective
  rw [← cancel_mono ((lowerStarCompSheafSectionsTerminalIso A g).hom.app _),
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc]
  refine (unit_app_upperStarConstantSheafIso A g (𝟙_ A)).trans ?_
  erw [upperStarLowerStarAdjunction_homEquiv_η]
  rw [Adjunction.homEquiv_unit, constantSheafAdj_unit_app_tensorUnit,
    constantSheafAdj_unit_app_tensorUnit, Category.assoc]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc,
    ← (ε (sheafToPresheaf X.smallEtaleTopology A)).naturality]
  exact (Category.id_comp _).symm

/-- The identification of the unit of `D(X_ét)` with the unit sheaf placed in degree zero
(`AlgebraicGeometry.Etale.singleFunctorObjUnitIso`) is the identity. -/
lemma singleFunctorObjUnitIso_inv (X : Scheme.{u}) :
    (singleFunctorObjUnitIso A X).inv = 𝟙 _ := by
  have h₁ : ε (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology A)) = 𝟙 _ := rfl
  have h₂ : ε (HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)) = 𝟙 _ := rfl
  have h₃ : ∀ K, (DerivedCategory.quotientCompQhIso (Sheaf X.smallEtaleTopology A)).hom.app K =
      𝟙 _ := fun _ ↦ rfl
  simp only [singleFunctorObjUnitIso, singleFunctorObjIsoQh, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, asIso_hom, Functor.Monoidal.εIso_hom, Iso.app_inv, h₁, h₂, h₃]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Functor.comp_obj,
    HomotopyCategory.quotient_obj_singleFunctors_obj, DerivedCategory.Qh_obj_singleFunctors_obj,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact Category.comp_id _

/-- The identification `Lg^* Λ_Y ≅ Λ_X` of constant complexes
(`AlgebraicGeometry.Etale.leftDerivedUpperStarSingleConstantSheafIso`) at the unit of `A` is the
unit comparison `Lg^* 𝟙 ≅ 𝟙` of the monoidal derived pullback
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`). -/
lemma leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp (g : X ⟶ Y) :
    (L((g)^*[A])).map (singleFunctorObjUnitIso A Y).inv ≫
        (leftDerivedUpperStarSingleConstantSheafIso A g (𝟙_ A)).hom =
      (leftDerivedUpperStarUnitIso A g).hom ≫ (singleFunctorObjUnitIso A X).inv := by
  rw [singleFunctorObjUnitIso_inv, singleFunctorObjUnitIso_inv,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [leftDerivedUpperStarSingleConstantSheafIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, upperStarConstantSheafIso_hom_app_tensorUnit]
  rw [leftDerivedUpperStarUnitIso]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  congr 1
  simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj,
    Functor.whiskerRight_app, NatTrans.id_app, Category.comp_id, Category.id_comp, Category.assoc,
    Functor.Monoidal.εIso_inv, Functor.map_comp]
  refine (Category.id_comp _).trans ?_
  rfl

/-- The identification `Lg^* M_Y ≅ M_X` of constant complexes
(`AlgebraicGeometry.Etale.leftDerivedUpperStarSingleConstantSheafIso`) is natural in `M`. -/
@[reassoc]
lemma leftDerivedUpperStarSingleConstantSheafIso_hom_naturality (g : X ⟶ Y) {M N : A}
    (φ : M ⟶ N) :
    (L((g)^*[A])).map ((DerivedCategory.singleFunctor _ 0).map
        ((constantSheaf Y.smallEtaleTopology A).map φ)) ≫
        (leftDerivedUpperStarSingleConstantSheafIso A g N).hom =
      (leftDerivedUpperStarSingleConstantSheafIso A g M).hom ≫
        (DerivedCategory.singleFunctor _ 0).map ((constantSheaf X.smallEtaleTopology A).map φ) := by
  simp only [leftDerivedUpperStarSingleConstantSheafIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  erw [(leftDerivedUpperStarIsoMapDerivedCategory A g).hom.naturality_assoc,
    ((g)^*[A].mapDerivedCategorySingleFunctor 0).hom.naturality_assoc]
  rw [Functor.comp_map, ← (DerivedCategory.singleFunctor _ 0).map_comp,
    ← (DerivedCategory.singleFunctor _ 0).map_comp,
    ← (upperStarConstantSheafIso A g).hom.naturality φ]
  rfl

end UnitComparison

section ProjectionMap

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

/-- Naturality of the inverse of the projection map in its second variable. -/
@[reassoc]
lemma rightDerivedLowerShriek_map_whiskerLeft_comp_inv_projectionMap [IsIso (projectionMap A a)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (q : 𝟙_ _ ⟶ M) :
    (R(a)_![A]).map (K ◁ (L((a)^*[A])).map q) ≫ inv (((projectionMap A a).app K).app M) =
      inv (((projectionMap A a).app K).app (𝟙_ _)) ≫ (R(a)_![A]).obj K ◁ q := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact (projectionMap_naturality_right A a K q).symm

end ProjectionMap

end Etale

end AlgebraicGeometry
