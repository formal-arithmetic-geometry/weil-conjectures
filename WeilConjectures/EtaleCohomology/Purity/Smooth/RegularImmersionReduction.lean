/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Purity for regular closed immersions and finite reduction

Let `i : Z ⟶ X` be a regular closed immersion of pure codimension `c`, with `X` smooth over a
perfect field `k` and `Z` regular, and let `J` be an ideal of the finite coefficient ring `Λ`.
The purity isomorphism `cl_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])`
(`AlgebraicGeometry.Etale.isIso_fundamentalClassMap`) reduces modulo `J` to a morphism

`cl_i mod J : Λ_Z ⊗ᴸ (Λ/J)_Z ⟶ Ri^! (Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X)`,

the reduction of `cl_i` followed by the canonical comparison
`Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)` and `(Λ/J)_Z ≅ Li^* (Λ/J)_X`. This is the form of the
finite reduction `A_{E,n} ⟶ A_{E,n-1}` of item 4 of blueprint
`prop-pur-regular-immersion-purity-compatibilities` in which the reduction is applied to the
target *before* `Ri^!`.

The reduction map `ρ : K ⟶ K ⊗ᴸ (Λ/J)_X` is natural in `K`, and the adjoint of the reduced
fundamental class is the purity map followed by `Ri^!(ρ)`: the classes reduce compatibly.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`: the comparison
  `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)`, adjoint to the inverse of the projection map followed by
  the counit of `Ri_! ⊣ Ri^!`.
- `AlgebraicGeometry.Etale.fundamentalClassMapModIdeal`: the reduced purity map `cl_i mod J`.
- `AlgebraicGeometry.Etale.constantComplexToQuotient`: the map `Λ_X ⟶ (Λ/J)_X` induced by the
  quotient map `Λ ⟶ Λ/J`.
- `AlgebraicGeometry.Etale.reductionModIdealUnit`: the reduction map `K ⟶ K ⊗ᴸ (Λ/J)_X`, natural
  in `K`.

## Main statements

- `AlgebraicGeometry.Etale.supportedClassMap_comp_map_rightDerivedUpperShriek`: the adjoint
  `Λ_Z ⟶ Ri^! L` of a class with supports is natural in the coefficients `L`.
- `AlgebraicGeometry.Etale.supportedClassMap_fundamentalClass_reductionModIdealUnit`: the
  adjoint of the reduced fundamental class is the purity map followed by `Ri^!(ρ)`.
- `AlgebraicGeometry.Etale.upperStarConstantSheafIso_hom_app_tensorUnit`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp`: at the
  unit, the identification `Lg^* M_Y ≅ M_X` of constant complexes is the unit comparison of the
  monoidal pullback.
- `AlgebraicGeometry.Etale.projectionMap_rightUnitality`: right unitality of the projection map.
- `AlgebraicGeometry.Etale.reductionModIdealUnit_app_comp_fundamentalClassMapModIdeal`: the
  reduced purity map `cl_i mod J` is compatible with the reduction maps `ρ` and the purity map
  `cl_i` (blueprint `prop-pur-regular-immersion-purity-compatibilities`, item 4).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Comparison

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
  [HasCompactification i]

/-- The canonical comparison `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)` for `K, M ∈ D(X_ét, Λ)`: the
adjoint, under `Ri_! ⊣ Ri^!`, of the composite

`Ri_! (Ri^! K ⊗ᴸ Li^* M) ≅ Ri_! Ri^! K ⊗ᴸ M ⟶ K ⊗ᴸ M`

of the inverse of the projection map (`AlgebraicGeometry.Etale.projectionMap`, invertible at a
finite coefficient ring by `AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) and of the
counit of the adjunction. -/
noncomputable def rightDerivedUpperShriekDerivedTensorMap
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj M) ⟶
      (R(i)^![ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj M) :=
  haveI := isIso_projectionMap_of_finite Λ i
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).homEquiv _ _
    (inv (((projectionMap (ModuleCat.{u + 1} Λ) i).app
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj K)).app M) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) i).counit.app K)).app M)

end Comparison

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- For a morphism `q : Λ_X ⟶ M` out of the unit, the natural transformation `K ⟶ K ⊗ᴸ M`:
the inverse of the right unitor `K ⊗ᴸ Λ_X ≅ K` followed by `K ⊗ᴸ q`. -/
noncomputable def derivedTensorRightUnitorInvComp
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (q : 𝟙_ _ ⟶ M) :
    𝟭 _ ⟶ (derivedTensor A X).flip.obj M where
  app K := (derivedTensorRightUnitor A X K).inv ≫ ((derivedTensor A X).obj K).map q
  naturality K L f := by
    change f ≫ (ρ_ L).inv ≫ L ◁ q = ((ρ_ K).inv ≫ K ◁ q) ≫ f ▷ M
    rw [rightUnitor_inv_naturality_assoc, Category.assoc, whisker_exchange]

end General

section UnitComparison

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X Y : Scheme.{u}}

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

/-- For a morphism `φ : 𝟙 ⟶ M` in `A`, the derived pullback of the induced map `𝟙 ⟶ M_Y` of
constant complexes is, under `Lg^* M_Y ≅ M_X` and the unit comparison `Lg^* 𝟙 ≅ 𝟙`, the induced
map `𝟙 ⟶ M_X`. -/
lemma leftDerivedUpperStar_map_comp_leftDerivedUpperStarSingleConstantSheafIso_hom
    (g : X ⟶ Y) {M : A} (φ : 𝟙_ A ⟶ M) :
    (L((g)^*[A])).map ((singleFunctorObjUnitIso A Y).inv ≫
        (DerivedCategory.singleFunctor _ 0).map ((constantSheaf Y.smallEtaleTopology A).map φ)) ≫
        (leftDerivedUpperStarSingleConstantSheafIso A g M).hom =
      (leftDerivedUpperStarUnitIso A g).hom ≫ (singleFunctorObjUnitIso A X).inv ≫
        (DerivedCategory.singleFunctor _ 0).map ((constantSheaf X.smallEtaleTopology A).map φ) := by
  rw [Functor.map_comp, Category.assoc, leftDerivedUpperStarSingleConstantSheafIso_hom_naturality,
    reassoc_of% leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp]

end UnitComparison

section ProjectionMap

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

/-- **Right unitality of the projection map** `Ra_! K ⊗ᴸ M ⟶ Ra_!(K ⊗ᴸ La^* M)` at `M = 𝟙`:
followed by `Ra_!(K ⊗ᴸ La^* 𝟙 ≅ K ⊗ᴸ 𝟙 ≅ K)` it is the right unitor. -/
lemma projectionMap_rightUnitality (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((projectionMap A a).app K).app (𝟙_ _) ≫ (R(a)_![A]).map
        (K ◁ (leftDerivedUpperStarUnitIso A a).hom ≫ (ρ_ K).hom) =
      (ρ_ ((R(a)_![A]).obj K)).hom := by
  rw [projectionMap_app_app_eq, rightDerivedLowerShriek_map_eq]
  exact compactificationProjectionMap_rightUnitality A (HasCompactification.compactification a) K

/-- The inverse of the projection map at `M = 𝟙` is the inverse of the right unitor followed by
`Ra_!(K ≅ K ⊗ᴸ 𝟙 ≅ K ⊗ᴸ La^* 𝟙)`. -/
lemma rightDerivedLowerShriek_map_rightUnitor_inv_comp_inv_projectionMap
    [IsIso (projectionMap A a)] (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (R(a)_![A]).map ((ρ_ K).inv ≫ K ◁ (leftDerivedUpperStarUnitIso A a).inv) ≫
      inv (((projectionMap A a).app K).app (𝟙_ _)) = (ρ_ ((R(a)_![A]).obj K)).inv := by
  have e : (K ◁ (leftDerivedUpperStarUnitIso A a).hom ≫ (ρ_ K).hom) ≫
      ((ρ_ K).inv ≫ K ◁ (leftDerivedUpperStarUnitIso A a).inv) = 𝟙 _ := by
    simp
  rw [IsIso.comp_inv_eq, Iso.eq_inv_comp, ← projectionMap_rightUnitality A a K,
    Category.assoc, ← Functor.map_comp, e]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Naturality of the inverse of the projection map in its second variable. -/
@[reassoc]
lemma rightDerivedLowerShriek_map_whiskerLeft_comp_inv_projectionMap [IsIso (projectionMap A a)]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (q : 𝟙_ _ ⟶ M) :
    (R(a)_![A]).map (K ◁ (L((a)^*[A])).map q) ≫ inv (((projectionMap A a).app K).app M) =
      inv (((projectionMap A a).app K).app (𝟙_ _)) ≫ (R(a)_![A]).obj K ◁ q := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact (projectionMap_naturality_right A a K q).symm

/-- The adjoint form of
`AlgebraicGeometry.Etale.rightDerivedUpperShriek_map_rightUnitor_inv_comp_whiskerLeft`. -/
lemma rightDerivedLowerShriek_map_rightUnitor_inv_comp_whiskerLeft [IsIso (projectionMap A a)]
    [(R(a)_![A]).IsLeftAdjoint] {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (q : 𝟙_ _ ⟶ M) (q' : 𝟙_ _ ⟶ M') (e : (L((a)^*[A])).obj M ≅ M')
    (h : (L((a)^*[A])).map q ≫ e.hom = (leftDerivedUpperStarUnitIso A a).hom ≫ q')
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (R(a)_![A]).map (((ρ_ ((R(a)^![A]).obj K)).inv ≫ (R(a)^![A]).obj K ◁ q') ≫
        (R(a)^![A]).obj K ◁ e.inv) ≫
      inv (((projectionMap A a).app ((R(a)^![A]).obj K)).app M) ≫
        (rightDerivedUpperShriekAdjunction A a).counit.app K ▷ M =
    (rightDerivedUpperShriekAdjunction A a).counit.app K ≫ (ρ_ K).inv ≫ K ◁ q := by
  set B := (R(a)^![A]).obj K
  have h' : q' ≫ e.inv = (leftDerivedUpperStarUnitIso A a).inv ≫ (L((a)^*[A])).map q := by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  rw [Category.assoc, ← whiskerLeft_comp, h', whiskerLeft_comp, ← Category.assoc
    ((ρ_ B).inv), Functor.map_comp, Category.assoc,
    reassoc_of% (rightDerivedLowerShriek_map_whiskerLeft_comp_inv_projectionMap A a B q),
    reassoc_of% (rightDerivedLowerShriek_map_rightUnitor_inv_comp_inv_projectionMap A a B),
    whisker_exchange]
  exact (rightUnitor_inv_naturality_assoc _ _).symm

/-- Let `q : 𝟙 ⟶ M` on `Y` and `q' : 𝟙 ⟶ M'` on `X` be compatible under an identification
`e : La^* M ≅ M'` and the unit comparison `La^* 𝟙 ≅ 𝟙`. Then the map
`Ra^! K ⟶ Ra^! K ⊗ᴸ M'` induced by `q'`, followed by `e⁻¹` and the comparison
`Ra^! K ⊗ᴸ La^* M ⟶ Ra^!(K ⊗ᴸ M)` (adjoint to the inverse of the projection map followed by the
counit), is `Ra^!` of the map `K ⟶ K ⊗ᴸ M` induced by `q`. -/
lemma rightDerivedUpperShriek_map_rightUnitor_inv_comp_whiskerLeft [IsIso (projectionMap A a)]
    [(R(a)_![A]).IsLeftAdjoint] {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {M' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (q : 𝟙_ _ ⟶ M) (q' : 𝟙_ _ ⟶ M') (e : (L((a)^*[A])).obj M ≅ M')
    (h : (L((a)^*[A])).map q ≫ e.hom = (leftDerivedUpperStarUnitIso A a).hom ≫ q')
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((ρ_ ((R(a)^![A]).obj K)).inv ≫ (R(a)^![A]).obj K ◁ q') ≫ (R(a)^![A]).obj K ◁ e.inv ≫
      (rightDerivedUpperShriekAdjunction A a).homEquiv _ _
        (inv (((projectionMap A a).app ((R(a)^![A]).obj K)).app M) ≫
          (rightDerivedUpperShriekAdjunction A a).counit.app K ▷ M) =
    (R(a)^![A]).map ((ρ_ K).inv ≫ K ◁ q) := by
  apply ((rightDerivedUpperShriekAdjunction A a).homEquiv _ _).symm.injective
  rw [← Category.assoc, ← Adjunction.homEquiv_naturality_left, Equiv.symm_apply_apply,
    Adjunction.homEquiv_counit, Adjunction.counit_naturality]
  exact rightDerivedLowerShriek_map_rightUnitor_inv_comp_whiskerLeft A a q q' e h K

end ProjectionMap

section Reduction

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) (J : Ideal Λ)

/-- The map `Λ_X ⟶ (Λ/J)_X` of constant complexes induced by the quotient map `Λ ⟶ Λ/J`: the
constant complex `Λ_X` is the unit sheaf, which is the constant sheaf on `Λ`, placed in degree
zero (`AlgebraicGeometry.Etale.singleFunctorObjUnitIso`). -/
noncomputable def constantComplexToQuotient :
    constantComplex Λ X ⟶ constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J)) :=
  (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv ≫
    (_root_.DerivedCategory.singleFunctor _ 0).map
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ J).toLinearMap))

/-- The reduction map `ρ_K : K ⟶ K ⊗ᴸ (Λ/J)_X` to the reduction of the coefficients modulo `J`
(`AlgebraicGeometry.Etale.reductionModIdeal`): the inverse of the right unitor
`K ⊗ᴸ Λ_X ≅ K` followed by `K ⊗ᴸ (Λ_X ⟶ (Λ/J)_X)`
(`AlgebraicGeometry.Etale.constantComplexToQuotient`). It is natural in `K`. -/
noncomputable def reductionModIdealUnit : 𝟭 _ ⟶ reductionModIdeal Λ X J :=
  derivedTensorRightUnitorInvComp (ModuleCat.{u + 1} Λ) X (constantComplexToQuotient Λ X J)

lemma reductionModIdealUnit_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (reductionModIdealUnit Λ X J).app K =
      (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X K).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map (constantComplexToQuotient Λ X J) :=
  rfl

end Reduction

section SupportedClass

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
  [IsClosedImmersion i]

/-- The adjoint `Λ_Z ⟶ Ri^! L` of a class with supports `γ : Λ_X ⟶ Ri_! Ri^! L`
(`AlgebraicGeometry.Etale.supportedClassMap`) is natural in the coefficients `L`. -/
theorem supportedClassMap_comp_map_rightDerivedUpperShriek
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj L)) (f : L ⟶ L') :
    supportedClassMap Λ i (γ ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map
      ((R(i)^![ModuleCat.{u + 1} Λ]).map f)) =
      supportedClassMap Λ i γ ≫ (R(i)^![ModuleCat.{u + 1} Λ]).map f := by
  rw [supportedClassMap_eq_supportedTranspose, supportedClassMap_eq_supportedTranspose,
    supportedTranspose_comp]

end SupportedClass

section ReductionComparison

variable (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} (i : Z ⟶ X) (J : Ideal Λ)

/-- The derived pullback of `Λ_X ⟶ (Λ/J)_X` is, under `Li^* (Λ/J)_X ≅ (Λ/J)_Z` and the unit
comparison `Li^* Λ_X ≅ Λ_Z`, the map `Λ_Z ⟶ (Λ/J)_Z`. -/
lemma leftDerivedUpperStar_map_constantComplexToQuotient :
    (L((i)^*[ModuleCat.{u + 1} Λ])).map (constantComplexToQuotient Λ X J) ≫
        (leftDerivedUpperStarSingleConstantSheafIso _ i (ModuleCat.of Λ (Λ ⧸ J))).hom =
      (leftDerivedUpperStarUnitIso _ i).hom ≫ constantComplexToQuotient Λ Z J :=
  leftDerivedUpperStar_map_comp_leftDerivedUpperStarSingleConstantSheafIso_hom _ i
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ J).toLinearMap)

variable [Finite Λ] [HasCompactification i]

/-- The reduction map `ρ : Ri^! K ⟶ Ri^! K ⊗ᴸ (Λ/J)_Z`, followed by
`(Λ/J)_Z ≅ Li^* (Λ/J)_X` and the comparison `Ri^! K ⊗ᴸ Li^* (Λ/J)_X ⟶ Ri^!(K ⊗ᴸ (Λ/J)_X)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`), is `Ri^!` of the reduction
map `ρ : K ⟶ K ⊗ᴸ (Λ/J)_X`. -/
lemma reductionModIdealUnit_app_comp_rightDerivedUpperShriekDerivedTensorMap
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (reductionModIdealUnit Λ Z J).app ((R(i)^![ModuleCat.{u + 1} Λ]).obj K) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).map
        (leftDerivedUpperStarSingleConstantSheafIso _ i (ModuleCat.of Λ (Λ ⧸ J))).inv ≫
      rightDerivedUpperShriekDerivedTensorMap Λ i _ _ =
    (R(i)^![ModuleCat.{u + 1} Λ]).map ((reductionModIdealUnit Λ X J).app K) :=
  have := isIso_projectionMap_of_finite Λ i
  rightDerivedUpperShriek_map_rightUnitor_inv_comp_whiskerLeft (ModuleCat.{u + 1} Λ) i _ _ _
    (leftDerivedUpperStar_map_constantComplexToQuotient Λ i J) K

end ReductionComparison

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {k : Type u}
  [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]

/-- The purity map reduced modulo an ideal `J` of `Λ`,

`cl_i mod J : Λ_Z ⊗ᴸ (Λ/J)_Z ⟶ Ri^! (Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X)`:

the reduction `cl_i ⊗ᴸ (Λ/J)_Z` of `cl_i`
(`AlgebraicGeometry.Etale.fundamentalClassMap`), followed by `(Λ/J)_Z ≅ Li^* (Λ/J)_X` and the
comparison `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`). -/
noncomputable def fundamentalClassMapModIdeal (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    (reductionModIdeal Λ Z J).obj (constantComplex Λ Z) ⟶
      (R(i)^![ModuleCat.{u + 1} Λ]).obj
        ((reductionModIdeal Λ X J).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  (reductionModIdeal Λ Z J).map (fundamentalClassMap Λ c i aX hZ) ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).map
      (leftDerivedUpperStarSingleConstantSheafIso _ i (ModuleCat.of Λ (Λ ⧸ J))).inv ≫
    rightDerivedUpperShriekDerivedTensorMap Λ i _ _

/-- Blueprint `prop-pur-regular-immersion-purity-compatibilities`: Compatibilities of purity for
regular immersions

**Finite reduction** (item 4), on the level of classes. For an ideal `J` of `Λ` (for
`Λ = A_{E,n}` and `J = ϖ^{n-1}` this is the reduction `A_{E,n} ⟶ A_{E,n-1}`), the reduction
`ρ : K ⟶ K ⊗ᴸ (Λ/J)_X` (`AlgebraicGeometry.Etale.reductionModIdealUnit`) carries the fundamental
class `[Z ⊂ X] : Λ_X ⟶ Ri_! Ri^! (Λ_X(c)[2c])` to a class with supports in the reduced
coefficients `Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X`, and the adjoint of this reduced class is the purity map
`cl_i` followed by `Ri^!(ρ)`: the purity map is natural in the coefficients, so the classes
reduce compatibly. -/
theorem supportedClassMap_fundamentalClass_reductionModIdealUnit (aX : X ⟶ Spec (.of k))
    [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    supportedClassMap Λ i (fundamentalClass Λ c i aX hZ ≫
      (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![ModuleCat.{u + 1} Λ]).map
        ((reductionModIdealUnit Λ X J).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)))) =
      fundamentalClassMap Λ c i aX hZ ≫ (R(i)^![ModuleCat.{u + 1} Λ]).map
        ((reductionModIdealUnit Λ X J).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  supportedClassMap_comp_map_rightDerivedUpperShriek Λ i _ _

/-- Blueprint `prop-pur-regular-immersion-purity-compatibilities`: Compatibilities of purity for
regular immersions

Item 4, finite reduction `A_{E,n} → A_{E,n-1}`: reducing the coefficients modulo `J` commutes
with the purity map `cl_i`. The square
```
  Λ_Z ─────────────cl_i─────────────▶ Ri^! (Λ_X(c)[2c])
   │                                         │
 ρ │                                         │ Ri^!(ρ)
   ▼                                         ▼
  Λ_Z ⊗ᴸ (Λ/J)_Z ──cl_i mod J──▶ Ri^! (Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X)
```
commutes, where `ρ` is the reduction map `K ⟶ K ⊗ᴸ (Λ/J)`
(`AlgebraicGeometry.Etale.reductionModIdealUnit`) and `cl_i mod J` is the reduced purity map
(`AlgebraicGeometry.Etale.fundamentalClassMapModIdeal`); for `Λ = A_{E,n}` and `J = ϖ^{n-1}`
this is the reduction `A_{E,n} ⟶ A_{E,n-1}`. -/
theorem reductionModIdealUnit_app_comp_fundamentalClassMapModIdeal (aX : X ⟶ Spec (.of k))
    [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    (reductionModIdealUnit Λ Z J).app (constantComplex Λ Z) ≫
        fundamentalClassMapModIdeal Λ c i aX hZ J =
      fundamentalClassMap Λ c i aX hZ ≫ (R(i)^![ModuleCat.{u + 1} Λ]).map
        ((reductionModIdealUnit Λ X J).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) := by
  rw [fundamentalClassMapModIdeal, ← Category.assoc,
    ← (reductionModIdealUnit Λ Z J).naturality, Category.assoc]
  exact congrArg (_ ≫ ·) (reductionModIdealUnit_app_comp_rightDerivedUpperShriekDerivedTensorMap
    Λ i J _)

end Etale

end AlgebraicGeometry
