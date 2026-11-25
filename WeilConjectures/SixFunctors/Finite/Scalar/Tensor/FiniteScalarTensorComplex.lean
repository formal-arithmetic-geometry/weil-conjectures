/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarPullbackComparison
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce

/-! # Tensor realization constructed from signed total comparisons

The realization of finite-scalar pro-étale module sheaves is compatible with tensor products of
complexes: the sheafification tensor comparison is lifted to signed total tensor complexes.

## References

* [Stacks Project, Tags 00CV, 00YV, 04VK, 06YN, 06YS, 07A4 and 0GMW]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf

universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

/-- Finite-scalar pro-étale module sheaves have countable (`0`-universe) colimits. -/
theorem finiteScalarCountableColimits
    (T : Scheme.{u}) (R : Type u) [CommRing R] :
    HasColimitsOfSize.{0, 0}
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) := by
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology _ T
  let : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :=
    IsGrothendieckAbelian.hasColimits _
  exact hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _

attribute [local instance] finiteScalarCountableColimits

/-- The total complex of the tensor bifunctor exists for complexes of finite-scalar module
sheaves. -/
theorem finiteScalarTensorTotal
    (T : Scheme.{u}) (R : Type u) [CommRing R]
    (V W : CochainComplex
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    HomologicalComplex.HasMapBifunctor V W (curriedTensor _) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (finiteScalarCountableColimits T R) _ _) _

attribute [local instance] finiteScalarTensorTotal

/-- Intrinsic pro-étale constant-ring modules have countable (`0`-universe) colimits. -/
theorem finiteScalarIntrinsicCountableColimits (T : Scheme.{u}) (R : Type u) [CommRing R] :
    HasColimitsOfSize.{0, 0} (proEtaleRingModules T (proEtaleConstantRing T R)) :=
  inferInstance

/-- The realization functor is additive. -/
theorem finiteScalarFunctorAdditive (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R] :
    (sfIntrinsicModuleEquivalence T R).functor.Additive := inferInstance

/-- The realization functor is an equivalence. -/
theorem finiteScalarFunctorEquivalence (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R] :
    (sfIntrinsicModuleEquivalence T R).functor.IsEquivalence := inferInstance

/-- The monoidal structure on fixed-scalar module sheaves is preadditive. -/
theorem finiteScalarFixedTensorPreadditive (T : Scheme.{u}) (R : Type u) [CommRing R] :
    MonoidalPreadditive
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) := inferInstance

attribute [local instance 10000] finiteScalarIntrinsicCountableColimits
  finiteScalarFunctorAdditive finiteScalarFunctorEquivalence finiteScalarFixedTensorPreadditive

/-- Flat-term K-flat fixed-scalar complexes. -/
def finiteScalarFlatRepresentatives (T : Scheme.{u}) (R : Type u) [CommRing R] :
    ObjectProperty (CochainComplex
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :=
  fun P ↦ (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
    ∀ n : ℤ, ObjectProperty.flat (P.X n)

/-- The realization's module sheafification inverts the fixed-scalar sheafification unit. -/
theorem finiteScalarModuleSheafificationUnit_isIso
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (P : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} R)) :
    let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} R)
    let S := PresheafOfModules.sheafification.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T R)
    IsIso (S.map (E.map (toSheafify (ProEt.topology T) P))) := by
  dsimp only
  rw [← MorphismProperty.isomorphisms.iff]
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T R))) _
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  change (ProEt.topology T).W
    (Functor.whiskerRight (toSheafify (ProEt.topology T) P)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) AddCommGrpCat.{u + 1}))
  let : (ProEt.topology T).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.forget₂CoinduceAdj (ULift.{u + 1} R))
  exact (ProEt.topology T).W_of_preservesSheafification _ _
    ((ProEt.topology T).W_toSheafify P)

/-- The sectionwise constant-module monoidal structure. -/
@[instance_reducible] def finiteScalarPresheafMonoidal (T : Scheme.{u}) (R : Type u)
    [CommRing R] :
    MonoidalCategory (PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} R)))) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u + 1}
    (((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R))) ⋙
      forget₂ CommRingCat RingCat)))

attribute [local instance] finiteScalarPresheafMonoidal

/-- Curry an ordinary tensor isomorphism, retaining its actual components. -/
def finiteScalarCurryTensorIso {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D) :
    (postcompose₂.obj F).obj (curriedTensor C) ≅
      (((whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D) :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun N ↦ e.app (M, N))
      (by
        intro N N' f
        simpa using e.hom.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, f)))
    (by
      intro M M' f
      ext N
      simpa using e.hom.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N))

/-- Postcomposition commutes with uncurrying by the functor composition equation. -/
def finiteScalarUncurryPostcomposeIso {C : Type u₁} {D : Type u₂} {E : Type u₃} {H : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} H]
    (F : C ⥤ D ⥤ E) (G : E ⥤ H) :
    uncurry.obj F ⋙ G ≅ uncurry.obj ((postcompose₂.obj G).obj F) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp [Functor.comp_map, Functor.uncurry, Functor.postcompose₂])

/-- The uncurrying conversion has identity components. -/
@[simp] theorem finiteScalarUncurryPostcomposeIso_hom_app
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {H : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} H]
    (F : C ⥤ D ⥤ E) (G : E ⥤ H) (Z : C × D) :
    (finiteScalarUncurryPostcomposeIso F G).hom.app Z = 𝟙 _ := rfl

/-- The uncurried lax tensorator, without unfolding the monoidal structures. -/
def finiteScalarLaxTensorNatTrans {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] :
    F.prod F ⋙ uncurry.obj (curriedTensor D) ⟶ uncurry.obj (curriedTensor C) ⋙ F where
  app P := Functor.LaxMonoidal.μ F P.1 P.2
  naturality X Y f := by
    change (F.map f.1 ▷ F.obj X.2 ≫ F.obj Y.1 ◁ F.map f.2) ≫
        Functor.LaxMonoidal.μ F Y.1 Y.2 =
      Functor.LaxMonoidal.μ F X.1 X.2 ≫ F.map (f.1 ▷ X.2 ≫ Y.1 ◁ f.2)
    simpa only [← MonoidalCategory.tensorHom_def] using
      Functor.LaxMonoidal.μ_natural F f.1 f.2

/-- The sheafification tensor comparison used by realization. -/
@[irreducible] def finiteScalarOrdinaryTensorIso
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R] :
    tensor _ ⋙ (sfIntrinsicModuleEquivalence T R).functor ≅
      ((sfIntrinsicModuleEquivalence T R).functor.prod
        (sfIntrinsicModuleEquivalence T R).functor) ⋙
          @tensor (proEtaleRingModules T (proEtaleConstantRing T R)) _
            (SheafOfModules.monoidalCategory (proEtaleConstantRing T R)) := by
  let J := ProEt.topology T
  let B := ModuleCat.{u + 1} (ULift.{u + 1} R)
  let E := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} R)
  let S := PresheafOfModules.sheafification.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T R)
  let U := sheafToPresheaf J B
  let L := presheafToSheaf J B
  let F := ProEtale.finiteCoefficientIntrinsicRealization T R
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing T R)
  let t : E ⋙ S ⟶ L ⋙ F :=
    Functor.whiskerRight (sheafificationAdjunction J B).unit (E ⋙ S)
  have : IsIso t := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    exact finiteScalarModuleSheafificationUnit_isIso T R P
  let h : E ⋙ S ≅ L ⋙ F := asIso t
  let c := asIso (sheafificationAdjunction J B).counit
  let e : U.prod U ⋙ tensor _ ⋙ L ≅ tensor _ :=
    isoWhiskerLeft (U.prod U) (Functor.Monoidal.μNatIso L).symm ≪≫
      isoWhiskerRight (NatIso.prod c c) (tensor _)
  let eE : tensor _ ⋙ E ≅ E.prod E ⋙ tensor _ := Iso.refl _
  let eS := Classical.choose
    (PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} R)))
    (ProEtale.finiteCoefficientIntrinsicScalarMap T R))
  exact (isoWhiskerRight e F).symm ≪≫
    isoWhiskerLeft (U.prod U ⋙ tensor _) h.symm ≪≫
    isoWhiskerLeft (U.prod U) (isoWhiskerRight eE S) ≪≫
    isoWhiskerLeft ((U ⋙ E).prod (U ⋙ E)) eS.symm

/-- The total tensor comparison induced by an ordinary tensor isomorphism, in abstract
categories. -/
@[irreducible] def finiteScalarTotalTensorIsoOfOrdinary
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence]
    (e : tensor C ⋙ F ≅ F.prod F ⋙ tensor D) :
    uncurry.obj ((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
        F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ))) ⋙
        uncurry.obj ((curriedTensor D).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)) := by
  let τ := finiteScalarCurryTensorIso F e
  exact finiteScalarUncurryPostcomposeIso
      ((curriedTensor C).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) ≪≫
    uncurry.mapIso (asIso
      (HomologicalComplex.mapBifunctorComparisonNatTrans
        (F := curriedTensor C) (F' := curriedTensor D) (G₁ := F) (G₂ := F) (G := F)
        (c₁ := .up ℤ) (c₂ := .up ℤ) τ.hom (.up ℤ)))

/-- The signed total of the specified ordinary tensor map, as a natural isomorphism. -/
@[irreducible] def finiteScalarTotalTensorIso
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R] :=
  let := SheafOfModules.monoidalCategory (proEtaleConstantRing T R)
  finiteScalarTotalTensorIsoOfOrdinary
    (sfIntrinsicModuleEquivalence T R).functor (finiteScalarOrdinaryTensorIso T R)

end WeilConjectures
