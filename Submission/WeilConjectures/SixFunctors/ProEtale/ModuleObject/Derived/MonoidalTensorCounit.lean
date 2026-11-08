/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
public import Submission.WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Tensor counits and the monoidal structure of left derived functors

Supplements to `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived`, used by the
finiteness of the derived pushforward (`boundedConstructible_rightDerivedLowerStar_obj`):

- `Functor.tensorCounitOfNatTrans`, `Functor.homotopyTensorCounit`,
  `Functor.homotopyTensorLeftDerivedCounit`: the tensor counits of a functor on complexes, on the
  homotopy category and for its left derived functor;
- `Functor.leftDerivedTensorUnitIso` and `leftDerivedMonoidalWithUnit`: the monoidal structure of a
  left derived functor with a prescribed unit comparison;
- `ProEtale.CondensedRing.upperStar_preservesFlat`: the pullback of module objects preserves flat
  objects.
-/

@[expose] public section

universe u v v₁ v₂

open CategoryTheory Limits MonoidalCategory

/-- Apply a natural transformation in both tensor factors, then a tensor comparison. -/
@[irreducible]
noncomputable def CategoryTheory.Functor.tensorCounitOfNatTrans
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory E] (L : C ⥤ D) (F : D ⥤ E) (G : C ⥤ E)
    (τ : L ⋙ F ⟶ G) (T : C ⥤ C ⥤ E)
    (α : (((Functor.whiskeringLeft₂ E).obj G).obj G).obj (curriedTensor E) ⟶ T) :
    (((Functor.whiskeringLeft₂ E).obj L).obj L).obj
      ((((Functor.whiskeringLeft₂ E).obj F).obj F).obj (curriedTensor E)) ⟶ T :=
  (((Functor.whiskeringLeft₂ E).map τ).app (L ⋙ F)).app (curriedTensor E) ≫
    (((Functor.whiskeringLeft₂ E).obj G).map τ).app (curriedTensor E) ≫ α

/-- The tensorator of an additive monoidal functor, passed to the homotopy category
and followed by the lax tensorator of the derived localization. -/
@[irreducible]
noncomputable def CategoryTheory.Functor.homotopyTensorCounit
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive]
    [F.IsLeftAdjoint] [F.Monoidal]
    : (((Functor.whiskeringLeft₂ _).obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj
          (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) ⟶
      (Functor.postcompose₂.obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) :=
  (((Functor.whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
      (F.mapHomotopyCategory (.up ℤ))).map
        (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh) ≫
    (Functor.postcompose₂.obj DerivedCategory.Qh).map
      (asIso (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F)).inv

/-- The counit of the derived tensor of two left derived functors, followed by the
homotopy-category tensor comparison. -/
@[irreducible]
noncomputable def CategoryTheory.Functor.homotopyTensorLeftDerivedCounit
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal]
    : (((Functor.whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (Functor.derivedTensorLeftDerived F) ⟶
      (Functor.postcompose₂.obj
        (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).obj (curriedTensor _) :=
  Functor.tensorCounitOfNatTrans DerivedCategory.Qh F.leftDerivedFunctor
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) F.leftDerivedFunctorCounit _
    F.homotopyTensorCounit

/-- The tensor-unit comparison for the left derived functor of an exact monoidal functor. -/
@[irreducible]
noncomputable def CategoryTheory.Functor.leftDerivedTensorUnitIso
    {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal]
    : F.leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso (F.leftDerivedFunctorCounit.app (𝟙_ _)) ≪≫
    DerivedCategory.Qh.mapIso
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app (𝟙_ _) ≪≫
        (HomotopyCategory.quotient _ _).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex F
              (ComplexShape.up ℤ) 0).app (𝟙_ _) ≪≫
            (HomologicalComplex.single _ _ 0).mapIso (Functor.Monoidal.εIso F).symm))

namespace CategoryTheory.Functor
open DerivedCategory LaxMonoidal OplaxMonoidal
variable {C : Type v₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type v₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.IsLeftAdjoint] [F.Monoidal] [F.PreservesFlat]

/-- The descended unit map is the counit followed by the ordinary unit comparison in degree zero. -/
lemma residueDerivedOplax_η_eq_tensorUnitIso :
    letI := residueDerivedOplax F
    η F.leftDerivedFunctor = (leftDerivedTensorUnitIso F).hom := by
  have := DerivedCategory.isIso_ε_Qh C
  have := DerivedCategory.isIso_ε_Qh D
  have hεC : ε (Qh (C := C)) = 𝟙 _ := rfl
  have hεD : ε (Qh (C := D)) = 𝟙 _ := rfl
  change F.leftDerivedFunctor.map (ε Qh) ≫ F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
    Qh.map (η (F.mapHomotopyCategory (.up ℤ))) ≫ CategoryTheory.inv (ε Qh) = _
  have hmapC : F.leftDerivedFunctor.map (ε (Qh (C := C))) = 𝟙 _ := by
    change F.leftDerivedFunctor.map (𝟙 _) = 𝟙 _
    exact F.leftDerivedFunctor.map_id _
  have hinvD : CategoryTheory.inv (ε (Qh (C := D))) = 𝟙 _ :=
    IsIso.inv_eq_of_hom_inv_id (by simpa only [Category.comp_id] using hεD)
  erw [hmapC, hinvD, Category.id_comp, Category.comp_id]
  simp only [leftDerivedTensorUnitIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom,
    mapHomotopyCategory_η, mapCochainComplex_η, mapCochainComplexεIso,
    Iso.trans_inv, Functor.mapIso_inv]
  congr 1
  apply Qh.congr_map
  change (HomotopyCategory.quotient D (.up ℤ)).map _ = _
  have hh : ((F.mapHomotopyCategoryFactors (.up ℤ)).app (𝟙_ _)).hom = 𝟙 _ := by
    simp [Functor.mapHomotopyCategoryFactors]
    rfl
  erw [hh, Category.id_comp]
  rfl

/-- The canonical derived monoidal structure with its unit maps written using the explicit
comparison `leftDerivedTensorUnitIso`. This preserves the definitional unit API. -/
@[instance_reducible]
noncomputable def leftDerivedMonoidalWithUnit : F.leftDerivedFunctor.Monoidal :=
  letI := residueDerivedMonoidal F
  have hη : η F.leftDerivedFunctor = (leftDerivedTensorUnitIso F).hom :=
    residueDerivedOplax_η_eq_tensorUnitIso F
  have hε : (leftDerivedTensorUnitIso F).inv = ε F.leftDerivedFunctor := by
    apply (cancel_mono (leftDerivedTensorUnitIso F).hom).1
    rw [Iso.inv_hom_id, ← hη, Monoidal.ε_η]
  Monoidal.copy (residueDerivedMonoidal F) (leftDerivedTensorUnitIso F).inv
    (μ F.leftDerivedFunctor) (leftDerivedTensorUnitIso F).hom (δ F.leftDerivedFunctor)
    hε rfl hη.symm rfl

variable [hR : (derivedTensorLeftDerived F).IsLeftDerivedFunctor₂
  F.homotopyTensorLeftDerivedCounit
  (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ))]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open scoped CategoryTheory.Obj

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Instances

Direct instances for complexes of module objects over `Λ_Z`. Finding them from the generic
instances on `Mod` exceeds the default heartbeat limit, so they are recorded once here. -/

-- Cache the ambient existence properties used by every derived functor in the file.
local instance grothendieckModulesShortcut (Z : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

local instance flatResolutionModulesShortcut (Z : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

-- Reuse the already available pullback properties throughout these concrete constructions.
local instance upperStarAdditiveShortcut : (f)^*⟦Λ⟧.Additive := inferInstance

local instance upperStarFiniteLimitsShortcut : PreservesFiniteLimits (f)^*⟦Λ⟧ :=
  inferInstance

local instance upperStarFiniteColimitsShortcut : PreservesFiniteColimits (f)^*⟦Λ⟧ :=
  inferInstance

local instance upperStarLeftAdjointShortcut : (f)^*⟦Λ⟧.IsLeftAdjoint := inferInstance

-- Give tensor-colimit inference a direct path in the internal module category.
local instance preservesColimitsTensorLeftShortcut (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfSize.{0, 0} ((curriedTensor _).obj M) :=
  inferInstance

local instance preservesColimitsTensorRightShortcut (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfSize.{0, 0} ((curriedTensor _).flip.obj M) :=
  inferInstance

-- Cache the colimit compatibility proofs used repeatedly by total tensor products.
local instance hasTensorGradedShortcut (Z : Scheme.{u})
    (A B : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : A.HasTensor B :=
  inferInstance

local instance hasGoodTensorLeftShortcut (Z : Scheme.{u})
    (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasGoodTensor₁₂Tensor A B C :=
  inferInstance

local instance hasGoodTensorRightShortcut (Z : Scheme.{u})
    (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasGoodTensorTensor₂₃ A B C :=
  inferInstance

local instance hasTensorFourShortcut (Z : Scheme.{u})
    (A B C D : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasTensor₄ObjExt A B C D :=
  inferInstance

/-! ### Complexes -/

/-! ### The homotopy category -/

/-! ### Derived categories -/

/-- Pullback of module objects preserves flat objects. The coefficient ring comparison is an
isomorphism, so extension of scalars identifies with restriction along its inverse. Transport
flatness along this identification and apply `ProEtale.inverseImageModule_preservesFlat`. -/
lemma upperStar_preservesFlat : (f)^*⟦Λ⟧.PreservesFlat := by
  let G := (f)^*[Ab.{u + 1}]
  let R := condensedRingObj Λ Y
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  have h := ProEtale.inverseImageModule_preservesFlat f R (condensedRingObj Λ X) ρ
  let e : (f)^*⟦Λ⟧ ≅ Mod.mapModComap ρ :=
    Functor.isoWhiskerLeft (G.mapMod R)
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  exact ⟨fun hM ↦ (ObjectProperty.flat).prop_of_iso (e.symm.app _) (h.flat_obj hM)⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ### The monoidal structure -/

end AlgebraicGeometry.ProEtale.CondensedRing
