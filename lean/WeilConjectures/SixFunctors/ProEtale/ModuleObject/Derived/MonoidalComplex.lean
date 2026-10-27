/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import Sheaf.SixFunctors.ModCondensedCachedInstances

/-!
# The tensor comparison of the pullback of module objects on complexes

Part of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, split off so that
each file compiles within the time limit: cached instances on
complexes of module objects over `Λ_Z`, the K-flatness of pullbacks, and the degreewise
comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` of complexes (`upperStarTensorComplexHomX`).
-/


set_option Elab.async false

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Instances

Direct instances for complexes of module objects over `Λ_Z`. Finding them from the generic
instances on `Mod` exceeds the default heartbeat limit, so they are recorded once here. -/

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
instance hasTensor_cochainComplex (Z : Scheme.{u})
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    HomologicalComplex.HasTensor A B :=
  inferInstance

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
noncomputable instance monoidalCategoryStruct_cochainComplex (Z : Scheme.{u}) :
    MonoidalCategoryStruct
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
        ℤ) :=
  inferInstance

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
noncomputable instance monoidalCategory_cochainComplex (Z : Scheme.{u}) :
    MonoidalCategory
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
        ℤ) :=
  inferInstance

/-! ### K-flatness of pullbacks -/

set_option synthInstance.maxHeartbeats 400000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
/-- The K-flat complexes of module objects over `Λ_Z` form a left derivability structure for the
quasi-isomorphisms of the homotopy category. It is not an instance: it would change the instance
found for the existence of the derived pullbacks of module objects. -/
lemma isLeftDerivabilityStructure_localizerMorphismKFlat (Z : Scheme.{u}) :
    (HomotopyCategory.quasiIso
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  have (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have h₁ : HasColimitsOfShape ℤ
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) := inferInstance
  have h₂ : HasExactColimitsOfShape ℤ
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) := inferInstance
  have h₃ (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) := inferInstance
  have h₄ : Abelian.HasFunctorialFlatResolution
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) := inferInstance
  have h₅ (X₁ X₂ X₃ X₄ : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  have h₆ (X₁ X₂ X₃ : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  have h₇ (X₁ X₂ X₃ : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  infer_instance

/-- The extension of scalars along the isomorphism `α_f : f^* Λ_Y ⟶ Λ_X` is an equivalence. -/
instance isEquivalence_extendScalars_condensedPullbackHom :
    (Mod.extendScalars (condensedPullbackHom Λ f)).IsEquivalence :=
  have : (Mod.comap (asIso (condensedPullbackHom Λ f)).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).symm.isEquivalence_functor
  Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm

/-- The pullback of module objects preserves K-flat complexes. -/
lemma kFlat_upperStar_mapHomologicalComplex_obj
    {P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ}
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((f)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ) |>.obj P) :=
  ObjectProperty.prop_of_iso _
    ((Functor.mapHomologicalComplexCompIso (Iso.refl ((f)^*⟦Λ⟧)) (.up ℤ)).app P)
    ((Mod.extendScalars (condensedPullbackHom Λ f)).kFlat_mapHomologicalComplex_obj_of_isEquivalence
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).kFlat_mapHomologicalComplex_obj P hP))

/-- The pullback of module objects preserves K-flat objects of the homotopy category. -/
lemma kFlat_upperStar_mapHomotopyCategory_obj
    {R : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ}
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R) :
    (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj R)) :=
  ObjectProperty.prop_of_iso _ (((f)^*⟦Λ⟧.mapHomotopyCategoryFactors (.up ℤ)).app R).symm
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2
      (kFlat_upperStar_mapHomologicalComplex_obj Λ f hR))

/-! ### Complexes -/

/-- The degreewise comparison `(f^* A ⊗ f^* B)^n ⟶ f^* ((A ⊗ B)^n)` for complexes `A` and `B`
of module objects over `Λ_Y`: on the summand `f^* A^p ⊗ f^* B^q` with `p + q = n`, the tensorator
`μ : f^* A^p ⊗ f^* B^q ⟶ f^* (A^p ⊗ B^q)` followed by `f^*` of the inclusion of the summand. -/
noncomputable def upperStarTensorComplexHomX
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n : ℤ) :
    (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
      ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).X n ⟶
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h ↦
    Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ (A.X p) (B.X q) ≫
      (f)^*⟦Λ⟧.map (HomologicalComplex.ιTensorObj A B p q n h)

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The degreewise comparison `upperStarTensorComplexHomX` is a section of the comparison
`f^* ((A ⊗ B)^n) ⟶ (f^* A ⊗ f^* B)^n` induced by the comonoidal structure of `f^*`. -/
lemma upperStarTensorComplexHomX_comp_mapBifunctorComparisonX
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n : ℤ) :
    upperStarTensorComplexHomX Λ f A B n ≫
      (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (f)^*⟦Λ⟧).app A).app B).f n =
      𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  simp only [Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  dsimp only [upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Category.assoc]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [Category.comp_id]
  exact Functor.Monoidal.μ_δ_assoc _ _ _ _

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The degreewise comparisons `upperStarTensorComplexHomX` commute with the differentials. -/
lemma upperStarTensorComplexHom_comm
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n n' : ℤ)
    (_ : (ComplexShape.up ℤ).Rel n n') :
    upperStarTensorComplexHomX Λ f A B n ≫
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).d n n' =
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).d n n' ≫
        upperStarTensorComplexHomX Λ f A B n' := by
  have hc := HomologicalComplex.Hom.comm
    (HomologicalComplex.mapBifunctorComparison (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧)
      (.up ℤ) A B) n n'
  have hX := upperStarTensorComplexHomX_comp_mapBifunctorComparisonX Λ f A B
  simp only [Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app] at hX
  rw [← cancel_mono ((HomologicalComplex.mapBifunctorComparison
      (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧) (.up ℤ) A B).f n'), Category.assoc,
    Category.assoc,
    hX, Category.comp_id]
  exact (congrArg (upperStarTensorComplexHomX Λ f A B n ≫ ·) hc).symm.trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hX n)).trans (Category.id_comp _)))

end AlgebraicGeometry.ProEtale.CondensedRing
