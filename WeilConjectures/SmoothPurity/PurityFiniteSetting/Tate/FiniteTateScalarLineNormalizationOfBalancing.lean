/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoUniqueness
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ScalarSingleAdjointInsertion
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientUnitInsertion
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Line normalization from finite Tate balancing

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4.
(blueprint: lem-pur-finite-tate-scalar-line-normalization-of-balancing)

The scalar/single comparison on each flat Tate line is the ordinary coefficient
extension comparison. The rank-one balancing map and its tensor powers therefore
are isomorphisms, and the degree-zero map is the specified scalar unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.upperStar Etale.lowerStar

private theorem single_from_rep_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (E : DerivedCategory C ⥤ DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (M : C) [IsIso (rep ((CochainComplex.singleFunctor C 0).obj M))] :
    IsIso (puritySingleFromRepresentativeMap F E rep M) := by
  unfold puritySingleFromRepresentativeMap
  infer_instance

private theorem single_map_iso (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hM : exactFunctor _ _ (tensorRight M)) : IsIso (purityScalarSingleMap φ X M) := by
  have hflat : ObjectProperty.flat M := by
    refine ⟨?_, hM⟩
    exact (exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight M).symm hM
  have hP := (CochainComplex.kFlat_single_obj_iff_flat M (0 : ℤ)).2 hflat
  have := Etale.scalarRepresentative_isIso φ X
    ((CochainComplex.singleFunctor _ 0).obj M) hP
  have hrep : Etale.scalarAdjunctionRepresentativeMap (Etale.purityScalarSheaf φ X)
      (Sheaf.restrictScalars X.smallEtaleTopology φ) (Etale.purityScalarSheafAdjunction φ X)
      (Etale.purityScalarExtension φ X)
      (Etale.purityScalarAdjunction φ X) = Etale.scalarExtensionRepresentative φ X := by
    funext P
    unfold Etale.scalarExtensionRepresentative Etale.purityScalarAdjunction
      Etale.scalarAdjunctionRepresentativeMap
    with_unfolding_all rfl
  unfold purityScalarSingleMap
  rw [CategoryTheory.purityAdjunctionSingleMap_eq_representative]
  unfold purityRepresentativeSingleMap
  rw [hrep]
  exact single_from_rep_isIso (Etale.purityScalarSheaf φ X)
    (Etale.purityScalarExtension φ X) (Etale.scalarExtensionRepresentative φ X) M

private theorem single_unit_hom (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} R) X).hom = 𝟙 _ := by
  have h := (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} R) X).hom_inv_id
  rw [Etale.singleFunctorObjUnitIso_inv] at h
  exact (Category.comp_id _).symm.trans h

private theorem scalar_unit_map (φ : A →+* B) (X : Scheme.{u}) :
    purityScalarUnitMap φ X = (Etale.ExceptionalCoefficients.unitIso φ X).hom := by
  unfold purityScalarUnitMap purityTransportUnitMap
  dsimp only [Iso.symm_inv, Iso.symm_hom]
  erw [single_unit_hom, Etale.singleFunctorObjUnitIso_inv, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

private theorem zero_shift_map
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {U : C} {V : D} (l : F.obj U ⟶ V) :
    (F.commShiftIso 0).hom.app U ≫ (shiftFunctor D 0).map l ≫
        (shiftFunctorZero D ℤ).hom.app V =
      F.map ((shiftFunctorZero C ℤ).hom.app U) ≫ l := by
  rw [F.commShiftIso_zero]
  simp only [Functor.CommShift.isoZero_hom_app, Category.assoc]
  rw [(shiftFunctorZero D ℤ).hom.naturality l]
  simp

/--
Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4.
(blueprint: lem-pur-finite-tate-scalar-line-normalization-of-balancing)

For the balancing family supplied by the ordinary coefficient construction,
flatness of every finite Tate line identifies the normalized scalar/single map
with its degree-zero flat representative. The rank-one coefficient formula is
invertible with inverse inserting `1`; tensor-power and shift comparisons preserve
invertibility. At degree zero the map is ordinary multiplication, so the
specified scalar unit and zero-line equation hold by the unit laws.
-/
theorem finite_tate_scalar_line_normalization_of_balancing [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r)
    (hβ : IsFiniteTateScalarBalancing φ N hA hB X β) :
    IsFiniteTateScalarLineNormalized φ N hA hB X β := by
  have hflat (r : ℕ) : ObjectProperty.flat
      (Scheme.finiteEtaleTateTwist X N A hA r) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line X N hN hX A hA r).2.2.1
  have hsingle (r : ℕ) : IsIso
      (purityScalarSingleMap φ X (Scheme.finiteEtaleTateTwist X N A hA r)) :=
    single_map_iso φ X _ (hflat r).2
  have hzero := hβ
  unfold IsFiniteTateScalarBalancing at hzero
  have hη : (ProEtale.etaleSheafExtendScalarsAdjunction φ X).homEquiv _ _
      (Functor.OplaxMonoidal.η (Etale.purityScalarSheaf φ X)) =
      Functor.LaxMonoidal.ε (Sheaf.restrictScalars X.smallEtaleTopology φ) := by
    change ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).homEquiv _ _)
      (((ProEtale.etaleSheafExtendScalarsAdjunction φ X).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  have hu : purityScalarSingleMap φ X (𝟙_ _) ≫
      (DerivedCategory.singleFunctor _ 0).map (β 0).hom = purityScalarUnitMap φ X := by
    rw [scalar_unit_map]
    have hi := Etale.FiniteSmoothPurity.scalarSingleMap_eq_scalarInsertion
      φ X (𝟙_ _) (𝟙_ _) (Functor.OplaxMonoidal.η (Etale.purityScalarSheaf φ X))
    rw [hη] at hi
    have hb : (β 0).hom = Functor.OplaxMonoidal.η (Etale.purityScalarSheaf φ X) :=
      hzero.2.1
    with_unfolding_all
      exact Eq.trans (congrArg
        (fun g : (Etale.purityScalarSheaf φ X).obj (𝟙_ _) ⟶ 𝟙_ _ ↦
          purityScalarSingleMap φ X (𝟙_ _) ≫ (DerivedCategory.singleFunctor _ 0).map g)
        hb) (Eq.trans hi (Eq.symm (finiteCoefficient_unit_eq_scalarInsertion φ X)))
  refine ⟨hu, ?_, ?_⟩
  · intro r
    have := hsingle r
    unfold finiteTateScalarLineMap
    infer_instance
  · let F := Etale.purityScalarExtension φ X
    let : F.CommShift ℤ := by
      with_unfolding_all exact (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).leftAdjointCommShift ℤ
    let UA := (DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (𝟙_ _)
    let UB := (DerivedCategory.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj (𝟙_ _)
    let a := Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X
    let b := Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} B) X
    with_unfolding_all
      change ((F.commShiftIso (0 : ℤ)).hom.app UA ≫
        (shiftFunctor _ (0 : ℤ)).map
          (purityScalarSingleMap φ X (𝟙_ _) ≫
            (DerivedCategory.singleFunctor _ 0).map (β 0).hom)) ≫
          ((shiftFunctorZero _ ℤ).hom.app UB ≫ b.hom) =
        F.map ((shiftFunctorZero _ ℤ).hom.app UA ≫ a.hom) ≫
          (Etale.ExceptionalCoefficients.unitIso φ X).hom
    rw [hu]
    calc
      _ = (F.map ((shiftFunctorZero _ ℤ).hom.app UA) ≫
          purityScalarUnitMap φ X) ≫ b.hom := by
        simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ b.hom)
          (zero_shift_map F (purityScalarUnitMap φ X))
      _ = _ := by
        dsimp only [F, a, b]
        unfold purityScalarUnitMap purityTransportUnitMap
        simp only [Iso.symm_inv, Iso.symm_hom, CategoryTheory.Functor.map_comp,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]

end WeilConjectures.PurityFiniteSetting
