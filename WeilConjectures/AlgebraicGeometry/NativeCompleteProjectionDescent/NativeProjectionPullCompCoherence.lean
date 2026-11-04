/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionDescentMaps
public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionReductionGenerators
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingUnitSections
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedRepresentsCompCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.DerivedRepresents
public import WeilConjectures.CategoryTheory.DerivedCategory.EquivalenceResolution

/-! # Compatibility of the native pullback reduction comparisons with composition

Source: current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1).

The pullback reduction comparisons `m.pull f` are fixed by their representative normalization
`m.pull_model f` on all complexes. The derived compositors `leftDerivedUpperStarComp` and
`VaryingRing.gComp` represent the ordinary compositors, the ordinary normalizations are
compatible with the ordinary compositors (both are fixed on quotient augmentation generators
of unit sections), and every integral object is represented by a complex on which the
reduction comparison is invertible (K-flat resolutions). The formal argument
`Functor.derivedComparison_comp_coherence` then gives the coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance] AlgebraicGeometry.ProEtale.SpReductionTower.additive
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Naturality of the reduction comparison in the complex. -/
theorem reductionEpsilon_naturality (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) {P P' : CochainComplex (Modules l E T) ℤ} (h : P ⟶ P') :
    (reduction l E T D R).map (DerivedCategory.Q.map h) ≫ reductionEpsilon l E T D R P' =
      reductionEpsilon l E T D R P ≫ DerivedCategory.Q.map
        (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).map h) := by
  let := D.hasDerived
  let := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  exact Functor.mapDerivedCategoryFactors_counit_naturality
    (spIntegralModuleEquivalence l E T).functor R.red R.ordinary R.counit
    (towerEquivalence l E T D).functor h

/-- Every integral object is represented by a complex on which the reduction comparison is
invertible. -/
theorem exists_reductionEpsilon_isIso (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (K : Integral l E T) :
    ∃ P : CochainComplex (Modules l E T) ℤ,
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧ IsIso (reductionEpsilon l E T D R P) := by
  let := D.hasDerived
  let := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  let := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).inverse
  obtain ⟨K', s, hK', -, hs, -⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj
      (DerivedCategory.Q.objPreimage K))
  refine ⟨((spIntegralModuleEquivalence l E T).inverse.mapHomologicalComplex (.up ℤ)).obj K',
    ?_, ?_⟩
  · obtain ⟨φ⟩ := (spIntegralModuleEquivalence l E T).nonempty_Q_obj_inverse_iso _ s
    exact ⟨φ ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩
  · have hc : IsIso (R.counit.app
        (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj
          (((spIntegralModuleEquivalence l E T).inverse.mapHomologicalComplex (.up ℤ)).obj
            K'))) :=
      (NatTrans.isIso_app_iff_of_iso R.counit
        ((spIntegralModuleEquivalence l E T).mapHomologicalComplexCounitIso K')).2
        (R.computes K' hK')
    dsimp only [reductionEpsilon]
    infer_instance

/-- The model condition in terms of the left derived presentation. -/
theorem pull_model_presentation (m : DescentModels l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (o : ordinaryPull l E f ⋙ ordinaryReduction l E X (m.abelian X) (m.red X) ≅
      ordinaryReduction l E Y (m.abelian Y) (m.red Y) ⋙
        VaryingRing.pull (rings l E) (transitions l E) f)
    (h : ∀ P : CochainComplex (Modules l E Y) ℤ,
      (red l E m X).map ((pullComplexComparison l E f P).hom) ≫
        reductionEpsilon l E X (m.abelian X) (m.red X)
          (((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) =
      (m.pull f).hom.app (DerivedCategory.Q.obj P) ≫
        (VaryingRing.G (rings l E) (transitions l E) f).map
          (reductionEpsilon l E Y (m.abelian Y) (m.red Y) P) ≫
        (VaryingRing.pull (rings l E) (transitions l E) f).mapDerivedCategoryFactors.hom.app
          (((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).mapHomologicalComplex
            (.up ℤ)).obj P))
    (P : CochainComplex (Modules l E Y) ℤ) :
    (red l E m X).map ((Functor.leftDerivedPresentation (ordinaryPull l E f)).hom.app P) ≫
        reductionEpsilon l E X (m.abelian X) (m.red X)
          (((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) =
      (m.pull f).hom.app (DerivedCategory.Q.obj P) ≫
        (VaryingRing.G (rings l E) (transitions l E) f).map
          (reductionEpsilon l E Y (m.abelian Y) (m.red Y) P) ≫
        (Functor.DerivedPresentation.ofMap
          (VaryingRing.pull (rings l E) (transitions l E) f)).hom.app
          (((ordinaryReduction l E Y (m.abelian Y) (m.red Y)).mapHomologicalComplex
            (.up ℤ)).obj P) :=
  h P

/-- The derived compositor of integral pullbacks represents the ordinary compositor. -/
theorem leftDerivedUpperStarComp_derivedRepresents {X Z Y : Scheme.{u}} (i : X ⟶ Z)
    (g : Z ⟶ Y) :
    Functor.DerivedRepresents (Functor.leftDerivedPresentation (ordinaryPull l E (i ≫ g)))
      ((Functor.leftDerivedPresentation (ordinaryPull l E g)).comp
        (Functor.leftDerivedPresentation (ordinaryPull l E i)))
      (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) i g).hom
      (CondensedRing.upperStarComp (spIntegralCondensed l E) i g).hom :=
  ((Functor.derivedRepresents_leftDerivedFunctorNatIso _ _).comp
      (Functor.derivedRepresents_leftDerivedFunctorCompIso _ _)).congr rfl (by simp)

/-- The derived compositor of system pullbacks represents the ordinary compositor. -/
theorem gComp_derivedRepresents {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y) :
    Functor.DerivedRepresents
      (Functor.DerivedPresentation.ofMap (VaryingRing.pull (rings l E) (transitions l E) (i ≫ g)))
      ((Functor.DerivedPresentation.ofMap (VaryingRing.pull (rings l E) (transitions l E) g)).comp
        (Functor.DerivedPresentation.ofMap (VaryingRing.pull (rings l E) (transitions l E) i)))
      (VaryingRing.gComp (rings l E) (transitions l E) i g).hom
      (VaryingRing.moduleGComp (rings l E) (transitions l E) i g).hom :=
  Functor.derivedRepresents_mapDerivedCategoryNatIso_trans_compIso _

/-- The generator normalization of an ordinary pullback reduction comparison (the first clause
of `PullReductionModel`). -/
def OrdinaryPullNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (DX : SpCoefficientTowersAbelian l E X) (DY : SpCoefficientTowersAbelian l E Y)
    (RX : SpReductionTower l E X DX) (RY : SpReductionTower l E Y DY)
    (ordinary : ordinaryPull l E f ⋙ ordinaryReduction l E X DX RX ≅
      ordinaryReduction l E Y DY RY ⋙ VaryingRing.pull (rings l E) (transitions l E) f) :
    Prop :=
  ∀ (M : Modules l E Y) (U : Y.ProEt)
    (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op U)) (n : ℕ),
    ((ordinary.hom.app M).val.app (op (n, (Scheme.proEtaleBaseChange f).obj U)))
      (reductionGenerator l E X DX RX ((ordinaryPull l E f).obj M) n
        (op ((Scheme.proEtaleBaseChange f).obj U))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op U) x)) =
      (((VaryingRing.moduleAdj (rings l E) (transitions l E) f).unit.app
        ((ordinaryReduction l E Y DY RY).obj M)).val.app (op (n, U)))
        (reductionGenerator l E Y DY RY M n (op U) x)

/-- Normalized ordinary pullback reduction comparisons are compatible with composition. -/
theorem ordinaryPull_comp_coherence {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y)
    (DX : SpCoefficientTowersAbelian l E X) (DY : SpCoefficientTowersAbelian l E Y)
    (DZ : SpCoefficientTowersAbelian l E Z)
    (RX : SpReductionTower l E X DX) (RY : SpReductionTower l E Y DY)
    (RZ : SpReductionTower l E Z DZ)
    (og : ordinaryPull l E g ⋙ ordinaryReduction l E Z DZ RZ ≅
      ordinaryReduction l E Y DY RY ⋙ VaryingRing.pull (rings l E) (transitions l E) g)
    (oi : ordinaryPull l E i ⋙ ordinaryReduction l E X DX RX ≅
      ordinaryReduction l E Z DZ RZ ⋙ VaryingRing.pull (rings l E) (transitions l E) i)
    (oig : ordinaryPull l E (i ≫ g) ⋙ ordinaryReduction l E X DX RX ≅
      ordinaryReduction l E Y DY RY ⋙ VaryingRing.pull (rings l E) (transitions l E) (i ≫ g))
    (hg : OrdinaryPullNormalized g DZ DY RZ RY og)
    (hi : OrdinaryPullNormalized i DX DZ RX RZ oi)
    (hig : OrdinaryPullNormalized (i ≫ g) DX DY RX RY oig) (M : Modules l E Y) :
    (ordinaryReduction l E X DX RX).map
        ((CondensedRing.upperStarComp (spIntegralCondensed l E) i g).inv.app M) ≫
      oig.hom.app M =
    oi.hom.app ((ordinaryPull l E g).obj M) ≫
      (VaryingRing.pull (rings l E) (transitions l E) i).map (og.hom.app M) ≫
      (VaryingRing.moduleGComp (rings l E) (transitions l E) i g).inv.app
        ((ordinaryReduction l E Y DY RY).obj M) := by
  rw [← cancel_epi ((ordinaryReduction l E X DX RX).map
    ((CondensedRing.upperStarComp (spIntegralCondensed l E) i g).hom.app M)),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  refine ordinaryReduction_upperStar_hom_ext (i ≫ g) DX RX M _ _ fun U x n ↦ ?_
  refine (hig M U x n).trans ?_
  symm
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  rw [ordinaryReduction_map_reductionGenerator_op, upperStarComp_hom_app_unit_section]
  erw [← ordinaryReduction_restrict_reductionGenerator]
  erw [PresheafOfModules.naturality_apply,
    hi ((ordinaryPull l E g).obj M) ((Scheme.proEtaleBaseChange g).obj U) _ n,
    PresheafOfModules.naturality_apply, VaryingRing.pull_map_unit_apply, hg M U x n]
  exact VaryingRing.moduleGComp_inv_app_unit _ _ i g _ n U _

/-- The pullback reduction comparison is compatible with composition of inverse images.
Source: blueprint, sec-smooth-purity, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1). -/
theorem pull_comp_coherence_proof (m : DescentModels l E) {X Z Y : Scheme.{u}} (i : X ⟶ Z)
    (g : Z ⟶ Y) (K : Integral l E Y) :
    (red l E m X).map
        ((CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) i g).inv.app K) ≫
        (m.pull (i ≫ g)).hom.app K =
      (m.pull i).hom.app ((ringedPull l E g).obj K) ≫
        (VaryingRing.G (rings l E) (transitions l E) i).map ((m.pull g).hom.app K) ≫
        (VaryingRing.gComp (rings l E) (transitions l E) i g).inv.app ((red l E m Y).obj K) := by
  obtain ⟨og, hog, hg⟩ := m.pull_model g
  obtain ⟨oi, hoi, hi⟩ := m.pull_model i
  obtain ⟨oig, hoig, hig⟩ := m.pull_model (i ≫ g)
  exact Functor.derivedComparison_comp_coherence
    (Functor.leftDerivedPresentation (ordinaryPull l E g))
    (Functor.leftDerivedPresentation (ordinaryPull l E i))
    (Functor.leftDerivedPresentation (ordinaryPull l E (i ≫ g)))
    (Functor.DerivedPresentation.ofMap (VaryingRing.pull (rings l E) (transitions l E) g))
    (Functor.DerivedPresentation.ofMap (VaryingRing.pull (rings l E) (transitions l E) i))
    (Functor.DerivedPresentation.ofMap (VaryingRing.pull (rings l E) (transitions l E) (i ≫ g)))
    (red l E m X) (red l E m Y) (red l E m Z)
    (ordinaryReduction l E X (m.abelian X) (m.red X))
    (ordinaryReduction l E Y (m.abelian Y) (m.red Y))
    (ordinaryReduction l E Z (m.abelian Z) (m.red Z))
    (reductionEpsilon l E X (m.abelian X) (m.red X))
    (reductionEpsilon l E Y (m.abelian Y) (m.red Y))
    (reductionEpsilon l E Z (m.abelian Z) (m.red Z))
    (reductionEpsilon_naturality X (m.abelian X) (m.red X))
    (m.pull g) (m.pull i) (m.pull (i ≫ g)) og oi oig
    (pull_model_presentation m g og hg) (pull_model_presentation m i oi hi)
    (pull_model_presentation m (i ≫ g) oig hig)
    _ _ (leftDerivedUpperStarComp_derivedRepresents i g)
    _ _ (gComp_derivedRepresents i g)
    (ordinaryPull_comp_coherence i g _ _ _ _ _ _ og oi oig hog hoi hoig)
    (exists_reductionEpsilon_isIso Y (m.abelian Y) (m.red Y)) K

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
