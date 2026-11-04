/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcActualPullProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcActualScalarPullRestrictionUnitOrdinary
import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcActualScalarPullRestrictionUnitDerived
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement

/-! # The derived scalar/pullback comparison under the scalar units

The derived scalar/pullback comparison corresponds, under the scalar adjunction units, to
the canonical restriction/pullback comparison of the pro-étale ring operations.

Source: Stacks Tags 03EL, 06YY and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B)
    (φY : pbcAdicCompletion Y dA ⟶ pbcAdicCompletion Y dB)
    (φX : pbcAdicCompletion X dA ⟶ pbcAdicCompletion X dB)
    (hφ : pbcActualCoefficientRingMap Y φY ≫ pbcActualStructureMap g dB =
      pbcActualStructureMap g dA ≫
        (proEtaleSheafDirectImage g RingCat.{u + 1}).map (pbcActualCoefficientRingMap X φX))
    (hc : (pbcActualCoefficientIso g dA).hom ≫ φX =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map φY ≫
        (pbcActualCoefficientIso g dB).hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The left side of the restriction-unit identity on a flat-term K-flat complex, after the
invertible universal counits, is an ordinary chain map.
Source: Stacks Tags 06YY and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualScalarDerivedPullIso_restriction_unit_left
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dA)) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion Y dA) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion Y dA) (P.X n)) :
    (pbcDerivedScalarAdjunction φX).unit.app
        ((pbcActualDerivedPull g dA).obj (DerivedCategory.Q.obj P)) ≫
        (pbcDerivedRestrict φX).map
          ((pbcActualScalarDerivedPullIso g dA dB φY φX hφ).inv.app (DerivedCategory.Q.obj P)) ≫
        (pbcDerivedRestrict φX).map ((pbcActualDerivedPull g dB).map (pbcComplexCounit φY P) ≫
          pbcActualPullComplexCounit g dB (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (pbcRestrict φX).mapDerivedCategoryFactors.hom.app
          (((pbcActualModulePull g dB).mapHomologicalComplex (.up ℤ)).obj
            (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) =
      pbcActualPullComplexCounit g dA P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φX).unit (.up ℤ)).app
              (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P) ≫
            ((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).map
              ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).inv.app P)) := by
  have hθ : (pbcActualScalarDerivedPullIso g dA dB φY φX hφ).hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend φX).map (pbcActualPullComplexCounit g dA P) ≫
        pbcComplexCounit φX (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcActualDerivedPull g dB).map (pbcComplexCounit φY P) ≫
        pbcActualPullComplexCounit g dB (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).hom.app P) :=
    (pbcActualScalarDerivedPullIso_exists g dA dB φY φX hφ).exists.choose_spec P hp hf
  have hθ' : (pbcActualScalarDerivedPullIso g dA dB φY φX hφ).inv.app (DerivedCategory.Q.obj P) ≫
        (pbcActualDerivedPull g dB).map (pbcComplexCounit φY P) ≫
        pbcActualPullComplexCounit g dB (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcDerivedExtend φX).map (pbcActualPullComplexCounit g dA P) ≫
        pbcComplexCounit φX (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).inv.app P) := by
    rw [← cancel_epi ((pbcActualScalarDerivedPullIso g dA dB φY φX hφ).hom.app _),
      Iso.hom_inv_id_app_assoc, reassoc_of% hθ, ← DerivedCategory.Q.map_comp,
      Iso.hom_inv_id_app]
    simp
  have hu : (pbcDerivedScalarAdjunction φX).unit.app (DerivedCategory.Q.obj
        (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (pbcDerivedRestrict φX).map (pbcComplexCounit φX
          (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (pbcRestrict φX).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φX).mapHomologicalComplex (.up ℤ)).obj
            (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φX).unit
        (.up ℤ)).app (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P)) :=
    (pbcDerivedScalarAdjunction_exists φX).exists.choose_spec _ (pull_good g dA P hp hf).1
  have hF := (pbcRestrict φX).mapDerivedCategoryFactors.hom.naturality
    ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).inv.app P)
  rw [← Functor.map_comp_assoc, hθ', Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, ← Category.assoc ((pbcDerivedScalarAdjunction φX).unit.app _),
    ]
  erw [Adjunction.unit_naturality]
  have hF' : (pbcDerivedRestrict φX).map (DerivedCategory.Q.map
        ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).inv.app P)) ≫
        (pbcRestrict φX).mapDerivedCategoryFactors.hom.app
          (((pbcActualModulePull g dB).mapHomologicalComplex (.up ℤ)).obj
            (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) =
      (pbcRestrict φX).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φX).mapHomologicalComplex (.up ℤ)).obj
            (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map (((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).map
          ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).inv.app P)) := hF
  rw [Category.assoc, hF', reassoc_of% hu, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The right side of the restriction-unit identity on a flat-term K-flat complex, after the
invertible universal counits, is an ordinary chain map.
Source: Stacks Tags 06YY and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualScalarDerivedPullIso_restriction_unit_right
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dA)) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion Y dA) P) :
    (pbcActualDerivedPull g dA).map
        ((pbcDerivedScalarAdjunction φY).unit.app (DerivedCategory.Q.obj P)) ≫
        (pbcActualPullProEtaleIso g dA).hom.app _ ≫
        (proEtaleRingRestrictionDerivedPullback g (pbcAdicCompletion Y dA)
          (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
          (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).inv.app
            ((pbcDerivedExtend φY).obj (DerivedCategory.Q.obj P)) ≫
        (pbcDerivedRestrict φX).map ((pbcActualPullProEtaleIso g dB).inv.app _) ≫
        (pbcDerivedRestrict φX).map ((pbcActualDerivedPull g dB).map (pbcComplexCounit φY P) ≫
          pbcActualPullComplexCounit g dB (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (pbcRestrict φX).mapDerivedCategoryFactors.hom.app
          (((pbcActualModulePull g dB).mapHomologicalComplex (.up ℤ)).obj
            (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) =
      pbcActualPullComplexCounit g dA P ≫
        DerivedCategory.Q.map
          (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).map
              ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φY).unit (.up ℤ)).app P) ≫
            (NatIso.mapHomologicalComplex (pbcActualModulePullIso g dA) (.up ℤ)).hom.app
              (((pbcRestrict φY).mapHomologicalComplex (.up ℤ)).obj
                (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) ≫
            (NatTrans.mapHomologicalComplex (proEtaleRingRestrictionPullbackInv g
              (pbcAdicCompletion Y dA) (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA)
              (pbcAdicCompletion X dB) φY φX (pbcActualCoefficientIso g dA)
              (pbcActualCoefficientIso g dB) hc) (.up ℤ)).app
                (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) ≫
            ((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).map
              ((NatIso.mapHomologicalComplex (pbcActualModulePullIso g dB) (.up ℤ)).inv.app
                (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P))) := by
  have hfB := pbcActualPullProEtaleIso_fac g dB
    (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)
  have hs6 : (pbcActualPullProEtaleIso g dB).inv.app
        (DerivedCategory.Q.obj (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        pbcActualPullComplexCounit g dB (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) =
      (proEtaleRingDerivedPullbackFactors g (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
          (pbcActualCoefficientIso g dB)).hom.app
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (pbcActualModulePullIso g dB) (.up ℤ)).inv.app
            (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) := by
    rw [← cancel_epi ((pbcActualPullProEtaleIso g dB).hom.app _), Iso.hom_inv_id_app_assoc,
      reassoc_of% hfB, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hs5 := (pbcActualPullProEtaleIso g dB).inv.naturality (pbcComplexCounit φY P)
  have hs56 : (pbcActualPullProEtaleIso g dB).inv.app
        ((pbcDerivedExtend φY).obj (DerivedCategory.Q.obj P)) ≫
        (pbcActualDerivedPull g dB).map (pbcComplexCounit φY P) ≫
        pbcActualPullComplexCounit g dB (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) =
      (proEtaleRingDerivedPullback g (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
          (pbcActualCoefficientIso g dB)).map (pbcComplexCounit φY P) ≫
        (proEtaleRingDerivedPullbackFactors g (pbcAdicCompletion Y dB) (pbcAdicCompletion X dB)
          (pbcActualCoefficientIso g dB)).hom.app
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (pbcActualModulePullIso g dB) (.up ℤ)).inv.app
            (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) := by
    rw [← reassoc_of% hs5, hs6]
  have hs9 := (pbcRestrict φX).mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex (pbcActualModulePullIso g dB) (.up ℤ)).inv.app
      (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P))
  have hs7 := (proEtaleRingRestrictionDerivedPullback g (pbcAdicCompletion Y dA)
    (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
    (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).inv.naturality
      (pbcComplexCounit φY P)
  have hD1 := proEtaleRingRestrictionDerivedPullback_inv_fac g (pbcAdicCompletion Y dA)
    (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
    (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc
    (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)
  rw [← Functor.map_comp_assoc (pbcDerivedRestrict φX), hs56, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc]
  erw [hs9]
  erw [← reassoc_of% hs7, reassoc_of% hD1]
  have hY : (pbcDerivedScalarAdjunction φY).unit.app (DerivedCategory.Q.obj P) ≫
        ((pbcDerivedRestrict φY).map (pbcComplexCounit φY P) ≫
        (pbcRestrict φY).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φY).unit (.up ℤ)).app P) :=
    (pbcDerivedScalarAdjunction_exists φY).exists.choose_spec P hp
  have hoA := (pbcActualPullProEtaleIso g dA).hom.naturality
    ((pbcDerivedRestrict φY).map (pbcComplexCounit φY P) ≫
        (pbcRestrict φY).mapDerivedCategoryFactors.hom.app
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P))
  have hfA := pbcActualPullProEtaleIso_fac g dA
    (((pbcRestrict φY).mapHomologicalComplex (.up ℤ)).obj
      (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P))
  have hs13 := pbcActualPullComplexCounit_naturality g dA
    ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φY).unit (.up ℤ)).app P)
  erw [← Functor.map_comp_assoc (proEtaleRingDerivedPullback g (pbcAdicCompletion Y dA)
    (pbcAdicCompletion X dA) (pbcActualCoefficientIso g dA))]
  erw [← reassoc_of% hoA]
  rw [← Functor.map_comp_assoc, hY]
  erw [reassoc_of% hfA]
  erw [reassoc_of% hs13]
  simp only [Functor.map_comp, Functor.comp_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary restriction-unit identity on cochain complexes.
Source: Stacks Tags 03D2, 03EL and 03EK
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualScalarOrdinaryPullComplexIso_restriction_unit
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dA)) ℤ) :
    (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φX).unit (.up ℤ)).app
        (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).map
        ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).inv.app P) =
    ((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction φY).unit (.up ℤ)).app P) ≫
      (NatIso.mapHomologicalComplex (pbcActualModulePullIso g dA) (.up ℤ)).hom.app
        (((pbcRestrict φY).mapHomologicalComplex (.up ℤ)).obj
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (NatTrans.mapHomologicalComplex (proEtaleRingRestrictionPullbackInv g
        (pbcAdicCompletion Y dA) (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA)
        (pbcAdicCompletion X dB) φY φX (pbcActualCoefficientIso g dA)
        (pbcActualCoefficientIso g dB) hc) (.up ℤ)).app
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) ≫
      ((pbcRestrict φX).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (pbcActualModulePullIso g dB) (.up ℤ)).inv.app
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) := by
  apply HomologicalComplex.hom_ext
  intro n
  have h := pbcActualScalarOrdinaryPullIso_restriction_unit g dA dB φY φX hφ hc (P.X n)
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, pbcActualScalarOrdinaryPullComplexIso, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, NatIso.mapHomologicalComplex_inv_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The restriction-unit identity on a flat-term K-flat complex.
Source: Stacks Tags 03EL, 06YY and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
theorem pbcActualScalarDerivedPullIso_restriction_unit_Q
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dA)) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion Y dA) P)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion Y dA) (P.X n)) :
    (pbcDerivedScalarAdjunction φX).unit.app
        ((pbcActualDerivedPull g dA).obj (DerivedCategory.Q.obj P)) ≫
        (pbcDerivedRestrict φX).map
          ((pbcActualScalarDerivedPullIso g dA dB φY φX hφ).inv.app (DerivedCategory.Q.obj P)) =
      (pbcActualDerivedPull g dA).map
          ((pbcDerivedScalarAdjunction φY).unit.app (DerivedCategory.Q.obj P)) ≫
        (pbcActualPullProEtaleIso g dA).hom.app _ ≫
        (proEtaleRingRestrictionDerivedPullback g (pbcAdicCompletion Y dA)
          (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
          (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).inv.app
            ((pbcDerivedExtend φY).obj (DerivedCategory.Q.obj P)) ≫
        (pbcDerivedRestrict φX).map ((pbcActualPullProEtaleIso g dB).inv.app _) := by
  have := scalar_counit_iso Y φY P hp
  have := pull_counit_iso g dB (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)
    (scalar_good Y φY P hp hf)
  rw [← cancel_mono ((pbcDerivedRestrict φX).map
      ((pbcActualDerivedPull g dB).map (pbcComplexCounit φY P) ≫
        pbcActualPullComplexCounit g dB (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (pbcRestrict φX).mapDerivedCategoryFactors.hom.app
        (((pbcActualModulePull g dB).mapHomologicalComplex (.up ℤ)).obj
          (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P))),
    Category.assoc, Category.assoc, Category.assoc, Category.assoc,
    pbcActualScalarDerivedPullIso_restriction_unit_left g dA dB φY φX hφ P hp hf,
    pbcActualScalarDerivedPullIso_restriction_unit_right g dA dB φY φX hc P hp,
    pbcActualScalarOrdinaryPullComplexIso_restriction_unit g dA dB φY φX hφ hc P]

/-- Two natural families of maps which agree on one object agree on every isomorphic object.
-/
theorem eq_app_of_iso_of_naturality {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (a b : ∀ M : C, F.obj M ⟶ G.obj M)
    (ha : ∀ {M N : C} (f : M ⟶ N), F.map f ≫ a N = a M ≫ G.map f)
    (hb : ∀ {M N : C} (f : M ⟶ N), F.map f ≫ b N = b M ≫ G.map f)
    {M N : C} (e : M ≅ N) (h : a M = b M) : a N = b N := by
  rw [← cancel_epi (F.map e.hom), ha, hb, h]

/-- The derived scalar/pullback comparison, transposed along the scalar units, is the
canonical restriction/pullback comparison.
Source: Stacks Tags 03EL, 06YY and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: both sides are natural, so it suffices to treat flat-term K-flat complexes. There
the scalar units, the pullback counits and the scalar/pullback comparison are computed by
ordinary module maps. The ordinary comparison is the conjugate of the identity-on-sections
restriction/direct-image comparison, and the canonical restriction/pullback comparison is
the mate of the same identity-on-sections comparison; these agree on every module. -/
theorem pbcActualScalarDerivedPullIso_restriction_unit (M : PbcCompletedDerived Y dA) :
    (pbcDerivedScalarAdjunction φX).unit.app ((pbcActualDerivedPull g dA).obj M) ≫
        (pbcDerivedRestrict φX).map
          ((pbcActualScalarDerivedPullIso g dA dB φY φX hφ).inv.app M) =
      (pbcActualDerivedPull g dA).map ((pbcDerivedScalarAdjunction φY).unit.app M) ≫
        (pbcActualPullProEtaleIso g dA).hom.app _ ≫
        (proEtaleRingRestrictionDerivedPullback g (pbcAdicCompletion Y dA)
          (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
          (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).inv.app
            ((pbcDerivedExtend φY).obj M) ≫
        (pbcDerivedRestrict φX).map ((pbcActualPullProEtaleIso g dB).inv.app _) := by
  obtain ⟨L, s, hl, hfl, hs, -⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (DerivedCategory.Q.objPreimage M)
  have hf (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := pbcAdicCompletion Y dA) (L.X n) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (pbcAdicCompletion Y dA) (L.X n)).symm (hfl n)
  have : IsIso (DerivedCategory.Q.map s) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).2 hs
  refine eq_app_of_iso_of_naturality (F := pbcActualDerivedPull g dA)
    (G := pbcDerivedExtend φY ⋙ pbcActualDerivedPull g dB ⋙ pbcDerivedRestrict φX)
    (fun M ↦ (pbcDerivedScalarAdjunction φX).unit.app ((pbcActualDerivedPull g dA).obj M) ≫
        (pbcDerivedRestrict φX).map
          ((pbcActualScalarDerivedPullIso g dA dB φY φX hφ).inv.app M))
    (fun M ↦ (pbcActualDerivedPull g dA).map ((pbcDerivedScalarAdjunction φY).unit.app M) ≫
        (pbcActualPullProEtaleIso g dA).hom.app _ ≫
        (proEtaleRingRestrictionDerivedPullback g (pbcAdicCompletion Y dA)
          (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
          (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).inv.app
            ((pbcDerivedExtend φY).obj M) ≫
        (pbcDerivedRestrict φX).map ((pbcActualPullProEtaleIso g dB).inv.app _))
    ?_ ?_ (asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso M)
    (pbcActualScalarDerivedPullIso_restriction_unit_Q g dA dB φY φX hφ hc L hl hf)
  · intro M N f
    have hθ := (pbcActualScalarDerivedPullIso g dA dB φY φX hφ).inv.naturality f
    erw [← Adjunction.unit_naturality_assoc, ← Functor.map_comp, hθ]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  · intro M N f
    have hb := (proEtaleRingRestrictionDerivedPullback g (pbcAdicCompletion Y dA)
      (pbcAdicCompletion Y dB) (pbcAdicCompletion X dA) (pbcAdicCompletion X dB) φY φX
      (pbcActualCoefficientIso g dA) (pbcActualCoefficientIso g dB) hc).inv.naturality
        ((pbcDerivedExtend φY).map f)
    have hoA := (pbcActualPullProEtaleIso g dA).hom.naturality
      ((pbcDerivedRestrict φY).map ((pbcDerivedExtend φY).map f))
    have hoB := (pbcActualPullProEtaleIso g dB).inv.naturality ((pbcDerivedExtend φY).map f)
    rw [← Functor.map_comp_assoc]
    erw [← Adjunction.unit_naturality]
    rw [Functor.map_comp, Category.assoc]
    erw [reassoc_of% hoA, reassoc_of% hb, ← Functor.map_comp, hoB]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl

end AlgebraicGeometry.Scheme
