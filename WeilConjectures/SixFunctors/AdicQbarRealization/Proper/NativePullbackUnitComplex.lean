/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorUnitRightRepresentatives
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # The normalized cochain left-unit equation for arbitrary native pullback

Source: Bhatt--Scholze Remark 6.8.15; Stacks Tags 03EK and 0FPT.
(blueprint: lem-sf-native-pullback-unit-complex)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
attribute [local implicit_reducible] WeilConjectures.coefficientTotalTensor
  CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite WeilConjectures CategoryTheory.RingedForgetTensorTransposition
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  {R : LocallyFiniteAdicRealization.Realization l X}
  {S : LocallyFiniteAdicRealization.Realization l Y}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  {O : Operations l p R S} {A : At l X R} {C : At l Y S}
  (V : TensorComparison l p R S O A C)

set_option maxHeartbeats 1600000 in
-- Adjunction transposition checks large sheaf total tensor and section instances.
/-- Native pullback preserves the multiplication-normalized left-unit chain map.
Source: BS Remark 6.8.15 and Stacks 03EK, 0FPT.
(blueprint: lem-sf-native-pullback-unit-complex).

Proof: transpose both maps under the ordinary cochain adjunction. Test each homogeneous
summand on pure sheafified tensors on Y. Degrees with a nonzero first index vanish.
In degree (0,n), express the unit section as the section of a coefficient a. The
recorded tensor and unit equations send the two factors to their adjunction-unit
images and a to its coefficient pullback. Linearity of the adjunction unit identifies
this with the image of a times the second factor. The normalized left unitors give
these same products. Thus the transposed maps, and hence the original maps, agree. -/
theorem nativePullbackLeftUnitorChain
    (P : CochainComplex (modules l Y S) ℤ)
    (bB : (coefficientTotalTensor.{u + 1, u + 1, u}
      (ProEt.topology Y) (ring l Y S)).obj
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S), P) ≅ P)
    (bA : (coefficientTotalTensor.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R)).obj
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R),
        ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj P) ≅
      ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj P)
    (hbB : ∀ (n : ℤ) (h : 0 + n = n) (W : Y.ProEtᵒᵖ) (a : (ring l Y S).obj.obj W)
      (x : (P.X n).val.obj W),
      (bB.hom.f n).val.app W (coefficientTensorGenerator.{u + 1, u + 1, u}
        (ProEt.topology Y) (ring l Y S)
        (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S))
        P 0 n n h W
        (ringedTensorUnitSection.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S) W a) x) =
        a • x)
    (hbA : ∀ (n : ℤ) (h : 0 + n = n) (W : X.ProEtᵒᵖ) (a : (ring l X R).obj.obj W)
      (x : ((((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex
        (.up ℤ)).obj P).X n).val.obj W),
      (bA.hom.f n).val.app W (coefficientTensorGenerator.{u + 1, u + 1, u}
        (ProEt.topology X) (ring l X R)
        (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R))
        (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex
          (.up ℤ)).obj P) 0 n n h W
        (ringedTensorUnitSection.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R) W a) x) =
        a • x) :
    ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).map bB.hom =
      V.cochain.hom.app
        (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S), P) ≫
      (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)).map
        (X := (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj
          (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)),
          ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj P))
        (Y := (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R),
          ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).obj P))
        (V.unitCochain.hom, 𝟙 _) ≫ bA.hom := by
  let F := (ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)
  let U := ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S)
  let adj := O.moduleAdjunction.mapHomologicalComplex (.up ℤ)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hn := adj.unit.naturality bB.hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← hn]
  apply CategoryTheory.RingedForgetTensorTransposition.total_hom_ext.{u + 1, u, u + 1}
    (ProEt.topology Y) (ring l Y S) U P _
  intro n i j hij
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by omega
    subst j
    apply CategoryTheory.RingedForgetTensorTransposition.pure_ext.{u + 1, u, u + 1}
      (ProEt.topology Y) (ring l Y S) _ _ _
    intro W x y
    let WX := op ((proEtaleBaseChange p).obj (unop W))
    let sy := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
      (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S)))
    let a : (ring l Y S).obj.obj W := sy.hom.val.app W x
    have hx : ringedTensorUnitSection.{u + 1, u, u + 1}
        (ProEt.topology Y) (ring l Y S) W a = x := by
      exact congrArg (fun f ↦ f.val.app W x) sy.hom_inv_id
    have hpure_aux (k : ℤ) (hk : 0 + n = k) :
        ((V.cochain.hom.app (U, P)).f k).val.app WX
          (((O.moduleAdjunction.unit.app
            (((coefficientTotalTensor.{u + 1, u + 1, u}
              (ProEt.topology Y) (ring l Y S)).obj (U, P)).X k)).val.app W)
            (coefficientTensorGenerator.{u + 1, u + 1, u}
              (ProEt.topology Y) (ring l Y S) U P 0 n k hk W x y)) =
        coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
          (F.obj U) (F.obj P) 0 n k hk WX
          (((O.moduleAdjunction.unit.app (U.X 0)).val.app W) x)
          (((O.moduleAdjunction.unit.app (P.X n)).val.app W) y) := by
      subst k
      exact V.pure U P 0 n (unop W) x y
    have hpure := hpure_aux n hij
    have hmap := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u + 1}
      V.unitCochain.hom (𝟙 (F.obj P)) 0 n n hij WX
      (((O.moduleAdjunction.unit.app (U.X 0)).val.app W) x)
      (((O.moduleAdjunction.unit.app (P.X n)).val.app W) y)
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] at hmap
    have hunit := V.unit_sections (unop W) a
    rw [hx] at hunit
    change ((O.moduleAdjunction.unit.app (P.X n)).val.app W)
        ((bB.hom.f n).val.app W
          (coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology Y)
            (ring l Y S) U P 0 n n hij W x y)) =
      (bA.hom.f n).val.app WX
        ((((coefficientTotalTensor.{u + 1, u + 1, u}
          (ProEt.topology X) (ring l X R)).map
            (V.unitCochain.hom, 𝟙 (F.obj P))).f n).val.app WX
          (((V.cochain.hom.app (U, P)).f n).val.app WX
            (((O.moduleAdjunction.unit.app
              (((coefficientTotalTensor.{u + 1, u + 1, u}
                (ProEt.topology Y) (ring l Y S)).obj (U, P)).X n)).val.app W)
                  (coefficientTensorGenerator.{u + 1, u + 1, u}
                    (ProEt.topology Y) (ring l Y S) U P 0 n n hij W x y))))
    let τ : (((coefficientTotalTensor.{u + 1, u + 1, u}
        (ProEt.topology X) (ring l X R)).obj (F.obj U, F.obj P)).X n).val.obj WX →
        ((F.obj P).X n).val.obj WX := fun z ↦ (bA.hom.f n).val.app WX
      ((((coefficientTotalTensor.{u + 1, u + 1, u}
        (ProEt.topology X) (ring l X R)).map
          (X := (F.obj U, F.obj P))
          (Y := (ringedTensorUnitComplex.{u + 1, u, u + 1}
            (ProEt.topology X) (ring l X R), F.obj P))
          (V.unitCochain.hom, 𝟙 (F.obj P))).f n).val.app WX z)
    let β := fun z ↦ (bA.hom.f n).val.app WX z
    have h1 := congrArg τ hpure
    have h2 := congrArg β hmap
    have h3 := congrArg (fun z ↦ β (coefficientTensorGenerator.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R)
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R))
      (F.obj P) 0 n n hij WX z
      (((O.moduleAdjunction.unit.app (P.X n)).val.app W) y))) hunit
    have h4 := hbA n hij WX
      ((((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
        O.coefficient).hom.app W) a)
      (((O.moduleAdjunction.unit.app (P.X n)).val.app W) y)
    have hb := hbB n hij W a y
    rw [hx] at hb
    have hleft := congrArg ((O.moduleAdjunction.unit.app (P.X n)).val.app W) hb
    exact hleft.trans
      ((((O.moduleAdjunction.unit.app (P.X n)).val.app W).hom.map_smul a y).trans
        (h1.trans (h2.trans (h3.trans h4))).symm)
  · apply IsZero.eq_of_src
    apply (tensorRight (P.X j)).map_isZero
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi

end WeilConjectures.AdicQbarRealization.Proper
