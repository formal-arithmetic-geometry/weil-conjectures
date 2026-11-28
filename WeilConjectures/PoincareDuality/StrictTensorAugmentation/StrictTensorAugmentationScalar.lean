/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentation
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

/-! # The strict tensor augmentation under scalar extension

Ordinary scalar extension of coefficients carries the strict ordinary-to-completed tensor map
to the strict ordinary-to-completed tensor map, conjugated by the ordinary and completed tensor
scalar comparisons, already before localization.

## References

* Stacks Project, Tags 03EL, 07A4, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.StrictTensorAugmentation
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  integralOperationsRoos integralOperationsRoosFunctor

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- A map into the Roos cocone of a strict tower followed by a scalar Roos comparison is
determined by levelwise product coordinates, once both second coordinates vanish. -/
private theorem scalarRoos_ext {A B : Type*} [Category* A] [Category* B] [Abelian A]
    [Abelian B] [HasCountableProducts A] [HasCountableProducts B] (F : A ⥤ B) [F.Additive]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (C' : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (t : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ C')
    {X : CochainComplex A ℤ} {Y : CochainComplex B ℤ}
    (a : X ⟶ integralOperationsRoos C) (c : (F.mapHomologicalComplex (.up ℤ)).obj X ⟶ Y)
    (b : Y ⟶ integralOperationsRoos C')
    (s : (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C) ⟶
      integralOperationsRoos C')
    (hs : s = scalarRoosMap F C ≫ integralOperationsRoosMap t)
    (ha : ∀ i, a.f i ≫ (CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v
      i (i - 1) (by omega) = 0)
    (hb : ∀ i, b.f i ≫ (CochainComplex.mappingCocone.snd (scalarRoosBoundary C')).v
      i (i - 1) (by omega) = 0)
    (hf : ∀ (n : ℕ) (k : ℤ), F.map ((a ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary C) ≫ Pi.π (fun j ↦ C.obj (op j)) n).f k) ≫ (t.app (op n)).f k =
      c.f k ≫ (b ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C') ≫
        Pi.π (fun j ↦ C'.obj (op j)) n).f k) :
    (F.mapHomologicalComplex (.up ℤ)).map a ≫ s = c ≫ b := by
  subst hs
  obtain ⟨hσf, hσs⟩ := scalarRoosCoordinates F C
  obtain ⟨hτf, hτs⟩ := scalarRoosTowerCoordinates t
  apply mappingCocone_hom_ext
  · apply Pi.hom_ext
    intro n
    apply HomologicalComplex.hom_ext
    intro k
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, reassoc_of% hτf,
      Pi.map_π, reassoc_of% hσf, piComparison_comp_π_assoc, ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Category.assoc, hf n k]
    simp only [HomologicalComplex.comp_f, Category.assoc]
  · intro i
    rw [HomologicalComplex.comp_f c b, Category.assoc, hb i, comp_zero,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
      hτs i (i - 1) (by omega), reassoc_of% (hσs i), Functor.mapHomologicalComplex_map_f,
      ← F.map_comp_assoc, ha i,
      F.map_zero, zero_comp]

/-- Maps out of the ordinary scalar extension of a total tensor term are determined by the
scalar extensions of the pure total tensors. -/
private theorem scalarTotal_hom_ext (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ)
    (H : integralTowerModules l L W)
    {f g : (integralOrdinaryScalar l E L ι W).obj
      ((((@coefficientTotalTensor.{u, u + 1, u} W.ProEt _ (Scheme.ProEt.topology W)
        (integralOperationsAbSheafify.{u, u} W)
        (integralOperationsAbLocallyBijective.{u, u} W)
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E W))).obj (P, Q)).X k) ⟶ H}
    (h : ∀ (p q : ℤ) (hpq : p + q = k) (U : W.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      f.val.app U (integralOrdinaryTensorSection l E L ι W _ U 1
        (@coefficientTensorGenerator.{u, u + 1, u} W.ProEt _ (Scheme.ProEt.topology W)
          (integralOperationsAbSheafify.{u, u} W)
          (integralOperationsAbLocallyBijective.{u, u} W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq U x y)) =
      g.val.app U (integralOrdinaryTensorSection l E L ι W _ U 1
        (@coefficientTensorGenerator.{u, u + 1, u} W.ProEt _ (Scheme.ProEt.topology W)
          (integralOperationsAbSheafify.{u, u} W)
          (integralOperationsAbLocallyBijective.{u, u} W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq U x y))) :
    f = g := by
  apply ((scalarAdjunction l E L ι W).homEquiv _ _).injective
  apply total_hom_ext l E W P Q k
  intro p q hpq U x y
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarAdjunction_unit]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    scalarAdjunction_unit]
  exact h p q hpq U x y

/-- The levels of the scalar tensor tower map are the normalized finite-level maps. -/
private theorem scalarTensorTower_app_app (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    ((scalarTensorTower l E L ι W).app (P, Q)).app (op n) =
      (scalarTensorLevel l E L ι W n).app (P, Q) :=
  (scalarTensorTower_existsUnique l E L ι W).exists.choose_spec P Q n

attribute [local irreducible] integralOperationsTensorTowerFunctor in
/-- The levelwise product coordinates of both routes agree. -/
private theorem map_scalar_level (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (k : ℤ) :
    (integralOrdinaryScalar l E L ι W).map
        (((map l E W).app (P, Q) ≫
          CochainComplex.mappingCocone.fst
            (scalarRoosBoundary ((integralOperationsTensorTowerFunctor l E W).obj (P, Q))) ≫
          Pi.π (fun j ↦ ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op j))
            n).f k) ≫
      (((scalarTensorTower l E L ι W).app (P, Q)).app (op n)).f k =
    ((scalarOrdinaryTensorChain l E L ι W).hom.app (P, Q)).f k ≫
      ((map l L W).app
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
            ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary
          ((integralOperationsTensorTowerFunctor l L W).obj
            (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
              ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))) ≫
        Pi.π (fun j ↦ ((integralOperationsTensorTowerFunctor l L W).obj
            (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
              ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)).obj
            (op j)) n).f k := by
  rw [scalarTensorTower_app_app]
  apply scalarTotal_hom_ext
  intro p q hpq U x y
  cases hpq
  have hE := (coordinates l E W).1 P Q p q n U x y
  have hL := (coordinates l L W).1
    (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)
    (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) p q n U
    (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
    (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f] at hE hL
  have h1 := scalar_map_tensor l E L ι W
    (((map l E W).app (P, Q) ≫ CochainComplex.mappingCocone.fst
      (scalarRoosBoundary ((integralOperationsTensorTowerFunctor l E W).obj (P, Q))) ≫
      Pi.π (fun j ↦ ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op j))
        n).f (p + q)) U 1
    (@coefficientTensorGenerator.{u, u + 1, u} W.ProEt _ (Scheme.ProEt.topology W)
      (integralOperationsAbSheafify.{u, u} W) (integralOperationsAbLocallyBijective.{u, u} W)
      (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y)
  rw [hE] at h1
  have h2 := (scalarTensorLevel_existsUnique l E L ι W n).exists.choose_spec P Q p q U x y
  have h3 := (scalarOrdinaryTensorChain_existsUnique l E L ι W).exists.choose_spec
    P Q p q U x y
  with_unfolding_all
    refine (congrArg (fun z ↦
      (((scalarTensorLevel l E L ι W n).app (P, Q)).f (p + q)).val.app U z) h1).trans ?_
  with_unfolding_all
    refine h2.trans ?_
  with_unfolding_all
    refine hL.symm.trans ?_
  with_unfolding_all
    exact (congrArg _ h3).symm

attribute [local irreducible] integralOperationsTensorTowerFunctor in
theorem map_scalar (W : Scheme.{u}) (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).map
        ((map l E W).app (P, Q)) ≫ scalarTensorChain l E L ι W P Q =
      (scalarOrdinaryTensorChain l E L ι W).hom.app (P, Q) ≫
        (map l L W).app
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
            ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) :=
  scalarRoos_ext (integralOrdinaryScalar l E L ι W)
    ((integralOperationsTensorTowerFunctor l E W).obj (P, Q))
    ((integralOperationsTensorTowerFunctor l L W).obj
      (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))
    ((scalarTensorTower l E L ι W).app (P, Q)) ((map l E W).app (P, Q))
    ((scalarOrdinaryTensorChain l E L ι W).hom.app (P, Q))
    ((map l L W).app
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
            ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))
    (scalarTensorChain l E L ι W P Q) (by unfold scalarTensorChain; rfl)
    ((coordinates l E W).2 P Q) ((coordinates l L W).2 _ _) (map_scalar_level l E L ι W P Q)

end WeilConjectures.StrictTensorAugmentation
