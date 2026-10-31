/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTowerData.FinitePullbackStrictTowerData
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerAugmentationGenerators

/-! # Augmentation square for a normalized Koszul comparison

Source: Stacks Project, sites-cohomology.tex, Tag 07A4 and sites-modules.tex, Tag 03EL.
(blueprint: lem-a1-balanced-finite-tower-augmentation-square).

The proof is the two-generator calculation on the degree minus one and degree
zero free summands, followed by sheafification and total-complex extensionality. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.FinitePullbackStrictTowerData
open WeilConjectures.CompletedPullbackUniverseTransportData
namespace WeilConjectures.BalancedFiniteTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (W : Scheme.{t})
private theorem zero_basis_isIso (n : ℕ) : IsIso (koszulZero l E W n) := by
  let R := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)
  let D := (CochainComplex.singleFunctor (Modules l E W) 0).obj R
  let f := (CochainComplex.singleFunctor (Modules l E W) 0).map
    (PrincipalKoszulStrictReplacement.multiplication l E W n)
  have hz : IsZero (D.X 1) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 R 1 (by decide)
  have hi : IsIso (biprod.inr : D.X 0 ⟶ D.X 1 ⊞ D.X 0) := by
    change IsIso (isoZeroBiprod hz).hom
    infer_instance
  change IsIso ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 R).inv ≫
    HomologicalComplex.homotopyCofiber.inrX f 0)
  have hi' : IsIso (HomologicalComplex.homotopyCofiber.inrX f 0) := by
    rw [← HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv f 1 0 (by decide)]
    change IsIso ((isoZeroBiprod hz).hom ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f 0 1 (by decide)).inv)
    infer_instance
  infer_instance

private theorem negative_basis_isIso (n : ℕ) : IsIso (koszulMinusOne l E W n) := by
  let R := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)
  let D := (CochainComplex.singleFunctor (Modules l E W) 0).obj R
  let f := (CochainComplex.singleFunctor (Modules l E W) 0).map
    (PrincipalKoszulStrictReplacement.multiplication l E W n)
  have hz : IsZero (D.X (-1)) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 R (-1) (by decide)
  have hi : IsIso (biprod.inl : D.X 0 ⟶ D.X 0 ⊞ D.X (-1)) := by
    change IsIso (isoBiprodZero hz).hom
    infer_instance
  change IsIso ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 R).inv ≫
    HomologicalComplex.homotopyCofiber.inlX f 0 (-1) (by decide))
  have hi' : IsIso (HomologicalComplex.homotopyCofiber.inlX f 0 (-1) (by decide)) := by
    rw [← HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv f 0 (-1) (by decide)]
    change IsIso ((isoBiprodZero hz).hom ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f (-1) 0 (by decide)).inv)
    infer_instance
  infer_instance

end WeilConjectures.BalancedFiniteTower

namespace WeilConjectures.BalancedFiniteTower
open CategoryTheory.MonoidalCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (W : Scheme.{t})
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem tensor_generator_balance
    (P Q : CochainComplex (Modules l E W) ℤ) (p q k : ℤ) (hpq : p + q = k)
    (U : W.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l E W).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    tensorGenerator l E W P Q p q k hpq U x (a • y) =
      tensorGenerator l E W P Q p q k hpq U (a • x) y := by
  unfold tensorGenerator coefficientTensorGenerator
  rw [TensorProduct.tmul_smul]
  rw [TensorProduct.smul_tmul']

private theorem basis_generator_balance (P : CochainComplex (Modules l E W) ℤ)
    (n : ℕ) (negative : Bool) (p k : ℤ) (hp : p + koszulDegree negative = k)
    (U : W.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l E W).obj.obj U)
    (x : (P.X p).val.obj U) :
    tensorGenerator l E W P (PrincipalKoszulStrictReplacement.koszul l E W n)
      p (koszulDegree negative) k hp U x ((koszulBasis l E W n negative).val.app U a) =
    tensorGenerator l E W P (PrincipalKoszulStrictReplacement.koszul l E W n)
      p (koszulDegree negative) k hp U (a • x)
        ((koszulBasis l E W n negative).val.app U
          (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U)) := by
  have ha : (koszulBasis l E W n negative).val.app U a =
      a • ((koszulBasis l E W n negative).val.app U
          (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U)) := by
    rw [← map_smul]
    congr 1
    exact (mul_one a).symm
  rw [ha]
  exact tensor_generator_balance l E W P _ p _ k hp U a x _

private theorem total_sections_ext
    (P Q : CochainComplex (Modules l E W) ℤ) (k : ℤ) (N : Modules l E W)
    {f h : (((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k) ⟶ N}
    (heq : ∀ (p q : ℤ) (hpq : p + q = k) (U : W.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      f.val.app U (tensorGenerator l E W P Q p q k hpq U x y) =
        h.val.app U (tensorGenerator l E W P Q p q k hpq U x y)) : f = h := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  let adj := PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat RingCat)).obj
      (completedIntegralCommRingSheafUnrestricted l E W)).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification
    (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X p) (Q.X q)).inv).mp
  apply (adj.homEquiv ((P.X p).val ⊗ (Q.X q).val) N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact heq p q hpq U x y

private theorem total_basis_ext (P : CochainComplex (Modules l E W) ℤ)
    (n : ℕ) (k : ℤ) (N : Modules l E W)
    {f h : (((H l E W P).obj (op n)).X k) ⟶ N}
    (hbase : ∀ (negative : Bool) (p : ℤ) (hp : p + koszulDegree negative = k)
      (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U),
      f.val.app U (tensorGenerator l E W P
        (PrincipalKoszulStrictReplacement.koszul l E W n)
        p (koszulDegree negative) k hp U x
        ((koszulBasis l E W n negative).val.app U
          (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U))) =
      h.val.app U (tensorGenerator l E W P
        (PrincipalKoszulStrictReplacement.koszul l E W n)
        p (koszulDegree negative) k hp U x
        ((koszulBasis l E W n negative).val.app U
          (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U)))) : f = h := by
  apply total_sections_ext l E W P (PrincipalKoszulStrictReplacement.koszul l E W n) k N
  intro p q hpq U x y
  have hb (negative : Bool) : IsIso (koszulBasis l E W n negative) := by
    cases negative
    · exact zero_basis_isIso l E W n
    · exact negative_basis_isIso l E W n
  by_cases hq : q = 0
  · subst q
    let a : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U :=
      ((inv (koszulBasis l E W n false)).val.app U) y
    have hy : (koszulBasis l E W n false).val.app U a = y := by
      have he := congrArg (fun z ↦ z.val.app U y)
        (IsIso.inv_hom_id (koszulBasis l E W n false))
      exact he
    erw [← hy, basis_generator_balance l E W P n false p k hpq U a x]
    exact hbase false p hpq U (a • x)
  · by_cases hq' : q = -1
    · subst q
      let a : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U :=
        ((inv (koszulBasis l E W n true)).val.app U) y
      have hy : (koszulBasis l E W n true).val.app U a = y := by
        have he := congrArg (fun z ↦ z.val.app U y)
          (IsIso.inv_hom_id (koszulBasis l E W n true))
        exact he
      erw [← hy, basis_generator_balance l E W P n true p k hpq U a x]
      exact hbase true p hpq U (a • x)
    · have hz : IsZero ((PrincipalKoszulStrictReplacement.koszul l E W n).X q) := by
        apply (CochainComplex.mappingCone.isZero_X_iff _ q).2
        constructor
        · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ _ (by omega)
        · exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ q hq
      have hy : y = 0 := by
        have he := congrArg (fun z ↦ z.val.app U y) (hz.eq_of_src (𝟙 _) 0)
        exact he
      rw [hy]
      simp [tensorGenerator, coefficientTensorGenerator]

end WeilConjectures.BalancedFiniteTower

namespace WeilConjectures.BalancedFiniteTower
open CategoryTheory.MonoidalCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)
private theorem pulled_basis_ext (P : CochainComplex (Modules l E Y) ℤ)
    (n : ℕ) (k : ℤ) (N : Modules l E X)
    {f h : (pull l E g).obj (((H l E Y P).obj (op n)).X k) ⟶ N}
    (hbase : ∀ (negative : Bool) (p : ℤ) (hp : p + koszulDegree negative = k)
      (V : Y.ProEt) (x : (P.X p).val.obj (op V)),
      f.val.app (op ((Scheme.proEtaleBaseChange g).obj V))
        (generator l E g (((H l E Y P).obj (op n)).X k) V
          (tensorGenerator l E Y P (PrincipalKoszulStrictReplacement.koszul l E Y n)
            p (koszulDegree negative) k hp (op V) x
            ((koszulBasis l E Y n negative).val.app (op V)
              (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))))) =
      h.val.app (op ((Scheme.proEtaleBaseChange g).obj V))
        (generator l E g (((H l E Y P).obj (op n)).X k) V
          (tensorGenerator l E Y P (PrincipalKoszulStrictReplacement.koszul l E Y n)
            p (koszulDegree negative) k hp (op V) x
            ((koszulBasis l E Y n negative).val.app (op V)
              (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V)))))) :
    f = h := by
  apply ((adjunction l E g).homEquiv _ _).injective
  apply total_basis_ext l E Y P n k ((push l E g).obj N)
  intro negative p hp U x
  exact hbase negative p hp U.unop x
end WeilConjectures.BalancedFiniteTower

namespace WeilConjectures.BalancedFiniteTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Equality on the two pulled basis tensors extends to the augmentation square.
Source: Stacks 03EK, sheafified tensor universal property.
(blueprint: lem-a1-balanced-finite-tower-augmentation-square).

Proof: both Koszul basis maps are isomorphisms, as the other summand of the
corresponding cone degree is zero. Totalization extensionality reduces to a
homogeneous tensor summand. Sheafification adjunction and tensor extensionality
reduce this summand to pure tensors. Outside degrees 0 and -1 the Koszul term
is zero; in either actual degree move the coefficient of the free basis to
the first factor by tensor balancing. Finally transpose the pulled maps across
the ordinary pullback adjunction and apply the generator calculation. -/
theorem normalized_theta_augmentation_square
    (lambda : G l E g ⋙ reductions l E X ≅ finite l E g)
    (c : reductions l E Y ⋙ diagramPull l E g ≅ finite l E g)
    (hlambda : ∀ P : CochainComplex (Modules l E Y) ℤ,
      BalancedNormalization l E g P (lambda.app P))
    (hc : QuotientUnitNormalization l E g c)
    (theta : koszuls l E Y ⋙ diagramPull l E g ≅ G l E g ⋙ koszuls l E X)
    (P : CochainComplex (Modules l E Y) ℤ)
    (htheta : KoszulNormalization l E g P (theta.app P)) (n : ℕᵒᵖ) (k : ℤ) :
    (((theta.hom.app P) ≫ augmentation l E X ((G l E g).obj P) ≫
      lambda.hom.app P).app n).f k =
        (((diagramPull l E g).map (augmentation l E Y P) ≫ c.hom.app P).app n).f k := by
  apply pulled_basis_ext l E g P n.unop k _
  intro negative p hp V x
  exact normalized_theta_augmentation_generators l E g lambda c hlambda hc
    theta P htheta n.unop k negative p hp V x

end WeilConjectures.BalancedFiniteTower
