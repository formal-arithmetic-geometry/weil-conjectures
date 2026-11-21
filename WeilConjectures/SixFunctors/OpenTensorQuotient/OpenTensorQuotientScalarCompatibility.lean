/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenQuotientScalarCompatibilityData
import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenQuotientScalarComparisonExistence
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenScalarTransitionCompatibility
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenFiniteScalarComparison

/-! # Scalar units and open restriction of strict quotient towers

## References

* [Stacks, Tag 03DI]
* [Stacks, Tag 03EK]
* [Stacks, Tag 0941]
* [Stacks, Tag 0E8I]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient
attribute [local implicit_reducible] reductionTower unrestrictedIntegralComplexFunctor
  unrestrictedIntegralReductionFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The scalar-adjunction unit as a map of strict towers, before localization. -/
def scalarUnitTower (W : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (Functor.const ℕᵒᵖ).obj P ⟶ (reductionTower l E W).obj P :=
  NatTrans.ofOpSequence (fun n ↦ unrestrictedTowerUnit l E W P n) (by
    intro n
    simp only [Functor.const_obj_map, reductionTower, Functor.flip_obj_map,
      Functor.ofOpSequence_map_homOfLE_succ]
    ext i V x
    change (((unrestrictedTowerUnit l E W P n).f i).val.app V) x =
      ((((unrestrictedIntegralTransition l E W n).app P).f i).val.app V)
        ((((unrestrictedTowerUnit l E W P (n + 1)).f i).val.app V) x)
    rw [unrestrictedTowerUnit_condition, unrestrictedTowerUnit_condition]
    have hone :
        ((integralCoefficientSheafTransition l E W n).hom.app V) (1 : _) = 1 :=
      map_one ((integralCoefficientSheafTransition l E W n).hom.app V).hom
    exact (congrArg (fun a ↦ unrestrictedIntegralTensorSection l E W n (P.X i) V a x)
      hone.symm).trans
        ((unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec
          P i V 1 x).symm)

/-- The unit tower has the scalar-unit formula at every degree and level. -/
theorem scalarUnitTower_sections (W : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (n : ℕ) (i : ℤ) (V : W.ProEtᵒᵖ) (x : (P.X i).val.obj V) :
    (((scalarUnitTower l E W P).app (op n)).f i).val.app V x =
      unrestrictedIntegralTensorSection l E W n (P.X i) V 1 x :=
  unrestrictedTowerUnit_condition l E W P n i V x

/-- Scalar units are natural in the entire complex, including every differential. -/
theorem scalarUnitTower_natural (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (f : P ⟶ Q) :
    (Functor.const ℕᵒᵖ).map f ≫ scalarUnitTower l E W Q =
      scalarUnitTower l E W P ≫ (reductionTower l E W).map f := by
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro i
  exact ((scalarReductionExtension_adjunction l E W n.unop).choose.unit.naturality
    (f.f i))

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local irreducible] scalarReductionExistence scalarReductionExtension
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted

/-- For fixed normalized scalar data and a strict scalar comparison, the scalar-adjunction
unit agrees with extension by zero. -/
theorem openQuotientScalarUnitEquation
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o)
    (sc : ScalarCompatibility l E j o)
    (r : ScalarComparison l E j o sc tc) :
    ∀ P : CochainComplex (scalarReductionSource l E U) ℤ,
      scalarUnitTower l E X ((OpenSemilinearTensor.extensionComplex l E j o).obj P) ≫
          r.iso.hom.app P =
        (Functor.constComp ℕᵒᵖ P (OpenSemilinearTensor.extensionComplex l E j o)).inv ≫
          Functor.whiskerRight (scalarUnitTower l E U P)
            (OpenSemilinearTensor.extensionComplex l E j o) := by
  intro P
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro i
  change (scalarReductionExtension_adjunction l E X n.unop).choose.unit.app
      ((IntegralOpenReduction.extension l E j o).obj (P.X i)) ≫
        ((r.iso.hom.app P).app n).f i =
    (IntegralOpenReduction.extension l E j o).map
      ((scalarReductionExtension_adjunction l E U n.unop).choose.unit.app (P.X i))
  have hr := r.components P n.unop i
  refine (congrArg
    ((scalarReductionExtension_adjunction l E X n.unop).choose.unit.app
      ((IntegralOpenReduction.extension l E j o).obj (P.X i)) ≫ ·) hr).trans ?_
  apply OpenSemilinearTensor.extensionSection_ext l E j o (P.X i) _
  intro V a x
  change ((sc.finite n.unop).hom.app
      ((scalarReductionExtension l E U n.unop).obj (P.X i))).val.app (op V)
    (((tc.ordinary n.unop).hom.app (P.X i)).val.app (op V)
      (((scalarReductionExtension_adjunction l E X n.unop).choose.unit.app
        ((IntegralOpenReduction.extension l E j o).obj (P.X i))).val.app (op V)
          (IntegralOpenReduction.extensionSection l E j o (P.X i) V a x))) = _
  have ht := congrArg
    (fun z ↦ ((sc.finite n.unop).hom.app
      ((scalarReductionExtension l E U n.unop).obj (P.X i))).val.app (op V) z)
    (tc.generators n.unop (P.X i) V a x)
  have hs := sc.sections n.unop
    ((scalarReductionExtension l E U n.unop).obj (P.X i)) V a
    (coefficientIntegralScalarUnitSection l E U n.unop (P.X i)
      (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) x)
  have hm := OpenSemilinearTensor.extensionSection_map l E j o
    ((scalarReductionExtension_adjunction l E U n.unop).choose.unit.app (P.X i)) V a x
  exact ht.trans (hs.trans hm.symm)

/-- Scalar restriction of the fixed open operations admits a strict comparison which
intertwines the actual scalar-adjunction units on every complex. This is only the
scalar comparison; no tensor balancing or open tensor square is asserted. -/
theorem openQuotientScalarUnitCompatibility
    (o : IntegralOpenReduction.Operations l E j)
    (tc : IntegralOpenReduction.TensorComparison l E j o) :
    ∃ (sc : ScalarCompatibility l E j o) (r : ScalarComparison l E j o sc tc),
      ∀ P : CochainComplex (scalarReductionSource l E U) ℤ,
        scalarUnitTower l E X ((OpenSemilinearTensor.extensionComplex l E j o).obj P) ≫
            r.iso.hom.app P =
          (Functor.constComp ℕᵒᵖ P (OpenSemilinearTensor.extensionComplex l E j o)).inv ≫
            Functor.whiskerRight (scalarUnitTower l E U P)
              (OpenSemilinearTensor.extensionComplex l E j o) := by
  obtain ⟨sc⟩ := openQuotientScalarCompatibilityData l E j o
  obtain ⟨r⟩ := openQuotientScalarComparisonExistence l E j o tc sc
  exact ⟨sc, r, openQuotientScalarUnitEquation l E j o tc sc r⟩

end WeilConjectures.OpenTensorQuotient
