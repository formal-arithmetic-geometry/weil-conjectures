/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.SixFunctors.IntegralHom.HomComplexTensorPureEquivalence
import WeilConjectures.SixFunctors.IntegralHom.Tensor.TensorEvaluationInterchange
import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermCoordinateEvaluation
import WeilConjectures.SixFunctors.IntegralHom.TotalTensorHomEvaluationExt

/-! # Finite-coordinate existence and uniqueness for the two-term Hom--tensor map

## References

* [Stacks, Tag 0A8X]
* [Stacks, Tag 08J7]
-/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option quotPrecheck false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace WeilConjectures.IntegralHom
attribute [local instance 2000] abSheafify abLocallyBijective
attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

local notation "J" => AlgebraicGeometry.Scheme.ProEt.topology Y

private theorem generator_transport
    (A B : CochainComplex (Modules.{t, u} Y R) ℤ) (p q n : ℤ) (h : p + q = n)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X p).val.obj U) (y : (B.X q).val.obj U) :
    (eqToHom (congrArg (fun k ↦ (((totalTensor.{t, u} Y R).obj A).obj B).X k) h)).val.app U
        (totalPair.{t, u} Y R A B p q U x y) =
      coefficientTensorGenerator.{u, t + 1, t} J R A B p q n h U x y := by
  subst n
  rfl

/-- The actual signed evaluation formula for tensoring an internal Hom complex.
The degree transport only reassociates integer addition. -/
def IsSignedHomTensor
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (f : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q)) : Prop :=
  ∀ (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (v : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X a
      |>.val.obj U)
    (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
    evaluate Y R P (((totalTensor Y R).obj I).obj Q) (a + b) p U
        ((f.f (a + b)).val.app U
          (totalPair Y R
            (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)
            Q a b U v z)) x =
      (b * p).negOnePow •
        (eqToHom (congrArg
          (fun k : ℤ ↦ (((totalTensor Y R).obj I).obj Q).X k)
          (add_assoc p a b))).val.app U
            (totalPair Y R I Q (p + a) b U (evaluate Y R P I a p U v x) z)

/-- The finite-free coordinate construction produces an isomorphism in each total degree. -/
theorem twoTermFreeHomTensor_coordinate_exists
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (j : ℤ) : ∃ g : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q), IsIso (g.f j) ∧
      ∀ (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (v : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X a
          |>.val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
        evaluate Y R P (((totalTensor Y R).obj I).obj Q) (a + b) p U
          ((g.f (a + b)).val.app U
            (totalPair Y R (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
              (R := R) P I) Q a b U v z)) x =
          (b * p).negOnePow •
            (eqToHom (congrArg (fun k : ℤ ↦ (((totalTensor Y R).obj I).obj Q).X k)
              (add_assoc p a b))).val.app U
              (totalPair Y R I Q (p + a) b U (evaluate Y R P I a p U v x) z) := by
  let H := homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I
  obtain ⟨uncurry, huncurry⟩ := homComplexTensor_pure_equivalence Y R H P I
  let e := uncurry.symm (𝟙 H)
  obtain ⟨psi, hpsi⟩ := tensorEvaluation_interchange Y R H P I Q e
  let HQ := ((totalTensor.{t, u} Y R).obj H).obj Q
  let IQ := ((totalTensor.{t, u} Y R).obj I).obj Q
  obtain ⟨curry, hcurry⟩ := homComplexTensor_pure_equivalence Y R HQ P IQ
  let f := curry psi
  have hf : IsSignedHomTensor Y R P I Q f := by
    intro a b p U v z x
    change evaluate.{t, u} Y R P IQ (a + b) p U
      (((curry psi).f (a + b)).val.app U (totalPair.{t, u} Y R H Q a b U v z)) x = _
    have hstart := hcurry psi (a + b) p U (totalPair.{t, u} Y R H Q a b U v z) x
    have hcalc := hpsi a b p U v z x
    have he := huncurry e a p U v x
    have hid : uncurry e = 𝟙 H := uncurry.apply_symm_apply _
    rw [hid] at he
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app] at he
    have ht := generator_transport Y R I Q (p + a) b (p + (a + b))
      (add_assoc p a b) U (evaluate.{t, u} Y R P I a p U v x) z
    exact hstart.trans (hcalc.trans
      ((congrArg (fun w ↦ (b * p).negOnePow •
        coefficientTensorGenerator.{u, t + 1, t} J R I Q (p + a) b (p + (a + b))
          (add_assoc p a b) U w z) he.symm).trans
        (congrArg (fun w ↦ (b * p).negOnePow • w) ht.symm)))
  refine ⟨f, ?_, hf⟩
  have eNeg' : Q.X (-1) ≅
      @MonoidalCategory.tensorUnit (Modules.{t, u} Y R) _
        (SheafOfModules.monoidalCategory R).toMonoidalCategoryStruct := by
    unfold SheafOfModules.monoidalCategory
    exact eNeg
  have eZero' : Q.X 0 ≅
      @MonoidalCategory.tensorUnit (Modules.{t, u} Y R) _
        (SheafOfModules.monoidalCategory R).toMonoidalCategoryStruct := by
    unfold SheafOfModules.monoidalCategory
    exact eZero
  apply twoTermCoordinate_isIso Y R Q hzero eNeg' eZero' P I j (f.f j)
  intro a b hab p U v z x
  subst j
  exact hf a b p U v z x

/-- The product projections make the signed coordinate construction unique. -/
theorem twoTermFreeHomTensor_coordinate_unique
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (f g : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q))
    (hf : IsSignedHomTensor Y R P I Q f) (j : ℤ)
    (hg : ∀ (a b p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (v : (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I).X a
          |>.val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
        evaluate Y R P (((totalTensor Y R).obj I).obj Q) (a + b) p U
          ((g.f (a + b)).val.app U
            (totalPair Y R (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
              (R := R) P I) Q a b U v z)) x =
          (b * p).negOnePow •
            (eqToHom (congrArg (fun k : ℤ ↦ (((totalTensor Y R).obj I).obj Q).X k)
              (add_assoc p a b))).val.app U
              (totalPair Y R I Q (p + a) b U (evaluate Y R P I a p U v x) z)) :
    f.f j = g.f j := by
  have _ := hzero
  have _ := eNeg
  have _ := eZero
  apply totalTensorHomEvaluation_ext Y R _ Q P _ j (f.f j) (g.f j)
  intro a b hab p U v z x
  subst j
  exact (hf a b p U v z x).trans (hg a b p U v z x).symm
end WeilConjectures.IntegralHom
