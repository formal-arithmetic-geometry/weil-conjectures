/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Coefficient and scalar-presentation constructions.
(blueprint: lem-sp-general-ring-prime-quotient-equivalence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Generator-normalized coefficient comparison at a common positive exponent.
Source: Kummer generator comparison
(blueprint: lem-sp-general-ring-common-exponent-line). -/
theorem generalRingCoefficientLine
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    Nonempty (Etale.FiniteSmoothPurity.CoefficientLineComparison φ N N hA hB T) := by
  have hi := reductionTateOrdinaryScalar_isIso φ T N hA hB
  exact ⟨{
    roots := 𝟙 _
    roots_power := by
      rw [Nat.div_self hN, one_nsmul]
      exact Category.id_comp _
    sheafIso := asIso (((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
      (reductionEtaleTateMap φ T N hA hB))
    generators := by
      intro W a z
      simp only [asIso_hom, Equiv.apply_symm_apply]
      change (reductionEtaleTateMap φ T N hA hB).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N T hA W a z) =
          Scheme.finiteEtaleTateOneGenerator B N T hB W (φ a) z
      simpa only [reductionEtaleTateMap] using
        (reductionEtaleTateMap_existsUnique φ T N hA hB).exists.choose_spec W a z
    derivedIso := reductionEtaleTateIso φ T N hA hB hT
    derived_normalization := Eq.refl
      (WeilConjectures.PurityFiniteSetting.purityScalarSingleMap φ T
          (Scheme.finiteEtaleTateLine T N A hA) ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map
          (((etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).symm
            (reductionEtaleTateMap φ T N hA hB))) }⟩

/-- Naturality of the intrinsic-to-fixed scalar presentation.
Source: scalar realization equivalence
(blueprint: lem-sp-general-ring-scalar-presentation-naturality). -/
theorem scalarPresentation_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    {K L : Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} A) T}
    (g : K ⟶ L) :
    (finiteGeneralRingScalar φ T).map g ≫ (finiteGeneralRingScalarIso φ T L).hom =
      (finiteGeneralRingScalarIso φ T K).hom ≫
        (Etale.FiniteSmoothPurity.proScalar φ.ulift T).map g := by
  let E := sfIntrinsicDerivedEquivalence T B
  have hn := (reductionRealizationScalarIso φ T).hom.naturality g
  have hu := E.unitIso.inv.naturality
    ((Etale.FiniteSmoothPurity.proScalar φ.ulift T).map g)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
    Etale.FiniteSmoothPurity.proScalar] at hn hu
  dsimp only [finiteGeneralRingScalar, finiteGeneralRingScalarIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Etale.FiniteSmoothPurity.proScalar, Functor.comp_map, Functor.comp_obj, Functor.id_obj]
  rw [← E.inverse.map_comp_assoc, hn, E.inverse.map_comp, Category.assoc, hu, ← Category.assoc]


end AlgebraicGeometry.ProEtale
