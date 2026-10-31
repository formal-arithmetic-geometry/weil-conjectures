/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.Integral.IntegralPositiveReductionConstructible
import WeilConjectures.AlgebraicGeometry.Integral.IntegralReductionUnderlyingDirectImage
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Classical models for finite integral reductions and their proper images -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private noncomputable def encodingForgetIso
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (X : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A X) :
    (e.ordinary.functor ⋙ e.fixed.functor) ⋙
        sheafCompose (Scheme.ProEt.topology X)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}) ≅
      Mod.forget (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) X) := by
  rw [e.ordinary_functor, e.fixed_functor]
  exact NatIso.ofComponents (fun M ↦ Iso.refl _) (fun f ↦ by rfl)

private theorem finiteConstantModel_etale_origin
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] (X : Scheme.{u}) [IsNoetherian X]
    (M : DerivedCategory (FiniteDiscreteOrdinary.Internal A X))
    (hM : constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X M) :
    ∃ L : DerivedCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))),
      DerivedCategory.TStructure.t.plus L ∧
      Nonempty ((Mod.forget (condensedRingObj
          (FiniteDiscreteOrdinary.coefficient A) X)).mapDerivedCategory.obj M ≅
        (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}) ⋙
            comparisonUpperStar Ab.{u + 1} X).mapDerivedCategory.obj L) := by
  obtain ⟨e, he⟩ := FiniteDiscreteOrdinary.finiteCoefficientModelComparison A X
  let F := e.ordinary.functor ⋙ e.fixed.functor
  let U := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})
  let : PreservesFiniteLimits U := by
    have : PreservesFiniteLimits (U ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1})))
    exact preservesFiniteLimits_of_reflects_of_preserves U (sheafToPresheaf _ _)
  let : PreservesFiniteColimits (F ⋙ U) :=
    preservesFiniteColimits_of_natIso (encodingForgetIso A X e).symm
  let : PreservesFiniteColimits U := by
    let H := e.ordinary.trans e.fixed
    let z : H.inverse ⋙ (F ⋙ U) ≅ U :=
      (Functor.associator H.inverse F U).symm ≪≫
        Functor.isoWhiskerRight H.counitIso U ≪≫ Functor.leftUnitor U
    exact preservesFiniteColimits_of_natIso z
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  let W := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}) ⋙
      comparisonUpperStar Ab.{u + 1} X
  have hb := (he.boundedConstructible M).mp hM
  have hc (q : ℤ) : IsConstructible (ULift.{u + 1} A)
      ((DerivedCategory.homologyFunctor _ q).obj (F.mapDerivedCategory.obj M)) := by
    have h := (Scheme.proEtaleModuleRestriction_constructible_iff X A _).mp (hb.2 q)
    let d := (FiniteDiscreteOrdinary.fixedIso A X e
      ((DerivedCategory.homologyFunctor _ q).obj (e.ordinaryDerived.functor.obj M))).symm
    let j := (e.ordinary.functor.mapDerivedCategoryHomologyFunctorIso q).app M
    let k := (F.mapDerivedCategoryHomologyFunctorIso q).app M
    exact isConstructible_of_iso
      (d ≪≫ e.fixed.functor.mapIso j.symm ≪≫ k) h
  obtain ⟨L, hL, ⟨eL⟩⟩ := DerivedCategory.boundedConstructible_of_homology
    (ULift.{u + 1} A) (F.bounded_mapDerivedCategory_obj hM.1)
      (fun q ↦ exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
        (ULift.{u + 1} A) (hc q))
  let d : F.mapDerivedCategory ⋙ U.mapDerivedCategory ≅
      (Mod.forget (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) X)).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso F U).symm ≪≫
      Functor.mapDerivedCategoryNatIso (encodingForgetIso A X e)
  let c : W.mapDerivedCategory ≅ C.mapDerivedCategory ⋙ U.mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso
      (sheafComposeForget₂CompComparisonUpperStarIso (ULift.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryCompIso C U
  exact ⟨L, hL.1.1, ⟨(d.app M).symm ≪≫ U.mapDerivedCategory.mapIso eL.symm ≪≫
    (c.app L).symm⟩⟩

private theorem realization_directImage
    (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (hL : DerivedCategory.TStructure.t.plus L) :
    let W (Z : Scheme.{u}) := sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ⋙ comparisonUpperStar Ab.{u + 1} Z
    Nonempty ((W Y).mapDerivedCategory.obj
      ((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj L) ≅
      (ProEtale.lowerStar Ab.{u + 1} p).rightDerivedFunctor.obj
        ((W X).mapDerivedCategory.obj L)) := by
  let SX := Etale.moduleAbelianForget R X
  let SY := Etale.moduleAbelianForget R Y
  let NX := comparisonUpperStar Ab.{u + 1} X
  let NY := comparisonUpperStar Ab.{u + 1} Y
  let GM := Etale.lowerStar (ModuleCat.{u + 1} R) p
  let GA := Etale.lowerStar Ab.{u + 1} p
  let GP := ProEtale.lowerStar Ab.{u + 1} p
  let LP : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    ⟨L, hL⟩
  obtain ⟨c⟩ := nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar Ab.{u + 1} p
  let d := (Etale.moduleAbelianDerivedLowerStarIso R p).app LP
  let e : SY.mapDerivedCategory.obj (GM.rightDerivedFunctor.obj L) ≅
      GA.rightDerivedFunctor.obj (SX.mapDerivedCategory.obj L) :=
    SY.mapDerivedCategory.mapIso (GM.rightDerivedFunctorPlusCompatibility.app LP).symm ≪≫
      DerivedCategory.Plus.ι.mapIso d ≪≫
      GA.rightDerivedFunctorPlusCompatibility.app (SX.mapDerivedCategoryPlus.obj LP)
  let f : NY.mapDerivedCategory.obj
      (GA.rightDerivedFunctor.obj (SX.mapDerivedCategory.obj L)) ≅
      GP.rightDerivedFunctor.obj (NX.mapDerivedCategory.obj
        (SX.mapDerivedCategory.obj L)) :=
    NY.mapDerivedCategory.mapIso
      (GA.rightDerivedFunctorPlusCompatibility.app (SX.mapDerivedCategoryPlus.obj LP)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso (c.app (SX.mapDerivedCategoryPlus.obj LP)) ≪≫
      GP.rightDerivedFunctorPlusCompatibility.app
        (NX.mapDerivedCategoryPlus.obj (SX.mapDerivedCategoryPlus.obj LP))
  exact ⟨(Functor.mapDerivedCategoryCompIso SY NY).app
      (GM.rightDerivedFunctor.obj L) ≪≫ NY.mapDerivedCategory.mapIso e ≪≫ f ≪≫
        GP.rightDerivedFunctor.mapIso ((Functor.mapDerivedCategoryCompIso SX NX).app L).symm⟩

/-- The finite-reduction classical models over a Noetherian source; no base field is used.
Source: blueprint lem-sfb-integral-proper-reduction-model, with the base field used only to
make the source Noetherian (blueprint: lem-sfb-integral-proper-reduction-model). -/
theorem integralProperReductionModel_of_isNoetherian
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Y) [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K)
    (n : ℕ) :
    let R := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
    let W (Z : Scheme.{u}) := sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ⋙ comparisonUpperStar Ab.{u + 1} Z
    ∃ L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)),
      Nonempty ((Mod.forget (AdicCompletion.ring l E X)).mapDerivedCategory.obj
        (AdicCompletion.integralLevel l E X K n) ≅ (W X).mapDerivedCategory.obj L) ∧
      Nonempty ((Mod.forget (AdicCompletion.ring l E Y)).mapDerivedCategory.obj
        (AdicCompletion.integralLevel l E Y
          ((CondensedRing.moduleObjectDerivedPushforward
            (DerivedNakayama.integerRing l E) p).obj K) n) ≅
        (W Y).mapDerivedCategory.obj
          ((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj L)) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology A := finiteTopology_discrete l E n
  let Q := (AdicCompletion.derivedReduction l E X n).obj K
  have hQ := integralReduction_constantModelBoundedConstructible l E X K hK n
  obtain ⟨L, hL, ⟨eL⟩⟩ := finiteConstantModel_etale_origin A X Q hQ
  let d : (Mod.forget (AdicCompletion.ring l E X)).mapDerivedCategory.obj
      (AdicCompletion.integralLevel l E X K n) ≅
      (Mod.forget (AdicCompletion.finiteRing l E X n)).mapDerivedCategory.obj Q :=
    ((Functor.mapDerivedCategoryCompIso
      (Mod.comap (AdicCompletion.quotient l E X n))
      (Mod.forget (AdicCompletion.ring l E X))).app Q).symm
  let e := d ≪≫ eL
  refine ⟨L, ⟨e⟩, ?_⟩
  obtain ⟨r⟩ := integralReduction_underlying_directImage l E p K hK.1 n
  obtain ⟨c⟩ := realization_directImage (ULift.{u + 1} A) p L hL
  exact ⟨r ≪≫ (ProEtale.lowerStar Ab.{u + 1} p).rightDerivedFunctor.mapIso e ≪≫ c.symm⟩


/-- Finite reductions admit bounded classical models, compatibly with proper image.
Source: blueprint main-20261015, integral proper direct sums, proof (1), finite
reduction and discrete direct-image comparison
(blueprint: lem-sfb-integral-proper-reduction-model).

Proof: The length-one free resolution of the positive quotient identifies derived
reduction with the cone of the uniformizer power. Finite presentation on each stratum
is preserved by this two-term construction. The finite discrete coefficient comparison
identifies its constructible cohomology with classical etale sheaves at the same
universe level. The fixed-module bounded constructible origin theorem gives L and
the first isomorphism, including torsion input.
For the second comparison, use the perfect quotient projection formula to commute
reduction with proper direct image. Restriction of scalars is exact, and forgetting
the action gives the same abelian sheaf. Apply discrete direct-image comparison to
L and then forget finite coefficients. These are ordinary derived images: the
perfect quotient projection formula requires no completed-image convention.
The quotient exponent n+1 is positive; the argument includes n=0 and K=0. -/
theorem integralProperReductionModel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K)
    (n : ℕ) :
    let R := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
    let W (Z : Scheme.{u}) := sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ⋙ comparisonUpperStar Ab.{u + 1} Z
    ∃ L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)),
      Nonempty ((Mod.forget (AdicCompletion.ring l E X)).mapDerivedCategory.obj
        (AdicCompletion.integralLevel l E X K n) ≅ (W X).mapDerivedCategory.obj L) ∧
      Nonempty ((Mod.forget (AdicCompletion.ring l E Y)).mapDerivedCategory.obj
        (AdicCompletion.integralLevel l E Y
          ((CondensedRing.moduleObjectDerivedPushforward
            (DerivedNakayama.integerRing l E) p).obj K) n) ≅
        (W Y).mapDerivedCategory.obj
          ((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj L)) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  exact integralProperReductionModel_of_isNoetherian l E p K hK n

end AlgebraicGeometry.ProEtale
