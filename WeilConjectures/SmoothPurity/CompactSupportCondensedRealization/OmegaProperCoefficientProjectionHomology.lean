/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealizationSetup
import all WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealizationSetup
import all WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjectionCore
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility

/-! # Homology-level proper coefficient projection

The proper coefficient comparison is invertible on every homology object.
(blueprint: lem-pur-omega-proper-coefficient-projection-homology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions _root_.instCategoryDerivedCategory

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.extendScalars
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] WeilConjectures.integralCoefficientCommRingSheaf

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj

attribute [local instance] fieldSheafAbelian fieldSheafGrothendieck
  fieldSheafBigColimits fieldSheafCoequalizers fieldSheafMonoidalPreadditive
  fieldModuleAbelian fieldModuleGrothendieck fieldModuleKInjectiveResolutions
  fieldModuleDerivedCategory fieldModuleColimits fieldTensorColimits fieldTensorColimitsRight
  fieldGradedTensor fieldGradedFour fieldGradedLeft fieldGradedRight fieldExtendScalarsKFlat

namespace WeilConjectures.CompactSupportCondensedRealization

private abbrev pulledCoefficientMonObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (W : Scheme.{u}) : MonObj (condensedRingObj Λ W) :=
  Functor.monObjObj (F := upperStarFromPoint W) Λ

attribute [local instance] pulledCoefficientMonObj

private theorem coefficientIso_push_isIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (b : Λ ⟶ Λ') [IsMonHom b] [IsIso b] [FlatCoefficientMap b]
    {X Y : Scheme.{u}} (g : X ⟶ Y) : IsIso (condensedPushScalar b g) := by
  have he (W : Scheme.{u}) :
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (coefficientMap b W)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (coefficientMap b W)).isEquivalence_functor
  have he' (W : Scheme.{u}) :
      (Mod.comap (D := Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (coefficientMap b W)).mapDerivedCategory.IsEquivalence := by
    have := he W
    infer_instance
  have := he' X
  have := he' Y
  have hx := (condensedScalarAdjunction b X).isEquivalence_left_of_isEquivalence_right
  have hy := (condensedScalarAdjunction b Y).isEquivalence_left_of_isEquivalence_right
  have := hx
  have := hy
  unfold condensedPushScalar Adjunction.pushHomOfComapIso
  dsimp only [Equiv.symm, mateEquiv, Equiv.coe_fn_mk]
  infer_instance

/--
The proper coefficient comparison induces an isomorphism on every homology object
of a bounded constructible input.

Source: Bhatt--Scholze 6.8.14(1)--(2), 6.8.15; compact-support realization proof
Step 13 (blueprint: lem-pur-omega-proper-coefficient-projection-homology).

Proof: identify the finite image of the coefficient embedding, express the closure
coefficient as the filtered colimit of finite intermediate fields, and choose a common
lower bound for the coefficient-complex presentation. At each finite stage the
restricted coefficient module is finite free, so the proper coefficient transpose is
a finite direct-sum comparison and is invertible. Bounded-below qcqs pushforward
continuity identifies the homology of the colimit comparison with the colimit of
these finite-stage isomorphisms. Exact scalar extension and filtered colimits identify
that colimit with the displayed homology map of `condensedPushScalar`; hence this map
is invertible in every degree. -/
theorem omegaProperCoefficientProjection_homology_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    {X Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    [TopologicalSpace.NoetherianSpace Y] (g : X ⟶ Y) [IsProper g]
    (K : CondensedERealization.Constructible E X) :
    ∀ n : ℤ, IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((condensedPushScalar (omegaMap l E a) g).app K.obj)) := by
  classical
  let F : PadicAlgCl.FiniteIntermediateField l :=
    ⟨a.fieldRange, Module.Finite.equiv a.equivFieldRange.toLinearEquiv⟩
  let H := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let e := coefficientRangeRingIso l E a
  let b : Profinite.continuousCoefficientRingObj E ⟶
      Profinite.continuousMapRingObj a.fieldRange := H.map e.hom
  let c := Profinite.padicSubfieldRingObjToPadicAlgCl l F
  have : IsMonHom b := by dsimp only [b, H]; infer_instance
  have : IsIso b := by dsimp only [b]; infer_instance
  have : FlatCoefficientMap b := fun W ↦
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv (coefficientMap b W)).symm
  have : FlatCoefficientMap c := fun W ↦
    CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
      l F (X := W)
  have hab : omegaMap l E a = b ≫ c := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro f
    rfl
  have : FlatCoefficientMap (b ≫ c) := by
    simpa only [← hab] using (inferInstance : FlatCoefficientMap (omegaMap l E a))
  obtain ⟨N, hN⟩ := K.property.1.1
  have : K.obj.IsGE N := hN
  let G := Mod.extendScalars (coefficientMap b X)
  have : (G.mapDerivedCategory.obj K.obj).IsGE N := G.isGE_mapDerivedCategory_obj K.obj N
  have : ((condensedScalar b X).obj K.obj).IsGE N :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (G.leftDerivedFunctorIsoMapDerivedCategory.app K.obj).symm N
  have hc : IsIso ((condensedPushScalar c g).app ((condensedScalar b X).obj K.obj)) :=
    CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE
      l g F ((condensedScalar b X).obj K.obj) N
  have := hc
  have := coefficientIso_push_isIso b g
  have hp := scalarPush_comp b c g K.obj
  have hi : IsIso ((condensedScalarComp b c Y).hom.app
      ((CondensedRing.lowerStar _ g).rightDerivedFunctor.obj K.obj) ≫
        (condensedPushScalar (b ≫ c) g).app K.obj) := by
    rw [← hp]
    infer_instance
  have := hi
  have : IsIso ((condensedPushScalar (b ≫ c) g).app K.obj) :=
    IsIso.of_isIso_comp_left ((condensedScalarComp b c Y).hom.app
      ((CondensedRing.lowerStar _ g).rightDerivedFunctor.obj K.obj)) _
  have transport (d : Profinite.continuousCoefficientRingObj E ⟶
      Profinite.padicAlgClRingObj l) [IsMonHom d] [FlatCoefficientMap d]
      (hd : d = b ≫ c) : ∀ n : ℤ,
      IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((condensedPushScalar d g).app K.obj)) := by
    subst d
    intro n
    infer_instance
  exact transport (omegaMap l E a) hab

end WeilConjectures.CompactSupportCondensedRealization
