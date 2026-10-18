/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.RingedModelCurrying
public import Sheaf.Algebra.Homology.SliceTensorNatural
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction

/-! # Restriction transports for arbitrary sheaf coefficients

Source: Stacks Project, Tags 04IX, 08JB, 0A90.
(blueprint: lem-weil-pbc-ringed-model-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.LocalizationRHom

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- The existing further-slice restriction with its coefficient category displayed.
Source: Stacks 04IX (blueprint: lem-weil-pbc-ringed-model-restriction). -/
abbrev moduleOverMap {U V : C} (a : V ⟶ U) :
    localizationModules (R.over U) ⥤ localizationModules (R.over V) :=
  SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a

/-- Further restriction is additive, with the displayed coefficient categories.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-model-restriction).
Proof: This is the existing sectionwise additivity theorem. -/
instance moduleOverMap_additive {U V : C} (a : V ⟶ U) : (moduleOverMap R a).Additive :=
  ringedSite_overMap_additive J R a

/-- Further restriction preserves finite limits.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-model-restriction).
Proof: Apply the existing exact slice-restriction theorem. -/
instance moduleOverMap_limits {U V : C} (a : V ⟶ U) :
    Limits.PreservesFiniteLimits (moduleOverMap R a) := ringedSite_overMap_limits J R a

/-- Further restriction preserves finite colimits.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-model-restriction).
Proof: Apply the existing exact slice-restriction theorem. -/
instance moduleOverMap_colimits {U V : C} (a : V ⟶ U) :
    Limits.PreservesFiniteColimits (moduleOverMap R a) := ringedSite_overMap_colimits J R a

/-- Restrict a degree-zero coefficient using the specified coefficient sheaf isomorphism.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-model-restriction). -/
def derivedCoefficientIso {U V : C} (a : V ⟶ U)
    (S : localizationModules (R.over U)) (T : localizationModules (R.over V))
    (ξ : (moduleOverMap R a).obj S ≅ T) :
    (localizationDerivedOverMap R a).obj (derivedCoefficient R U S) ≅
      derivedCoefficient R V T := by
  letI := HasDerivedCategory.standard (localizationModules (R.over U))
  letI := HasDerivedCategory.standard (localizationModules (R.over V))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V))
  let W := moduleOverMap R a
  let singleU := HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0
  let singleV := HomologicalComplex.single (localizationModules (R.over V)) (.up ℤ) 0
  exact W.mapDerivedCategoryFactors.app (singleU.obj S) ≪≫
    (localizationQ (R.over V)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex W (.up ℤ) 0).app S ≪≫
        singleV.mapIso ξ)

/-- The natural ordinary tensor comparison for further slice restriction.
Source: Stacks 01CD, 03DH and 04IX
(blueprint: lem-weil-pbc-ringed-model-restriction). -/
def restrictionTensorIso {U V : C} (a : V ⟶ U)
    (S : localizationModules (R.over U)) (T : localizationModules (R.over V))
    (ξ : (moduleOverMap R a).obj S ≅ T) :
    letI := SheafOfModules.monoidalCategory (R.over U)
    letI := SheafOfModules.monoidalCategory (R.over V)
    tensorLeft S ⋙ moduleOverMap R a ≅ moduleOverMap R a ⋙ tensorLeft T := by
  let := SheafOfModules.monoidalCategory (R.over U)
  let := SheafOfModules.monoidalCategory (R.over V)
  let W := moduleOverMap R a
  let e (M : localizationModules (R.over U)) :
      W.obj (S ⊗ M) ≅ W.obj S ⊗ W.obj M :=
    SheafOfModules.sliceTensorIso (J := J.over V) (K := J.over U) (Over.map a)
      (R.over U) S M
  refine NatIso.ofComponents (fun M ↦ e M ≪≫ (ξ ⊗ᵢ Iso.refl (W.obj M))) ?_
  intro M M' g
  have h : W.map (S ◁ g) ≫ (e M').hom =
      (e M).hom ≫ (W.obj S ◁ W.map g) := by
    have hn := SheafOfModules.sliceTensorIso_natural
      (J := J.over V) (K := J.over U) (Over.map a) (R.over U) (𝟙 S) g
    simp only [Functor.map_id, id_tensorHom] at hn
    apply SheafOfModules.hom_ext
    ext Z x
    exact congrArg (fun q ↦ q.val.app Z x) hn
  have ht : (W.obj S ◁ W.map g) ≫ (ξ.hom ⊗ₘ 𝟙 (W.obj M')) =
      (ξ.hom ⊗ₘ 𝟙 (W.obj M)) ≫ (T ◁ W.map g) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
  simp only [Functor.comp_map, tensorLeft, curriedTensor_obj_map, Iso.trans_hom,
    tensorIso_hom, Iso.refl_hom]
  rw [← Category.assoc, h, Category.assoc, ht, Category.assoc]

/-- The ordinary complex comparison combines termwise tensor restriction with the
canonical identification of successive slices. No boundedness is required.
Source: Stacks 04IX and 08JB (blueprint: lem-weil-pbc-ringed-model-restriction). -/
def coefficientComplexIso {U V : C} (a : V ⟶ U)
    (S : localizationModules (R.over U)) (T : localizationModules (R.over V))
    (ξ : (moduleOverMap R a).obj S ≅ T) :
    coefficientComplex R U S ⋙ (moduleOverMap R a).mapHomologicalComplex (.up ℤ) ≅
      coefficientComplex R V T := by
  let := SheafOfModules.monoidalCategory (R.over U)
  let := SheafOfModules.monoidalCategory (R.over V)
  let := Classical.choice (SheafOfModules.tensorClosed (R.over U)).1
  let := Classical.choice (SheafOfModules.tensorClosed (R.over V)).1
  let W := moduleOverMap R a
  let FU := SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U
  let FV := SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) V
  let β : localizationTensorComplex (R.over U) S ⋙ W.mapHomologicalComplex (.up ℤ) ≅
      W.mapHomologicalComplex (.up ℤ) ⋙ localizationTensorComplex (R.over V) T :=
    NatIso.mapHomologicalComplex (restrictionTensorIso R a S T ξ) (.up ℤ)
  let δ : FU.mapHomologicalComplex (.up ℤ) ⋙ W.mapHomologicalComplex (.up ℤ) ≅
      FV.mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso
      (SheafOfModules.overFunctorMap
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a) (.up ℤ)
  exact Functor.isoWhiskerLeft (FU.mapHomologicalComplex (.up ℤ)) β ≪≫
    Functor.isoWhiskerRight δ (localizationTensorComplex (R.over V) T)

/-- The derived comparison is obtained from the ordinary complex comparison by the
exact restriction factorization. It is a natural isomorphism in every complex.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-model-restriction). -/
def coefficientDerivedComplexIso {U V : C} (a : V ⟶ U)
    (S : localizationModules (R.over U)) (T : localizationModules (R.over V))
    (ξ : (moduleOverMap R a).obj S ≅ T) :
    coefficientComplex R U S ⋙ localizationQ (R.over U) ⋙
      localizationDerivedOverMap R a ≅ coefficientComplex R V T ⋙
        localizationQ (R.over V) := by
  letI := HasDerivedCategory.standard (localizationModules (R.over U))
  letI := HasDerivedCategory.standard (localizationModules (R.over V))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V))
  exact Functor.isoWhiskerLeft (coefficientComplex R U S)
      (moduleOverMap R a).mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight (coefficientComplexIso R a S T ξ) (localizationQ (R.over V))

end CategoryTheory.LocalizationRHom
