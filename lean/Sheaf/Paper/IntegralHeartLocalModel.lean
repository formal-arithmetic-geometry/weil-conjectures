/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

import Sheaf.Paper.AdicStratifiedPerfect
import Sheaf.Paper.IntegralCohomologicalAdicCriterion
import Sheaf.Paper.IntegralModels
import Sheaf.SixFunctors.ProEtale.DerivedCompletion
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.CartesianCoefficients
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Local models for the integral constructible heart

Source: blueprint main-20261015, integral-heart-local-model, clauses (1)--(3);
Stacks Project, Tags 099I, 09C7, 09C4, 0990, 099Q and 099Y
(blueprint: det-lem-int-integral-heart-local-model).

The coefficient ring is exactly the sibling integral-heart theorem's ring. Scalar
modules are lifted copies of the integers in the canonical small presentation of E.
Their realization is sheafified extension of scalars along constant functions,
followed by the existing equivalence with internal module objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The coefficient DVR, lifted only to the sheaf-value universe.
Source: integral-heart coefficient setup (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartScalars (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :=
  ULift.{u + 1} (SmallAdicCompletion.Coefficients.integers ℓ E)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- The actual section ring sheaf of the condensed integral ring.
Source: pulled-back coefficient setup (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartPointRing :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E))

/-- A scalar as its constant continuous function, in the reconstructed section ring.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartScalarSection (S : Profinite.{u}ᵒᵖ)
    (a : integralHeartScalars.{u} ℓ E) :
    (sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).obj.obj S :=
  ULift.up (ContinuousMap.const S.unop a.down)

/-- The constant scalar one is the unit of the reconstructed section ring.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model).
Proof: the internal unit of continuous functions is the constant function one.
Evaluating its section-ring reconstruction gives the same constant function. -/
theorem integralHeartScalarSection_one (S : Profinite.{u}ᵒᵖ) :
    integralHeartScalarSection.{u} ℓ E S 1 = 1 := by
  let : MonObj (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E).obj :=
    (Profinite.continuousMapRingSheaf
      (SmallAdicCompletion.Coefficients.integers ℓ E)).obj.monObjCompForget₂
  have h := congr_app (Sheaf.ε_comp_map_one
    (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)) S
  have hh := (ConcreteCategory.congr_hom h (ULift.up (1 : ℤ))).symm
  convert! hh using 1
  simp only [integralHeartScalarSection, Functor.one_compForget₂_app,
    Monoidal.tensorUnit_obj, ObjectProperty.ι_obj]
  change (1 : ULift.{u + 1} C(S.unop,
    SmallAdicCompletion.Coefficients.integers ℓ E)) = ((1 : ℤ) :
      ULift.{u + 1} C(S.unop, SmallAdicCompletion.Coefficients.integers ℓ E))
  simp only [Int.cast_one]

/-- Constant continuous functions preserve multiplication in the reconstructed ring.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model).
Proof: the reconstructed internal multiplication evaluated on a pure tensor is the
original pointwise multiplication of continuous functions. The two constant functions
multiply to the constant function on the scalar product. -/
theorem integralHeartScalarSection_mul (S : Profinite.{u}ᵒᵖ)
    (a b : integralHeartScalars.{u} ℓ E) :
    integralHeartScalarSection.{u} ℓ E S (a * b) =
      integralHeartScalarSection.{u} ℓ E S a * integralHeartScalarSection.{u} ℓ E S b := by
  let : MonObj (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E).obj :=
    (Profinite.continuousMapRingSheaf
      (SmallAdicCompletion.Coefficients.integers ℓ E)).obj.monObjCompForget₂
  have h := congr_app (Sheaf.μ_comp_map_mul
    (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)) S
  exact (ConcreteCategory.congr_hom h
    (TensorProduct.tmul ℤ (integralHeartScalarSection.{u} ℓ E S a)
      (integralHeartScalarSection.{u} ℓ E S b))).symm

/-- Constant scalar functions in every profinite section ring.
Source: the scalar-extension model in clause (1)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartConstantMap :
    (Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (integralHeartScalars.{u} ℓ E)) ⟶
      (sectionRingSheaf (coherentTopology Profinite.{u})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E)).obj where
  app S := @CommRingCat.ofHom
    (integralHeartScalars.{u} ℓ E)
    ((sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)).obj.obj S) inferInstance
    (CommRingCat.commRing _)
    { toFun := integralHeartScalarSection.{u} ℓ E S
      map_one' := integralHeartScalarSection_one.{u} ℓ E S
      map_mul' := integralHeartScalarSection_mul.{u} ℓ E S
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

/-- Constant scalar module presheaves on the point, with identity restrictions.
Source: the scalar-extension model in clause (1)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartConstantPresheaf : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤
    PresheafOfModules.{u + 1}
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (integralHeartScalars.{u} ℓ E))) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

/-- Additivity of constant module presheaves.
Source: clause (1), constant realization (blueprint: det-lem-int-integral-heart-local-model).
Proof: evaluate a sum of morphisms at each profinite object; its value is the original
sum of linear maps, so additivity is pointwise. -/
theorem integralHeartConstantPresheaf_additive :
    (integralHeartConstantPresheaf.{u} ℓ E).Additive := by
  refine ⟨?_⟩
  intro X Y f g
  rfl

attribute [instance] integralHeartConstantPresheaf_additive

/-- The constant scalar ring sheaf.
Source: the scalar model in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartConstantRing :=
  (constantSheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).obj
    (CommRingCat.of (integralHeartScalars.{u} ℓ E))

/-- The sheafification unit for the constant scalar ring, forgetting commutativity.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartConstantUnit :=
  Functor.whiskerRight
    (toSheafify (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj
        (CommRingCat.of (integralHeartScalars.{u} ℓ E))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

/-- The constant ring sheafification unit is locally injective after forgetting
commutativity. Source: constant sheafification, Stacks 03DA
(blueprint: det-lem-int-integral-heart-local-model).
Proof: the underlying functions and equalizer sieves are unchanged by forgetting
commutativity, and the original sheafification unit is locally injective. -/
theorem integralHeartConstantUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u})
      (integralHeartConstantUnit.{u} ℓ E) := by
  constructor
  intro S x y h
  exact Presheaf.equalizerSieve_mem (coherentTopology Profinite.{u})
    (toSheafify (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj
        (CommRingCat.of (integralHeartScalars.{u} ℓ E)))) x y h

/-- The constant ring sheafification unit is locally surjective after forgetting
commutativity. Source: constant sheafification, Stacks 03DA
(blueprint: det-lem-int-integral-heart-local-model).
Proof: the underlying functions and image sieves are unchanged by forgetting
commutativity, and the original sheafification unit is locally surjective. -/
theorem integralHeartConstantUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (integralHeartConstantUnit.{u} ℓ E) := by
  constructor
  intro S x
  exact Presheaf.imageSieve_mem (coherentTopology Profinite.{u})
    (toSheafify (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj
        (CommRingCat.of (integralHeartScalars.{u} ℓ E)))) x

attribute [instance] integralHeartConstantUnit_isLocallyInjective
  integralHeartConstantUnit_isLocallySurjective

/-- The canonical ring map from constant scalars to continuous coefficients.
Source: scalar realization in clauses (1)--(2)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartScalarMap : integralHeartConstantRing.{u} ℓ E ⟶
    sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) :=
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) CommRingCat.{u + 1}).homEquiv
    _ _).symm (integralHeartConstantMap.{u} ℓ E)

/-- Modules over the constant scalar ring on the point.
Source: scalar realization in clause (1) (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartConstantModules :=
  SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E))

/-- The map laws of the existing canonical sectionwise scalar-extension construction.
Source: sheaf tensor, Stacks 03EK (blueprint: det-lem-int-integral-heart-local-model).
Proof: before sheafification all maps are id tensor f. Tensor functoriality gives
identity and composition on pure tensors. Sheafification preserves both equations. -/
theorem integralHeartExtension_laws :
    (∀ M : integralHeartConstantModules.{u} ℓ E,
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M (𝟙 M) = 𝟙 _) ∧
    (∀ (M N P : integralHeartConstantModules.{u} ℓ E) (f : M ⟶ N) (g : N ⟶ P),
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M (f ≫ g) =
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M f ≫
      SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) N g) := by
  let F := PresheafOfModules.sheafification.{u + 1}
    (R := integralHeartPointRing.{u} ℓ E) (𝟙 _)
  constructor
  · intro M
    change F.map _ = 𝟙 _
    trans F.map (𝟙 _)
    · congr 1
      ext S : 1
      change (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        ((integralHeartScalarMap.{u} ℓ E).hom.app S).hom).map (𝟙 _) = 𝟙 _
      exact CategoryTheory.Functor.map_id _ _
    · exact F.map_id _
  · intro M N P f g
    change F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp]
    congr 1
    ext S : 1
    change (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      ((integralHeartScalarMap.{u} ℓ E).hom.app S).hom).map (f.val.app S ≫ g.val.app S) =
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        ((integralHeartScalarMap.{u} ℓ E).hom.app S).hom).map (f.val.app S) ≫
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          ((integralHeartScalarMap.{u} ℓ E).hom.app S).hom).map (g.val.app S)
    exact CategoryTheory.Functor.map_comp _ _ _

/-- Actual completed scalar extension, sheafifying the sectionwise tensor product.
Source: scalar realization in clauses (1)--(2)
(blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartExtension :
    SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E)) ⥤
    SheafOfModules.{u + 1} (integralHeartPointRing.{u} ℓ E) where
  obj M := SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (integralHeartScalarMap.{u} ℓ E) M
  map {M _N} f := SheafOfModules.changeOfRingsHomOfUniverses.{u, u + 1, u + 1, u + 1}
    (integralHeartScalarMap.{u} ℓ E) M f
  map_id M := (integralHeartExtension_laws.{u} ℓ E).1 M
  map_comp f g := (integralHeartExtension_laws.{u} ℓ E).2 _ _ _ f g

/-- The canonical completed scalar-module realization on the point. It first forms
constant module sheaves, then extends scalars along constant functions, and finally
uses the existing internal-module equivalence. No realization functor is an input.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartPointRealization : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤
    CategoryTheory.Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) :=
  integralHeartConstantPresheaf.{u} ℓ E ⋙
    PresheafOfModules.sheafification
      (R := (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralHeartConstantRing.{u} ℓ E))
      (integralHeartConstantUnit.{u} ℓ E) ⋙
    integralHeartExtension.{u} ℓ E ⋙
    (sectionModuleEquivalence (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).inverse

/-- Additivity of completed scalar realization.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model).
Proof: constant presheaves preserve addition pointwise. Scalar extension and
sheafification are additive; the inverse of an additive equivalence is additive. -/
theorem integralHeartPointRealization_additive :
    (integralHeartPointRealization.{u} ℓ E).Additive := by
  have : (PresheafOfModules.sheafification.{u + 1}
      (R := (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (integralHeartConstantRing.{u} ℓ E))
      (integralHeartConstantUnit.{u} ℓ E)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (R := (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (integralHeartConstantRing.{u} ℓ E))
      (integralHeartConstantUnit.{u} ℓ E)).left_adjoint_additive
  have : (integralHeartExtension.{u} ℓ E).Additive := by
    let F := PresheafOfModules.sheafification.{u + 1}
      (R := integralHeartPointRing.{u} ℓ E) (𝟙 _)
    have : F.Additive :=
      (PresheafOfModules.sheafificationAdjunction.{u + 1}
        (R := integralHeartPointRing.{u} ℓ E) (𝟙 _)).left_adjoint_additive
    constructor
    intro M N f g
    change F.map _ = F.map _ + F.map _
    rw [← F.map_add]
    congr 1
    ext S : 1
    let G := ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      ((integralHeartScalarMap.{u} ℓ E).hom.app S).hom
    have : G.Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        ((integralHeartScalarMap.{u} ℓ E).hom.app S).hom).left_adjoint_additive
    exact G.map_add
  have : (sectionModuleEquivalence (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).functor.Additive := by
    constructor
    intro M N f g
    ext S m
    rfl
  let : (sectionModuleEquivalence (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)).inverse.Additive :=
    @Equivalence.inverse_additive _ _ _ _ _ _
      (sectionModuleEquivalence (coherentTopology Profinite.{u})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E))
      (by infer_instance)
  unfold integralHeartPointRealization
  infer_instance

attribute [instance] integralHeartPointRealization_additive

/-- Scalar-module realization on a scheme by the published inverse image from the point.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartRealization (X : Scheme.{u}) :=
  integralHeartPointRealization.{u} ℓ E ⋙
    (upperStarFromPoint X).mapMod (SmallAdicCompletion.Coefficients.integerRing ℓ E)

/-- Additivity of realization on the scheme.
Source: clauses (1)--(2) (blueprint: det-lem-int-integral-heart-local-model).
Proof: point realization is additive and inverse image is additive; compose these
properties. This is only the structure needed to map cochain complexes. -/
theorem integralHeartRealization_additive (X : Scheme.{u}) :
    (integralHeartRealization.{u} ℓ E X).Additive := by
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive :=
    CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _
  have : ((upperStarFromPoint X).mapMod
      (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)).Additive := by
    constructor
    intro M N f g
    apply CategoryTheory.Mod.hom_ext
    exact (upperStarFromPoint X).map_add
  unfold integralHeartRealization
  infer_instance

attribute [instance] integralHeartRealization_additive

/-- The ordinary unbounded category with exactly the integral-heart coefficient ring.
Source: the standing setup (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartDerivedCategory (X : Scheme.{u}) :=
  DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) X))

/-- The q-th cohomology sheaf in degree zero.
Source: clause (2) (blueprint: det-lem-int-integral-heart-local-model). -/
abbrev integralHeartCohomology (X : Scheme.{u})
    (K : integralHeartDerivedCategory.{u} ℓ E X) (q : ℤ) :=
  (DerivedCategory.singleFunctor _ 0).obj ((DerivedCategory.homologyFunctor _ q).obj K)

-- Step 1: use the identity cover and the zero finitely presented condensed module.
private lemma integralHeartFiniteConstantLocalModel_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

-- The one-stratum stratification works also when the scheme is empty.
private lemma integralHeartFiniteConstantStratified_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsFiniteConstantStratified Λ X M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun a ↦ integralHeartFiniteConstantLocalModel_of_isZero Λ _ _
    ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hM)⟩

private lemma integralHeartConstructible_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact integralHeartFiniteConstantStratified_of_isZero Λ X M hM
  · exact fun U _ ↦ integralHeartFiniteConstantStratified_of_isZero Λ _ _
      ((CondensedRing.upperStar Λ U.ι).map_isZero hM)

private lemma integralHeartConstructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hs (T : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
      (e : A ≅ B) (hA : IsFiniteConstantStratified Λ T A) :
      IsFiniteConstantStratified Λ T B := by
    obtain ⟨S, hS⟩ := hA
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨𝒰, h𝒰⟩ := hS a
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (𝒰.f i)).mapIso
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e)).symm ≪≫ eP⟩⟩
  classical
  unfold IsConstantModelConstructible at *
  split_ifs at * with h
  · exact hs X e hM
  · exact fun U hU ↦ hs U.toScheme ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private theorem integralHeartCohomology_constructible (X : Scheme.{u})
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (hK : constantModelBoundedConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X K) (q : ℤ) :
    constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
      (integralHeartCohomology.{u} ℓ E X K q) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact integralHeartConstructible_of_iso
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm (hK.2 q)
  · apply integralHeartConstructible_of_isZero
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn

open scoped ZeroObject in
private theorem integralHeartTruncations_constructible (X : Scheme.{u})
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (hK : constantModelBoundedConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X K) (q : ℤ) :
    constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
        ((DerivedCategory.TStructure.t.truncLE q).obj K) ∧
      constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
        ((DerivedCategory.TStructure.t.truncGE q).obj K) := by
  let P : ObjectProperty (SmallAdicCompletion.Modules ℓ E X) :=
    IsConstantModelConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
  have : P.IsClosedUnderIsomorphisms := ⟨fun e hM ↦
    integralHeartConstructible_of_iso _ X e hM⟩
  have : P.ContainsZero :=
    ⟨0, isZero_zero _, integralHeartConstructible_of_isZero
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X _ (isZero_zero _)⟩
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  constructor
  · refine ⟨⟨⟨a, inferInstance⟩, ⟨q, inferInstance⟩⟩, ?_⟩
    exact DerivedCategory.homologyProperty_truncLE hc q
  · refine ⟨⟨⟨q, inferInstance⟩, ⟨b, inferInstance⟩⟩, ?_⟩
    exact DerivedCategory.homologyProperty_truncGE hc q


private theorem integralHeartConstant_exact :
    PreservesFiniteLimits (integralHeartConstantPresheaf.{u} ℓ E ⋙
      PresheafOfModules.sheafification
        (R := (sheafCompose (coherentTopology Profinite.{u})
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (integralHeartConstantRing.{u} ℓ E))
        (integralHeartConstantUnit.{u} ℓ E)) ∧
    PreservesFiniteColimits (integralHeartConstantPresheaf.{u} ℓ E ⋙
      PresheafOfModules.sheafification
        (R := (sheafCompose (coherentTopology Profinite.{u})
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (integralHeartConstantRing.{u} ℓ E))
        (integralHeartConstantUnit.{u} ℓ E)) := by
  let P := integralHeartConstantPresheaf.{u} ℓ E
  have : PreservesFiniteLimits P := by
    constructor
    intro J _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro J _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

private theorem scalar_pid (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsPrincipalIdealRing (integralHeartScalars.{u} l E) := by
  have h := (Padic.extension_integers_dvr l (SmallAdicCompletion.Coefficients.field l E)
    (Padic.coefficientExtensionAbsoluteValue l (SmallAdicCompletion.Coefficients.field l E))
    (spectralNorm_extends (K := Padic l)
      (L := SmallAdicCompletion.Coefficients.field l E))).choose_spec.choose_spec
  let : IsPrincipalIdealRing (SmallAdicCompletion.Coefficients.integers l E) :=
    h.2.2.2.2.2.2.2.2.1
  exact IsPrincipalIdealRing.of_surjective ULift.ringEquiv.symm
    ULift.ringEquiv.symm.surjective

-- The complete local coefficient hypotheses for the adic stratified-perfect theorem.
private theorem integralHeartScalarProperties (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    IsNoetherianRing (integralHeartScalars.{u} l E) ∧
      ∃ I : Ideal (integralHeartScalars.{u} l E),
        (I.IsMaximal ∧ ∀ J : Ideal (integralHeartScalars.{u} l E), J.IsMaximal → J = I) ∧
          IsAdicComplete I (integralHeartScalars.{u} l E) := by
  let F := SmallAdicCompletion.Coefficients.field l E
  let R := SmallAdicCompletion.Coefficients.integers l E
  let S := integralHeartScalars.{u} l E
  let m := Padic.coefficientExtensionMaximalIdeal l F
  let e : R ≃+* S := ULift.ringEquiv.symm
  have h := (Padic.extension_integers_dvr l F
    (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := Padic l) (L := F))).choose_spec.choose_spec
  have hm : m.IsMaximal := h.2.2.2.2.1
  have huniq : ∀ J : Ideal R, J.IsMaximal → J = m := h.2.2.2.2.2.1
  let : IsPrincipalIdealRing R := h.2.2.2.2.2.2.2.2.1
  have hNoeth : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  have hcomplete : IsAdicComplete m R :=
    (@Padic.finite_module_adic_complete_and_hom.{0, 0, 0}
      l inferInstance F inferInstance inferInstance inferInstance).1 R |>.1
  refine ⟨hNoeth, m.map e, ⟨hm.map_bijective e e.bijective, ?_⟩,
    (IsAdicComplete.congr_ringEquiv m e).mpr hcomplete⟩
  intro J hJ
  have heq : J.comap e = m := huniq _ (hJ.comap_bijective e e.bijective)
  have hh := congrArg (Ideal.map e) heq
  rwa [Ideal.map_comap_of_surjective e e.surjective] at hh

private theorem finite_homology {R : Type u} [CommRing R] [IsNoetherianRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (q : ℤ)
    [Module.Finite R (P.X q)] : Module.Finite R (P.homology q) := by
  have : Module.Finite R (P.cycles q) :=
    Module.Finite.of_injective (P.iCycles q).hom (ModuleCat.mono_iff_injective _ |>.mp
      inferInstance)
  exact Module.Finite.of_surjective (P.homologyπ q).hom
    (ModuleCat.epi_iff_surjective _ |>.mp inferInstance)

private theorem projective_free {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Projective R M] : Module.Free R M := by
  infer_instance

/-- Finite free models and all their cohomology models on the same strata and charts.
The differential matrices are over the scalar DVR since P is a scalar cochain complex.
Source: clauses (1) and (2) (blueprint: det-lem-int-integral-heart-local-model). -/
def integralHeartFiniteFreeLocalModel (X : Scheme.{u})
    (K : integralHeartDerivedCategory.{u} ℓ E X) : Prop :=
  ∃ s : Scheme.FiniteLocallyClosedStratification X,
    (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
    ∀ a : Fin s.n, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
      ∀ i : 𝒰.I₀,
        ∃ (P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ)
          (b c : ℤ),
          P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
          (∀ q : ℤ, Module.Free (integralHeartScalars.{u} ℓ E) (P.X q) ∧
            Module.Finite (integralHeartScalars.{u} ℓ E) (P.X q)) ∧
          Nonempty (((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
              (𝒰.f i ≫ s.immersion a)).mapDerivedCategory).obj K ≅
            DerivedCategory.Q.obj
              (((integralHeartRealization.{u} ℓ E (𝒰.X i)).mapHomologicalComplex (.up ℤ)).obj P)) ∧
          (∀ q : ℤ,
            Module.Finite (integralHeartScalars.{u} ℓ E) (P.homology q) ∧
            Nonempty ((CondensedRing.upperStar (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                (𝒰.f i ≫ s.immersion a)).obj
                  ((DerivedCategory.homologyFunctor _ q).obj K) ≅
              (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj (P.homology q)))

private theorem integralHeartFiniteFreeLocalModel_of_projective (X : Scheme.{u})
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (hExact : ∀ Y : Scheme.{u},
      PreservesFiniteLimits (integralHeartRealization.{u} ℓ E Y) ∧
      PreservesFiniteColimits (integralHeartRealization.{u} ℓ E Y))
    (hModels : ∃ s : Scheme.FiniteLocallyClosedStratification X,
      (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
      ∀ a : Fin s.n, ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
        ∀ i : 𝒰.I₀,
          ∃ (P : CochainComplex (ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E)) ℤ)
            (b c : ℤ),
            P.IsStrictlyGE b ∧ P.IsStrictlyLE c ∧
            (∀ q : ℤ, Module.Projective (integralHeartScalars.{u} ℓ E) (P.X q) ∧
              Module.Finite (integralHeartScalars.{u} ℓ E) (P.X q)) ∧
            Nonempty (((CondensedRing.upperStar
                (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                (𝒰.f i ≫ s.immersion a)).mapDerivedCategory).obj K ≅
              DerivedCategory.Q.obj
                (((integralHeartRealization.{u} ℓ E (𝒰.X i)).mapHomologicalComplex
                  (.up ℤ)).obj P))) :
    integralHeartFiniteFreeLocalModel.{u} ℓ E X K := by
  let : IsPrincipalIdealRing (integralHeartScalars.{u} ℓ E) := scalar_pid ℓ E
  let : IsNoetherianRing (integralHeartScalars.{u} ℓ E) :=
    (integralHeartScalarProperties ℓ E).1
  let : IsDomain (integralHeartScalars.{u} ℓ E) :=
    ULift.ringEquiv.isDomain
  obtain ⟨s, hs, hModels⟩ := hModels
  refine ⟨s, hs, fun a ↦ ?_⟩
  obtain ⟨𝒰, hModels⟩ := hModels a
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, b, c, hb, hc, hP, ⟨e⟩⟩ := hModels i
  refine ⟨P, b, c, hb, hc, ?_, ⟨e⟩, fun q ↦ ?_⟩
  · intro q
    have := (hP q).1
    have := (hP q).2
    exact ⟨projective_free (P.X q), inferInstance⟩
  · have := (hP q).2
    refine ⟨finite_homology P q, ⟨?_⟩⟩
    let F := integralHeartRealization.{u} ℓ E (𝒰.X i)
    have : PreservesFiniteLimits F := (hExact _).1
    have : PreservesFiniteColimits F := (hExact _).2
    exact ((CondensedRing.upperStar
      (SmallAdicCompletion.Coefficients.integerRing ℓ E)
      (𝒰.f i ≫ s.immersion a)).mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ q).app _ ≪≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) q).app P

/-- Integral constructible complexes have finite free local models, their cohomology is
complete and constructible, and both good truncations remain constructible.
Source: blueprint main-20261015, integral-heart-local-model, clauses (1)--(3), and
Stacks Tags 099I, 09C7, 09C4, 0990, 099Q, 099Y
(blueprint: det-lem-int-integral-heart-local-model).

Proof: (1) The coefficient DVR is a local PID and hence Noetherian. Completeness
follows by lifting a compatible sequence of residues and using the absolute-value
bound by successive powers of the uniformizer. The integral cohomological adic
criterion identifies the hypothesis with local derived completeness and finite-Tor
constructible residue reduction. The stratified-perfect theorem supplies finite
projective scalar complexes on a finite constructible stratification and its covers.
Each finite projective module embeds in a finite free module, is torsion-free, and
is free over the DVR; bases give the scalar differential matrices.
(2) Each H^q(K)[0] is bounded constructible by the cohomological definition, so the
integral-models criterion gives derived completeness in the canonical reduction-limit
sense. On exactly the original charts, exact cartesian inverse image and flat completed
scalar extension commute with kernels, images and cohomology. Thus the model is the
realization of H^q(P), which is finite since the DVR is Noetherian.
(3) Good truncations retain the original cohomology in the retained degrees and zero
elsewhere. Both lists are bounded and constructible, which is exactly the same
constant-model bounded-constructible predicate as in the hypothesis. -/
theorem integralHeartLocalModel
    (k₀ : Type u) [Field k₀] (p : ℕ) [CharP k₀ p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : p ≠ ℓ)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k₀))]
    [IsSeparated (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
    [QuasiCompact (X ↘ Spec (.of k₀))]
    (K : integralHeartDerivedCategory.{u} ℓ E X)
    (hK : constantModelBoundedConstructible
      (SmallAdicCompletion.Coefficients.integerRing ℓ E) X K) :
    integralHeartFiniteFreeLocalModel.{u} ℓ E X K ∧
      (∀ q : ℤ,
        SmallAdicCompletion.IsDerivedComplete ℓ E X (integralHeartCohomology.{u} ℓ E X K q) ∧
        constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
          (integralHeartCohomology.{u} ℓ E X K q)) ∧
      (∀ q : ℤ,
        constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
          ((DerivedCategory.TStructure.t.truncLE q).obj K) ∧
        constantModelBoundedConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X
          ((DerivedCategory.TStructure.t.truncGE q).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale
