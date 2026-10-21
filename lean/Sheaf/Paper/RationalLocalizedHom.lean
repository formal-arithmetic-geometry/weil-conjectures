/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.IntegralModels
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Sheaf.Paper.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import Sheaf.Paper.ContinuousIntegralPushComparison
import Sheaf.Paper.ContinuousConstructibleIntegralModel
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.IntegralModelsOperations
import Sheaf.SixFunctors.IntegralModelsGenerators

/-! # Rational Hom groups from integral models

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-rational,
sk-prop-sp-rational-hom.md (blueprint: det-sp-rational-localized-hom).

The Hom scalar actions use the existing continuous module encoding and constant functions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.RationalLocalizedHom

/-- Fix the exact existing locally bijective criterion at the coefficient universe.
Source: Stacks 03DA (blueprint: det-sp-rational-localized-hom). -/
instance (priority := 4000) locallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective Ab.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X

/-- Constant functions give the actual scalar sections of the continuous coefficient sheaf.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
def scalarSections (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    A →+* RingCat.sectionsSubring (continuousMapRingSheaf.{0, u} X A).obj where
  toFun a := ⟨fun _ ↦ ULift.up (ContinuousMap.const _ a), fun _ ↦ rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The original continuous coefficient presheaf, retaining commutativity.
Source: blueprint coefficient convention (blueprint: det-sp-rational-localized-hom). -/
def commutativePresheaf (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj V := CommRingCat.of (ULift.{u + 1} C(V.unop.left, A))
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      (((ContinuousMap.compRightAlgHom ℤ A f.unop.left.base.hom).toRingHom).comp
        ULift.ringEquiv.toRingHom))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Pointwise constant-scalar action on module sheaves.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance continuousLinear (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    Linear A (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X A)) :=
  letI : Linear (RingCat.sectionsSubring (continuousMapRingSheaf.{0, u} X A).obj)
      (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X A)) :=
    SheafOfModules.homLinear (commutativePresheaf X A)
      (continuousMapRingSheaf.{0, u} X A).property
  { homModule := fun M N ↦ Module.compHom (M ⟶ N) (scalarSections X A)
    smul_comp := fun M N P a f g ↦ Linear.smul_comp M N P (scalarSections X A a) f g
    comp_smul := fun M N P f a g ↦ Linear.comp_smul M N P f (scalarSections X A a) g }

/-- The standard ambient localization on continuous module sheaves.
Source: Stacks 05RR (blueprint: det-sp-rational-localized-hom). -/
instance continuousDerived (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      (continuousMapRingSheaf.{0, u} X A)) := HasDerivedCategory.standard _

/-- An equivalence of abelian categories is additive.
Source: Stacks 00YV (blueprint: det-sp-rational-localized-hom). -/
instance encodingAdditive (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    (CondensedRing.continuousRingModuleEquivalence X A).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse encoding is additive as well.
Source: Stacks 00YV (blueprint: det-sp-rational-localized-hom). -/
instance encodingInverseAdditive (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    (CondensedRing.continuousRingModuleEquivalence X A).inverse.Additive := inferInstance

/-- The existing continuous module equivalence on ordinary derived categories.
Source: Stacks 05RR (blueprint: det-sp-rational-localized-hom). -/
abbrev encoding (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)) ≌
    DerivedCategory.{u + 2} (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X A)) :=
  (CondensedRing.continuousRingModuleEquivalence X A).mapDerivedCategory

/-- Derived encoding remains additive.
Source: Stacks 05RR (blueprint: det-sp-rational-localized-hom). -/
instance derivedEncodingAdditive (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    (encoding X A).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Hom scalar action transported through the actual coefficient encoding.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance homModule (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))) : Module A (K ⟶ L) :=
  AddEquiv.module A
    { (encoding X A).fullyFaithfulFunctor.homEquiv with
      map_add' := fun f g ↦ (encoding X A).functor.map_add (f := f) (g := g) }

/-- Flatness is the existing coefficient-localization theorem's final clause.
Source: blueprint proof step 1 (blueprint: det-sp-rational-localized-hom). -/
instance exactExtension (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)) :=
  (padicIntegers_invertEll X ℓ E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2

/-- Canonical shifts of scalar extension, using its exact termwise description.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance extensionShift (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.CommShift ℤ :=
  Functor.CommShift.ofIso
    (Functor.leftDerivedFunctorIsoMapDerivedCategory
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E))).symm ℤ

/-- Integral and rational ambient derived categories with the published coefficient sheaves.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev integral (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))

/-- Rational ambient category with the continuous field coefficients.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev rational (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj E.1) X))

/-- The specified rationalization is the recorded total left derived scalar extension.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev extend (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : integral X ℓ E ⥤ rational X ℓ E :=
  (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor

/-- Bounded constructibility is the recorded full subcategory predicate.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev integralConstructible (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)

/-- Bounded constructibility over the field is the same recorded predicate.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
abbrev rationalConstructible (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
  boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)

/-- Use the canonical induced norm for the finite embedded coefficient field.
Source: blueprint coefficient convention (blueprint: det-sp-rational-localized-hom). -/
instance coefficientNorm (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : NormedField E.1 :=
  PadicAlgCl.normedFieldOfAlgebra ℓ E.1

/-- The induced norm is ultrametric.
Source: the existing PadicAlgCl valuation (blueprint: det-sp-rational-localized-hom). -/
instance coefficientUltra (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : IsUltrametricDist E.1 :=
  PadicAlgCl.isUltrametricDist_ofAlgebra ℓ E.1

/-- The integer Hom action is the canonical continuous scalar action above.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance integralHomModule (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (K L : integral X ℓ E) :
    Module (PadicAlgCl.integers ℓ E.1) (K ⟶ L) :=
  homModule X (PadicAlgCl.integers ℓ E.1) K L

/-- The field Hom action is the canonical continuous scalar action above.
Source: blueprint rational Hom formula (blueprint: det-sp-rational-localized-hom). -/
instance rationalHomModule (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (K L : rational X ℓ E) :
    Module E.1 (K ⟶ L) := homModule X E.1 K L

/-- The standing chosen compactification defines the ambient compact-support composite.
Source: blueprint rational Hom groups, final clause
(blueprint: det-sp-rational-localized-hom). -/
abbrev shriek (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :=
  CondensedRing.rightDerivedLowerShriekOfCompactification Λ
    (CondensedRing.compactificationOverField f)

/-- The specified natural compact-support comparison, with the chosen Nagata compactification.
Source: blueprint rational Hom groups, final clause
(blueprint: det-sp-rational-localized-hom). -/
def shriekComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    shriek (Profinite.padicIntegersRingObj ℓ E.1) f ⋙ extend Y.left ℓ E ⟶
      extend X.left ℓ E ⋙ shriek (Profinite.continuousMapRingObj E.1) f :=
  letI := HasCompactification.of_over f
  CondensedRing.derivedLowerShriekHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left

/-- The pullback and compact-support claims, using the existing canonical natural maps.
Source: blueprint rational Hom groups, final paragraph
(blueprint: det-sp-rational-localized-hom). -/
def Comparisons (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : Prop :=
    (∀ {X Y : Over (Spec (.of k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      [IsNoetherian X.left] [IsNoetherian Y.left] (f : X ⟶ Y),
      (∀ K₀ : integral Y.left ℓ E, integralConstructible Y.left ℓ E K₀ →
        integralConstructible X.left ℓ E
          ((CondensedRing.moduleObjectDerivedPullback
            (Profinite.padicIntegersRingObj ℓ E.1) f.left).obj K₀) ∧
        rationalConstructible X.left ℓ E
          ((CondensedRing.moduleObjectDerivedPullback
            (Profinite.continuousMapRingObj E.1) f.left).obj
              ((extend Y.left ℓ E).obj K₀))) ∧
      IsIso (Functor.whiskerLeft (integralConstructible Y.left ℓ E).ι
        (CondensedRing.derivedPullIso
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left).inv) ∧
      (∀ M₀ : integral X.left ℓ E, integralConstructible X.left ℓ E M₀ →
        integralConstructible Y.left ℓ E
          ((shriek (Profinite.padicIntegersRingObj ℓ E.1) f).obj M₀) ∧
        rationalConstructible Y.left ℓ E
          ((shriek (Profinite.continuousMapRingObj E.1) f).obj
            ((extend X.left ℓ E).obj M₀))) ∧
      IsIso (Functor.whiskerLeft (integralConstructible X.left ℓ E).ι
        (shriekComparison ℓ E f)))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 100] homModule integralHomModule rationalHomModule
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  CategoryTheory.Functor.mapDerivedCategory
  CondensedRing.continuousRingModuleEquivalence upperStarFromPoint upperStar
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

private theorem hom_localized
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    (ℓ : ℕ) (F : C ⥤ D) [F.Additive]
    [F.IsLocalization (CategoryTheory.Rationalization.W (Submonoid.powers (ℓ : ℤ)) C)]
    (K L : C) :
    IsLocalizedModule (Submonoid.powers (ℓ : ℤ)) (F.mapLinearMap ℤ (X := K) (Y := L)) := by
  let S := Submonoid.powers (ℓ : ℤ)
  let Q := CategoryTheory.Rationalization.Q S C
  let e := Localization.uniq Q F (CategoryTheory.Rationalization.W S C)
  let α := Localization.compUniqFunctor Q F (CategoryTheory.Rationalization.W S C)
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  let h : (Q.obj K ⟶ Q.obj L) ≃ₗ[ℤ] (F.obj K ⟶ F.obj L) :=
    (LinearEquiv.ofBijective (e.functor.mapLinearMap ℤ)
      e.fullyFaithfulFunctor.homEquiv.bijective).trans
        (Linear.homCongr ℤ (α.app K) (α.app L))
  have hmap : h.toLinearMap.comp (Q.mapLinearMap ℤ) = F.mapLinearMap ℤ := by
    ext g
    change (α.inv.app K ≫ e.functor.map (Q.map g)) ≫ α.hom.app L = F.map g
    rw [Category.assoc, ← Functor.comp_map, α.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hm (g : K ⟶ L) : h (Q.map g) = F.map g := LinearMap.congr_fun hmap g
  constructor
  · intro n
    have hn : IsIso (F.map ((n : ℤ) • 𝟙 K)) :=
      Localization.inverts F (CategoryTheory.Rationalization.W S C) _
        (CategoryTheory.Rationalization.W_smul_id n.property K)
    have : IsIso ((n : ℤ) • 𝟙 (F.obj K)) := by
      rw [Functor.map_zsmul] at hn
      convert hn using 1
      rw [F.map_id]
    rw [Module.End.isUnit_iff]
    constructor
    · intro f g hfg
      apply (cancel_epi ((n : ℤ) • 𝟙 (F.obj K))).1
      simpa only [Linear.smul_comp, Category.id_comp,
        Module.algebraMap_end_apply] using hfg
    · intro g
      refine ⟨inv ((n : ℤ) • 𝟙 (F.obj K)) ≫ g, ?_⟩
      change (n : ℤ) • (inv ((n : ℤ) • 𝟙 (F.obj K)) ≫ g) = g
      rw [← Linear.smul_comp, ← Category.id_comp (inv _), ← Linear.smul_comp,
        Category.assoc, IsIso.hom_inv_id_assoc]
  · intro g
    obtain ⟨n, hn, f, hf⟩ :=
      CategoryTheory.Rationalization.exists_smul_eq_map (h.symm g)
    have hf' : n • h.symm g = Q.map f := by
      let m := (Localization.instLinearLocalization ℤ
        (CategoryTheory.Rationalization.W S C)).homModule (Q.obj K) (Q.obj L)
      exact (int_smul_eq_zsmul m n (h.symm g)).symm.trans hf
    refine ⟨⟨f, ⟨n, hn⟩⟩, ?_⟩
    change n • g = F.map f
    have hh := congrArg h hf'
    simpa only [map_smul, LinearEquiv.apply_symm_apply, hm] using hh
  · intro f g hfg
    change F.map f = F.map g at hfg
    have hq : Q.map f = Q.map g := h.injective (by simpa only [hm] using hfg)
    obtain ⟨n, hn, hfg'⟩ := (CategoryTheory.Rationalization.map_eq_map_iff f g).1 hq
    exact ⟨⟨n, hn⟩, hfg'⟩

private theorem encoding_map_smul (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))}
    (a : A) (f : K ⟶ L) :
    (encoding X A).functor.map (a • f) = a • (encoding X A).functor.map f := by
  exact ((encoding X A).fullyFaithfulFunctor.homEquiv).apply_symm_apply _

attribute [local irreducible] homModule

@[instance_reducible]
private def internalLinear (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A] :
    Linear A (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))) where
  homModule := homModule X A
  smul_comp K L M a f g := by
    apply (encoding X A).functor.map_injective
    simp only [Functor.map_comp, encoding_map_smul, Linear.smul_comp]
  comp_smul K L M f a g := by
    apply (encoding X A).functor.map_injective
    simp only [Functor.map_comp, encoding_map_smul, Linear.comp_smul]

@[instance_reducible]
private def restrictLinear (A B : Type*) [CommRing A] [CommRing B]
    (φ : A →+* B) (C : Type*) [Category C] [Preadditive C] [Linear B C] : Linear A C where
  homModule K L := Module.compHom (K ⟶ L) φ
  smul_comp K L M a f g := Linear.smul_comp K L M (φ a) f g
  comp_smul K L M f a g := Linear.comp_smul K L M f (φ a) g

private theorem continuousRestriction_linear (X : Scheme.{u}) (A B : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    let := restrictLinear A B φ
      (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X B))
    (SheafOfModules.restrictScalars.{u + 1} (continuousMapRingSheafMap X φ hφ)).Linear A := by
  let := restrictLinear A B φ
    (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X B))
  constructor
  intro M N f a
  ext V m
  rfl

private local instance continuousRestriction_limits (X : Scheme.{u}) (A B : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u + 1} (continuousMapRingSheafMap X φ hφ)) := by
  let U := SheafOfModules.toSheaf.{u + 1} (continuousMapRingSheaf X A)
  have : PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u + 1} (continuousMapRingSheafMap X φ hφ) ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u + 1} (continuousMapRingSheaf X B)))
  exact preservesFiniteLimits_of_reflects_of_preserves _ U

private local instance continuousRestriction_colimits (X : Scheme.{u}) (A B : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u + 1} (continuousMapRingSheafMap X φ hφ)) := by
  let U := SheafOfModules.toSheaf.{u + 1} (continuousMapRingSheaf X A)
  have : PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u + 1} (continuousMapRingSheafMap X φ hφ) ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf.{u + 1} (continuousMapRingSheaf X B)))
  exact preservesFiniteColimits_of_reflects_of_preserves _ U

private theorem continuousDerivedRestriction_linear (X : Scheme.{u}) (A B : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    let := restrictLinear A B φ
      (DerivedCategory (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X B)))
    (SheafOfModules.restrictScalars.{u + 1}
      (continuousMapRingSheafMap X φ hφ)).mapDerivedCategory.Linear A := by
  let := restrictLinear A B φ
    (DerivedCategory (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X B)))
  let := restrictLinear A B φ
    (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X B))
  let G := SheafOfModules.restrictScalars.{u + 1} (continuousMapRingSheafMap X φ hφ)
  have : G.Linear A := continuousRestriction_linear X A B φ hφ
  have : (DerivedCategory.Q : CochainComplex
      (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X B)) ℤ ⥤ DerivedCategory
        (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X B))).Linear A := by
    constructor
    intro K L f a
    change DerivedCategory.Q.map (φ a • f) = φ a • DerivedCategory.Q.map f
    exact Functor.map_smul _ _ _
  exact (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) A
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) G.mapDerivedCategory).1
      inferInstance

private theorem equivalence_exact {C D : Type*} [Category C] [Category D] (e : C ≌ D) :
    PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor :=
  ⟨inferInstance, inferInstance⟩

private def derivedSquare
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    (U : C₂ ⥤ C₁) (G : D₂ ⥤ D₁) (FA : C₁ ⥤ D₁) (FB : C₂ ⥤ D₂)
    [addU : U.Additive] [addG : G.Additive] [addFA : FA.Additive] [addFB : FB.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [limFA : PreservesFiniteLimits FA] [colimFA : PreservesFiniteColimits FA]
    [limFB : PreservesFiniteLimits FB] [colimFB : PreservesFiniteColimits FB]
    (e : U ⋙ FA ≅ FB ⋙ G) :
    U.mapDerivedCategory ⋙ FA.mapDerivedCategory ≅
      FB.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso U FA).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso FB G

private local instance continuousCoefficient_comm (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    IsCommMonObj (condensedRingObj (Profinite.continuousMapRingObj A) X) := by
  infer_instance

private local instance integralCoefficient_comm (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsCommMonObj (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) := by
  infer_instance

private local instance coefficientInclusion_isMonHom (X : Scheme.{u}) (A B : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (φ : A →+* B) (hφ : Continuous φ) :
    IsMonHom ((upperStarFromPoint X).map
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap φ hφ))) := by
  infer_instance

-- The proof transports the canonical scalar action through a derived encoding square.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- The proof transports a derived coefficient square through two equivalences.
private theorem comapDerived_linear (X : Scheme.{u}) (A B : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [TotallyDisconnectedSpace B]
    (φ : A →+* B) (hφ : Continuous φ) :
    let := internalLinear X A
    let := internalLinear X B
    let := restrictLinear A B φ
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj B) X)))
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStarFromPoint X).map
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap φ hφ)))).mapDerivedCategory.Linear A := by
  let := internalLinear X A
  let := internalLinear X B
  let := restrictLinear A B φ
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj B) X)))
  let := restrictLinear A B φ
    (DerivedCategory (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X B)))
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    ((upperStarFromPoint X).map
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap φ hφ)))
  let G := SheafOfModules.restrictScalars.{u + 1} (continuousMapRingSheafMap X φ hφ)
  let FA := (CondensedRing.continuousRingModuleEquivalence X A).functor
  let FB := (CondensedRing.continuousRingModuleEquivalence X B).functor
  have : FA.IsEquivalence :=
    Equivalence.isEquivalence_functor (CondensedRing.continuousRingModuleEquivalence X A)
  have : FB.IsEquivalence :=
    Equivalence.isEquivalence_functor (CondensedRing.continuousRingModuleEquivalence X B)
  have hFA := equivalence_exact (CondensedRing.continuousRingModuleEquivalence X A)
  have hFB := equivalence_exact (CondensedRing.continuousRingModuleEquivalence X B)
  have : PreservesFiniteLimits FA := hFA.1
  have : PreservesFiniteColimits FA := hFA.2
  have : PreservesFiniteLimits FB := hFB.1
  have : PreservesFiniteColimits FB := hFB.2
  have : FA.Additive := encodingAdditive X A
  have : FB.Additive := encodingAdditive X B
  let e := Classical.choice
    (CondensedRing.continuousRing_comap_compatibility X A B φ hφ)
  let DU : DerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj B) X)) ⥤
      DerivedCategory.{u + 1}
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj A) X)) := U.mapDerivedCategory
  let DA := (encoding X A).functor
  let DB := (encoding X B).functor
  let DG : DerivedCategory.{u + 2}
      (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X B)) ⥤
      DerivedCategory.{u + 2}
        (SheafOfModules.{u + 1} (continuousMapRingSheaf.{0, u} X A)) := G.mapDerivedCategory
  let eD : DU ⋙ DA ≅ DB ⋙ DG := derivedSquare U G FA FB e
    (addU := Functor.additive_of_preserves_binary_products _)
    (addG := Functor.additive_of_preserves_binary_products _)
    (addFA := encodingAdditive X A) (addFB := encodingAdditive X B)
    (limFA := hFA.1) (colimFA := hFA.2) (limFB := hFB.1) (colimFB := hFB.2)
  have : DA.Linear A := ⟨fun f a ↦ encoding_map_smul X A a f⟩
  have : DB.Linear A := ⟨fun f a ↦ encoding_map_smul X B (φ a) f⟩
  have : DG.Linear A := continuousDerivedRestriction_linear X A B φ hφ
  have : (DU ⋙ DA).Linear A :=
    Functor.linear_of_iso _ eD.symm
  constructor
  intro K L f a
  apply (encoding X A).functor.map_injective
  exact ((DU ⋙ DA).map_smul a f).trans (DA.map_smul a (DU.map f)).symm

@[instance_reducible]
private local instance coefficientNormedAlgebra (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : NormedAlgebra ℚ_[ℓ] E.1 where
  norm_smul_le c x := by
    change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
      ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
      PadicAlgCl.norm_extends]

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CondensedRing.derivedPushHom
  CondensedRing.lowerStar boundedConstructibleExtendScalars
  CondensedRing.boundedConstructibleLowerShriekOfCompactification

private local instance padicInclusion_isMonHom (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsMonHom (padicIntegersToPadicSubfield X ℓ E) := by infer_instance

-- The proof identifies the published inclusion with the sectionwise scalar map.
attribute [-instance] homModule integralHomModule rationalHomModule in
private theorem extend_map_smul (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (K L : integral X ℓ E)
    (a : PadicAlgCl.integers ℓ E.1) (f : K ⟶ L) :
    (extend X ℓ E).map (@SMul.smul _ _
      (integralHomModule X ℓ E K L).toSMul a f) = @SMul.smul E.1
      ((extend X ℓ E).obj K ⟶ (extend X ℓ E).obj L)
      (rationalHomModule X ℓ E _ _).toSMul (a : E.1) (extend X ℓ E |>.map f) :=
  let O := PadicAlgCl.integers ℓ E.1
  letI := internalLinear X O
  letI := internalLinear X E.1
  letI := restrictLinear O E.1 O.subtype (rational X ℓ E)
  haveI : (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicIntegersToPadicSubfield X ℓ E)).mapDerivedCategory.Linear O := by
    unfold padicIntegersToPadicSubfield padicIntegersRingObjToContinuousMapRingObj
      Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing
    exact comapDerived_linear X O E.1 O.subtype continuous_subtype_val
  haveI : (extend X ℓ E).Linear O :=
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (padicIntegersToPadicSubfield X ℓ E)).left_adjoint_linear
  (extend X ℓ E).map_smul a f

private local instance extend_additive (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : (extend X ℓ E).Additive :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
    (padicIntegersToPadicSubfield X ℓ E)).left_adjoint_additive

private local instance exactExtension_map (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)) :=
  exactExtension X ℓ E

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The two coefficient inclusions are definitionally identical for the induced norm.
private theorem pushComparison_iso (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (K : integral X ℓ E)
    (hK : integralConstructible X ℓ E K) :
    IsIso ((CondensedRing.derivedPushHom
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) f).app K) := by
  let : NormedAlgebra ℚ_[ℓ] E.1 := coefficientNormedAlgebra ℓ E
  exact @CondensedRing.integralScalarPushHom_isIso.{u} ℓ hℓ E.1
    (coefficientNorm ℓ E) (coefficientNormedAlgebra ℓ E) X Y f
    inferInstance inferInstance ⟨K, hK⟩

private theorem shriek_preserves
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [CondensedRing.IsFinitenessCoefficient ℓ Λ]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    boundedConstructible (condensedRingObj Λ Y.left) ((shriek Λ f).obj K) := by
  let c := CondensedRing.compactificationOverField f
  exact CondensedRing.boundedConstructible_rightDerivedLowerStar_obj Λ ℓ c.overG _
    (CondensedRing.boundedConstructible_openImmersionLowerShriek_obj Λ ℓ c.overI K hK)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The proof restricts the two compactification comparison functors.
private theorem comparisons (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : Comparisons ℓ k E := by
  intro X Y _ _ _ _ _ _ _ _ f
  let : NormedAlgebra ℚ_[ℓ] E.1 := coefficientNormedAlgebra ℓ E
  have : CondensedRing.IsFinitenessCoefficient ℓ
      (Profinite.continuousMapRingObj.{u} E.1) :=
    @CondensedRing.IsFinitenessCoefficient.continuous.{u} ℓ hℓ E.1
      (coefficientNorm ℓ E) (coefficientNormedAlgebra ℓ E) inferInstance
  refine ⟨?_, inferInstance, ?_, ?_⟩
  · intro K hK
    constructor
    · exact CondensedRing.boundedConstructible_leftDerivedUpperStar_obj
        (Profinite.padicIntegersRingObj ℓ E.1) ℓ f K hK
    · exact CondensedRing.boundedConstructible_leftDerivedUpperStar_obj
        (Profinite.continuousMapRingObj E.1) ℓ f _
        (boundedConstructible_derivedExtendScalars_obj Y.left ℓ E K hK)
  · intro M hM
    constructor
    · exact shriek_preserves ℓ k (Profinite.padicIntegersRingObj ℓ E.1) f M hM
    · exact shriek_preserves ℓ k (Profinite.continuousMapRingObj E.1) f _
        (boundedConstructible_derivedExtendScalars_obj X.left ℓ E M hM)
  · rw [NatTrans.isIso_iff_isIso_app]
    intro M
    let := HasCompactification.of_over f
    let c := CondensedRing.compactificationOverField f
    have hM := CondensedRing.boundedConstructible_openImmersionLowerShriek_obj
      (Profinite.padicIntegersRingObj ℓ E.1) ℓ c.overI M.obj M.property
    change IsIso ((CondensedRing.derivedLowerShriekHom
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) f.left).app M.obj)
    dsimp only [CondensedRing.derivedLowerShriekHom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Category.id_comp, Category.comp_id]
    apply IsIso.comp_isIso'
    · exact IsIso.id _
    · apply IsIso.comp_isIso'
      · exact pushComparison_iso ℓ E c.g _ hM
      · infer_instance

private theorem induced_localized
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D) [F.Additive]
    (G : P.FullSubcategory ⥤ Q.FullSubcategory) [G.Additive]
    (e : G ⋙ Q.ι ≅ P.ι ⋙ F) (ℓ : ℕ) (K L : P.FullSubcategory)
    [IsLocalizedModule (Submonoid.powers (ℓ : ℤ))
      (G.mapLinearMap ℤ (X := K) (Y := L))] :
    IsLocalizedModule (Submonoid.powers (ℓ : ℤ))
      (F.mapLinearMap ℤ (X := K.obj) (Y := L.obj)) := by
  let S := Submonoid.powers (ℓ : ℤ)
  let i : (K ⟶ L) ≃ₗ[ℤ] (K.obj ⟶ L.obj) := InducedCategory.homLinearEquiv
  let j : (G.obj K ⟶ G.obj L) ≃ₗ[ℤ] (F.obj K.obj ⟶ F.obj L.obj) :=
    InducedCategory.homLinearEquiv.trans (Linear.homCongr ℤ (e.app K) (e.app L))
  have : IsLocalizedModule S (j.toLinearMap.comp (G.mapLinearMap ℤ)) :=
    IsLocalizedModule.of_linearEquiv S (G.mapLinearMap ℤ) j
  have h := IsLocalizedModule.of_linearEquiv_right S
    (j.toLinearMap.comp (G.mapLinearMap ℤ)) i.symm
  have heq : F.mapLinearMap ℤ (X := K.obj) (Y := L.obj) =
      (j.toLinearMap.comp (G.mapLinearMap ℤ)).comp i.symm.toLinearMap := by
    apply LinearMap.ext
    intro f
    change F.map f = (e.inv.app K ≫ (G ⋙ Q.ι).map (i.symm f)) ≫ e.hom.app L
    rw [Category.assoc, e.hom.naturality, Iso.inv_hom_id_app_assoc]
    rfl
  rw [heq]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The proof compares full-subcategory Hom localization with scalar base change.
attribute [-instance] homModule integralHomModule rationalHomModule in
private theorem tensorHom_unshifted (X : Scheme.{u}) [IsNoetherian X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K L : integral X ℓ E) (hK : integralConstructible X ℓ E K)
    (hL : integralConstructible X ℓ E L) :
    let := integralHomModule X ℓ E K L
    let := rationalHomModule X ℓ E ((extend X ℓ E).obj K) ((extend X ℓ E).obj L)
    ∃ c : (E.1 ⊗[PadicAlgCl.integers ℓ E.1] (K ⟶ L)) ≃ₗ[E.1]
        ((extend X ℓ E).obj K ⟶ (extend X ℓ E).obj L),
      ∀ (e : E.1) (h : K ⟶ L), c (e ⊗ₜ h) = @SMul.smul E.1
        ((extend X ℓ E).obj K ⟶ (extend X ℓ E).obj L)
        (rationalHomModule X ℓ E _ _).toSMul e ((extend X ℓ E).map h) := by
  dsimp only
  let O := PadicAlgCl.integers ℓ E.1
  let := integralHomModule X ℓ E K L
  let := rationalHomModule X ℓ E ((extend X ℓ E).obj K) ((extend X ℓ E).obj L)
  let : Module O ((extend X ℓ E).obj K ⟶ (extend X ℓ E).obj L) :=
    Module.compHom _ O.subtype
  let f : @LinearMap O O _ _ (RingHom.id O) (K ⟶ L)
      ((extend X ℓ E).obj K ⟶ (extend X ℓ E).obj L) _ _
      (integralHomModule X ℓ E K L) (Module.compHom _ O.subtype) :=
    { toFun := (extend X ℓ E).map
      map_add' := fun f g ↦ (extend X ℓ E).map_add (f := f) (g := g)
      map_smul' := fun a h ↦ extend_map_smul X ℓ E K L a h }
  let P := integralConstructible X ℓ E
  let K' : P.FullSubcategory := ⟨K, hK⟩
  let L' : P.FullSubcategory := ⟨L, hL⟩
  let F := boundedConstructibleExtendScalars X ℓ E
  have : P.IsTriangulated := isTriangulated_boundedConstructible _
  have : F.Additive := by
    let e := boundedConstructibleExtendScalarsCompatibility X ℓ E
    have : (F ⋙ (boundedConstructible _).ι).Additive :=
      Functor.additive_of_iso e.symm
    exact Functor.additive_of_comp_faithful F (boundedConstructible _).ι
  have : ∀ n : ℤ, (shiftFunctor P.FullSubcategory n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products _
  have hF := hom_localized ℓ F K' L'
  let S := Submonoid.powers (ℓ : ℤ)
  have hG := induced_localized P _ (extend X ℓ E) F
    (boundedConstructibleExtendScalarsCompatibility X ℓ E) ℓ K' L'
  have : IsLocalizedModule S (f.restrictScalars ℤ) := by
    convert hG using 1
    all_goals first | exact Subsingleton.elim _ _ | (ext; rfl)
  have : IsLocalizedModule (Submonoid.powers (ℓ : O)) f := by
    have h := IsLocalizedModule.of_restrictScalars S f
    simpa only [S, Algebra.algebraMapSubmonoid_powers, map_natCast, Int.cast_natCast] using h
  have : IsLocalization.Away (ℓ : O) E.1 :=
    CondensedRing.continuousIntegers_isLocalization ℓ E.1
  have : IsScalarTower O E.1 ((extend X ℓ E).obj K ⟶ (extend X ℓ E).obj L) :=
    ⟨fun a b h ↦ smul_assoc (a : E.1) b h⟩
  let bc := IsLocalizedModule.isBaseChange (Submonoid.powers (ℓ : O)) E.1 f
  exact ⟨bc.equiv, fun e h ↦ bc.equiv_tmul e h⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Hom localization, with its natural map determined on all pure tensors.
Source: blueprint main-20261015, rational Hom groups
(blueprint: det-sp-rational-localized-hom).
Proof: the coefficient localization is the sequential ell-telescope, by
 det-prop-sfb-qlbar-colimit-x-invert-ell. Exact filtered colimits give its derived version.
The derived scalar adjunction identifies rational Hom with integral Hom into this telescope.
Use det-lem-int-ext-continuity with a bounded-below representative of L and common bound
for all telescope terms. This identifies Hom with its ell-localization. Since E=O_E[1/ell],
fractions identify it with tensor E. At stage n a map h is sent to ell^(-n) F(h), with the
canonical shift comparison. This proves the pure-tensor formula and E-linearity.
For essential surjectivity use det-lem-integral-models-generators: lift each generator,
and clear denominators in each arrow using the Hom result, then lift its cone. Scalar
extension preserves the cone triangles; TR3 and lem-sf-triangle-morphism-iso identify the
rational cones. Induct on the finite cone-and-shift construction, starting with zero.
For pullback use sk-def-sfb-coefficient-comparisons (Pull), together with flatness and
sk-prop-sfb-cartesian-coefficients. Integral pullback preserves constructibility by
 det-lem-integral-models-operations. Scalar extension preserves local finite presentations
and cohomological bounds. For lower shriek choose the standing Nagata compactification:
first apply integral extension by zero and proper direct-image preservation. Then apply
 det-pe-bounded-continuity-direct-image to the ell-telescope with a common lower bound.
Restriction of scalars commutes with derived proper pushforward by
 def-sfb-derived-comap-lower-star-iso and reflects quasi-isomorphisms, so (Push) is invertible.
Compose with the canonical open extension-by-zero comparison. The composite is precisely
(Shriek), and its inverse has the orientation stated in the node. Restriction of natural
transformations to the full subcategories gives naturality. -/
theorem rationalLocalizedHom
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [IsNoetherian T] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (∀ K : rational T ℓ E, rationalConstructible T ℓ E K →
      ∃ K₀ : integral T ℓ E, integralConstructible T ℓ E K₀ ∧
        Nonempty ((extend T ℓ E).obj K₀ ≅ K)) ∧
    (∀ K₀ L₀ : integral T ℓ E,
      integralConstructible T ℓ E K₀ → integralConstructible T ℓ E L₀ →
      ∀ q : ℤ, ∃ c :
        (E.1 ⊗[PadicAlgCl.integers ℓ E.1] (K₀ ⟶ L₀⟦q⟧)) ≃ₗ[E.1]
          ((extend T ℓ E).obj K₀ ⟶ ((extend T ℓ E).obj L₀)⟦q⟧),
        ∀ (e : E.1) (h : K₀ ⟶ L₀⟦q⟧),
          c (e ⊗ₜ h) = @SMul.smul E.1
            ((extend T ℓ E).obj K₀ ⟶ ((extend T ℓ E).obj L₀)⟦q⟧)
            (rationalHomModule T ℓ E _ _).toSMul e
            ((extend T ℓ E).map h ≫ ((extend T ℓ E).commShiftIso q).hom.app L₀)) ∧
    Comparisons ℓ k E := by
  constructor
  · intro K hK
    let : NormedAlgebra ℚ_[ℓ] E.1 := coefficientNormedAlgebra ℓ E
    have hp : Fact ℓ.Prime := inferInstance
    obtain ⟨M, ⟨e⟩⟩ := @CondensedRing.continuousConstructible_integral_model.{u}
      ℓ hp E.1 (coefficientNorm ℓ E) (coefficientNormedAlgebra ℓ E)
      inferInstance T inferInstance ⟨K, hK⟩
    exact ⟨M.obj, M.property, ⟨e⟩⟩
  · constructor
    · intro K L hK hL q
      let := integralHomModule T ℓ E K (L⟦q⟧)
      let := rationalHomModule T ℓ E ((extend T ℓ E).obj K)
        ((extend T ℓ E).obj (L⟦q⟧))
      let := rationalHomModule T ℓ E ((extend T ℓ E).obj K)
        (((extend T ℓ E).obj L)⟦q⟧)
      have : (integralConstructible T ℓ E).IsTriangulated :=
        isTriangulated_boundedConstructible _
      have hLq : integralConstructible T ℓ E (L⟦q⟧) :=
        (integralConstructible T ℓ E).le_shift q L hL
      have ht := tensorHom_unshifted T ℓ E K (L⟦q⟧) hK hLq
      dsimp only at ht
      obtain ⟨c, hc⟩ := ht
      let := internalLinear T E.1
      let d := Linear.homCongr E.1 (Iso.refl ((extend T ℓ E).obj K))
        (((extend T ℓ E).commShiftIso q).app L)
      refine ⟨c.trans d, fun e h ↦ ?_⟩
      change d (c (e ⊗ₜ h)) = _
      exact (congrArg d (hc e h)).trans ((d.map_smul e _).trans (by
        simp only [d, Linear.homCongr_apply, Iso.refl_inv, Category.id_comp]
        rfl))
    · exact comparisons ℓ k E

end AlgebraicGeometry.ProEtale.RationalLocalizedHom
