/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
public import WeilConjectures.AlgebraicGeometry.FiniteOpenClosedRecollement
public import WeilConjectures.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.OpenTensorNormalizationData
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import all WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenClosed
import all WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
import all WeilConjectures.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionUnitShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenClosedTriangle
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import all WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated

/-! # Constructible restriction of the finite support-kernel adjoint

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-localization-all-stages.proof.md,
"Finite stage" and "Vanishing"; Stacks Tags 09AH, 09BM, 070I and 07A6
(blueprint: lem-sf-finite-kernel-constructible-localization).

The underived support functor is the published inverse image of the kernel of
N → j_*j* N. Its counit is normalized by the kernel inclusion before derivation.
All categories below are intrinsic constant-ring module categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The positive finite coefficient level; n+1 ranges over every n≥1.
Source: blueprint finite stage
(blueprint: lem-sf-finite-kernel-constructible-localization). -/
abbrev sfKernelCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  Padic.coefficientExtensionRing l E (n + 1)

/-- The recorded positive-level finiteness proof, with no extra hypothesis.
Source: blueprint finite stage
(blueprint: lem-sf-finite-kernel-constructible-localization). -/
instance sfKernelCoefficient_finite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (sfKernelCoefficient l E n) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- Constant scalar multiplication on intrinsic derived morphisms, through the
published constant-section realization equivalence. The counit conjugations identify
its underlying objects with the given objects; this is the usual A-module action,
including on morphisms introduced by localization.
Source: blueprint finite-stage coefficient linearity; Stacks 09MK
(blueprint: lem-sf-finite-kernel-constructible-localization). -/
def sfKernelScalar (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (a : A) {K L : proEtaleDerivedCategory T A} (f : K ⟶ L) : K ⟶ L :=
  (sfIntrinsicDerivedEquivalence T A).counitIso.inv.app K ≫
    (sfIntrinsicDerivedEquivalence T A).functor.map
      ((ULift.up a : ULift.{u + 1, u} A) •
        (sfIntrinsicDerivedEquivalence T A).inverse.map f) ≫
    (sfIntrinsicDerivedEquivalence T A).counitIso.hom.app L

/-- Direct image is a right adjoint, hence left exact, also in these coefficient
coordinates. This supplies the exact-functor interface once right exactness is known.
Source: Stacks 03D7 (blueprint: lem-sf-finite-kernel-constructible-localization). -/
instance sfKernelPush_limits {Z X : Scheme.{u}} (i : Z ⟶ X)
    (A : Type u) [CommRing A] [Finite A] :
    PreservesFiniteLimits (sfConstantModuleDirectImage i A) :=
  letI := (sfConstantModuleAdjunction i A).rightAdjoint_preservesLimits
  inferInstance

private theorem kernel_push_eq {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    sfConstantModuleDirectImage f A = proEtaleConstantModuleDirectImage f A := by
  unfold sfConstantModuleDirectImage proEtaleRingModuleDirectImage
    proEtaleConstantModuleDirectImage
  have h : proEtaleRingDirectImageMap f (proEtaleConstantRing T A)
      (proEtaleConstantRing Y A) (sfConstantCoefficientIso f A) =
        proEtaleCoefficientDirectImageMap f A :=
    ((proEtaleSheafAdjunction f CommRingCat).homEquiv _ _).apply_symm_apply _
  rw [h]

private def kernel_pull_iso {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    sfConstantModulePullback f A ≅ sfIntrinsicPullback A f :=
  (sfConstantModuleAdjunction f A).leftAdjointUniq
    ((sfIntrinsicConstantModuleAdjunction f A).ofNatIsoRight
      (eqToIso (kernel_push_eq f A)).symm)

attribute [local irreducible] kernel_pull_iso

attribute [local irreducible] coefficientTransport directImageComparison
  AlgebraicGeometry.Scheme.pullbackComparison
  sfConstantCoefficientIso sfIntrinsicConstantModuleAdjunction

private theorem kernel_ringed_data
    {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ (ai : proEtaleModuleInverseImage i B ⊣ proEtaleRingedDirectImage i B)
      (aj : proEtaleModuleInverseImage j B ⊣ proEtaleRingedDirectImage j B),
      Nonempty (ringedSupportKernel j B aj ≅
        ringedClosedKernelShriek i j B aj ⋙ proEtaleRingedDirectImage i B) ∧
        ∀ P, IsIso (ai.counit.app P) := by
  let V : X.ProEt := ProEt.mk j
  have : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  have : QuasiCompact V.hom := ‹QuasiCompact j›
  have hp := proEtale_ringed_open_closed i V hij B
  let q := hp.choose
  let eq := hp.choose_spec.1.some
  let ai := hp.choose_spec.2.choose
  let aBang₀ := hp.choose_spec.2.choose_spec.choose
  have hx := hp.choose_spec.2.choose_spec.choose_spec
  let aj := ringedInverseImageAdjunction j B
  have := ((proEtale_immersion_inverseImage_preservesLimits i).2.2 B).choose
  have := ((proEtale_immersion_inverseImage_preservesLimits j).2.2 B).choose
  have := ((proEtale_immersion_inverseImage_preservesLimits j).2.2 B).choose_spec.1
  have : ∀ P, IsIso (ai.counit.app P) := hx.1
  have : ∀ P, IsIso (aBang₀.unit.app P) := hx.2.1
  have : IsIso ai.counit := NatIso.isIso_of_isIso_app _
  have : IsIso aBang₀.unit := NatIso.isIso_of_isIso_app _
  let er : proEtaleModuleInverseImage j B ≅
      SheafOfModules.overFunctor (proEtaleModuleCoefficients B) V ⋙ q.inverse :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ q.unitIso ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eq q.inverse
  let aBang := (q.toAdjunction.comp aBang₀).ofNatIsoRight er.symm
  have := aBang₀.fullyFaithfulLOfIsIsoUnit.full
  have := aBang₀.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso aBang.unit := aBang.unit_isIso_of_L_fully_faithful
  have : IsIso aj.counit :=
    (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨aBang, aj⟩).mp inferInstance
  have : (proEtaleRingedDirectImage i B).Additive := ai.right_adjoint_additive
  have : (proEtaleRingedDirectImage j B).Additive := aj.right_adjoint_additive
  have : q.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : (proEtaleModuleInverseImage V.hom B).Additive := by
    change (proEtaleModuleInverseImage j B).Additive
    infer_instance
  have : (SheafOfModules.overFunctor (proEtaleModuleCoefficients B) V).Additive :=
    Functor.additive_of_iso eq
  have : (proEtaleRingedExtensionByZero V B).Additive := aBang₀.left_adjoint_additive
  have hsup (N) (h0 : IsZero ((proEtaleModuleInverseImage j B).obj N)) :
      IsIso (ai.unit.app N) :=
    supportedUnitIso ai aBang₀ (fun M ↦ ⟨(hx.2.2.2.2.2.2.2.2.1 M).2.1,
      (hx.2.2.2.2.2.2.2.2.1 M).2.2⟩) N
        ((q.functor.map_isZero h0).of_iso (eq.app N).symm)
  have hz (P) : IsZero ((proEtaleModuleInverseImage j B).obj
      ((proEtaleRingedDirectImage i B).obj P)) :=
    IsZero.of_full_of_faithful_of_isZero q.functor _
      ((hx.2.2.1 P).of_iso (eq.app _))
  have hker := closedKernelConstruction ai aj hsup hz
  exact ⟨ai, aj, ⟨hker.choose_spec.choose_spec.choose⟩, hx.1⟩

private theorem kernel_ringed_disjoint
    {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P : proEtaleRingModules Z ((proEtaleSheafInverseImage i CommRingCat).obj B)) :
    IsZero ((proEtaleModuleInverseImage j B).obj
      ((proEtaleRingedDirectImage i B).obj P)) := by
  let V : X.ProEt := ProEt.mk j
  have : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  have : QuasiCompact V.hom := ‹QuasiCompact j›
  obtain ⟨q, ⟨eq⟩, _, _, _, _, hz, _⟩ := proEtale_ringed_open_closed i V hij B
  exact IsZero.of_full_of_faithful_of_isZero q.functor _
    ((hz P).of_iso (eq.app _))

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_sheaf_data
    (A : Type u) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    ∃ a0 : sfConstantModuleDirectImage i A ⊣ sfIntrinsicClosedUpperShriek i j A,
      ∀ N, IsIso ((sfConstantModuleAdjunction i A).unit.app
        ((sfIntrinsicSectionsWithSupport j A).obj N)) ∧
        (sfConstantModuleAdjunction i A).unit.app
          ((sfIntrinsicSectionsWithSupport j A).obj N) ≫ a0.counit.app N =
            kernel.ι ((sfConstantModuleAdjunction j A).unit.app N) := by
  let B := proEtaleConstantRing X A
  obtain ⟨ai, aj, ⟨eH⟩, hci⟩ := kernel_ringed_data i j hij B
  let ei := coefficientTransport i B (proEtaleConstantRing Z A) (sfConstantCoefficientIso i A)
  let ej := coefficientTransport j B (proEtaleConstantRing U A) (sfConstantCoefficientIso j A)
  let lj := pullbackComparison j B _ (sfConstantCoefficientIso j A) aj
  let di := directImageComparison i B _ (sfConstantCoefficientIso i A)
  have : IsIso ai.counit := NatIso.isIso_of_isIso_app _
  have := ai.fullyFaithfulROfIsIsoCounit.full
  have := ai.fullyFaithfulROfIsIsoCounit.faithful
  have : (sfConstantModuleDirectImage i A).Full := Functor.Full.of_iso di.symm
  have : (sfConstantModuleDirectImage i A).Faithful := Functor.Faithful.of_iso di.symm
  let lj' : sfConstantModulePullback j A ⋙ ej.functor ≅
      proEtaleModuleInverseImage j B :=
    Functor.isoWhiskerRight lj ej.functor ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ej.counitIso ≪≫ Functor.rightUnitor _
  let eK : sfIntrinsicSectionsWithSupport j A ≅ ringedSupportKernel j B aj :=
    (supportKernelIso j A).symm ≪≫
      unitKernelCompEquivalenceIso (sfConstantModuleAdjunction j A) ej ≪≫
      unitKernelIsoOfLeftIso ((sfConstantModuleAdjunction j A).comp ej.toAdjunction) aj lj'
  have hs (N) : IsIso ((sfConstantModuleAdjunction i A).unit.app
      ((sfIntrinsicSectionsWithSupport j A).obj N)) := by
    apply (sfConstantModuleAdjunction i A).isIso_unit_app_iff_mem_essImage.mpr
    refine ⟨ei.inverse.obj ((ringedClosedKernelShriek i j B aj).obj N), ⟨?_⟩⟩
    exact (di.app _ ≪≫ (proEtaleRingedDirectImage i B).mapIso (ei.counitIso.app _) ≪≫
      (eH.app N).symm ≪≫ (eK.app N).symm)
  let H := sfIntrinsicSectionsWithSupport j A
  let k : H ⟶ 𝟭 _ :=
    { app N := kernel.ι ((sfConstantModuleAdjunction j A).unit.app N)
      naturality M N f := by simp [H, sfIntrinsicSectionsWithSupport] }
  have : ∀ N, Mono (k.app N) := fun N ↦ inferInstanceAs
    (Mono (kernel.ι ((sfConstantModuleAdjunction j A).unit.app N)))
  let e : H ≅ sfIntrinsicClosedUpperShriek i j A ⋙ sfConstantModuleDirectImage i A :=
    NatIso.ofComponents (fun N ↦ @asIso _ _ _ _
      ((sfConstantModuleAdjunction i A).unit.app (H.obj N)) (hs N))
      (fun f ↦ (sfConstantModuleAdjunction i A).unit.naturality (H.map f))
  have hz (P) : IsZero ((sfConstantModulePullback j A).obj
      ((sfConstantModuleDirectImage i A).obj P)) := by
    have hr := kernel_ringed_disjoint i j hij B (ei.functor.obj P)
    have he := lj.app ((sfConstantModuleDirectImage i A).obj P) ≪≫
      (proEtaleModuleInverseImage j B ⋙ ej.inverse).mapIso (di.app P)
    exact ((ej.inverse.map_isZero hr)).of_iso he
  have hf (P) (N) (f : (sfConstantModuleDirectImage i A).obj P ⟶ N) :
      ∃ g : (sfConstantModuleDirectImage i A).obj P ⟶ H.obj N, g ≫ k.app N = f := by
    have hh : f ≫ (sfConstantModuleAdjunction j A).unit.app N = 0 := by
      rw [← Functor.id_map (f := f), (sfConstantModuleAdjunction j A).unit.naturality]
      change _ ≫ (sfConstantModuleDirectImage j A).map
        ((sfConstantModulePullback j A).map f) = 0
      rw [(hz P).eq_of_src ((sfConstantModulePullback j A).map f) 0,
        Functor.map_zero, comp_zero]
    exact ⟨kernel.lift _ f hh, kernel.lift_ι _ f hh⟩
  let a := kernelAdjunction (sfConstantModuleDirectImage i A) H
    (sfIntrinsicClosedUpperShriek i j A) k e hf
  refine ⟨a, fun N ↦ ⟨hs N, ?_⟩⟩
  have hn := congrArg (fun z : H ⟶ 𝟭 _ ↦ z.app N)
    (kernelAdjunction_counit (sfConstantModuleDirectImage i A) H
      (sfIntrinsicClosedUpperShriek i j A) k e hf)
  change e.hom.app N ≫ a.counit.app N = k.app N
  exact hn

private def kernelConstructible (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty (proEtaleDerivedCategory T A) := fun K ↦
  Set.Finite {r : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
    (proEtaleRingModules T (proEtaleConstantRing T A)) r).obj K)} ∧
    ∀ r : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor _ r).obj K)

private theorem kernel_constructible_iso (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] {K L : proEtaleDerivedCategory T A}
    (e : K ≅ L) (h : kernelConstructible T A K) : kernelConstructible T A L := by
  constructor
  · apply h.1.subset
    intro r hr hz
    exact hr (hz.of_iso ((DerivedCategory.homologyFunctor _ r).mapIso e).symm)
  · intro r
    exact intrinsicConstructible_of_iso T A
      ((DerivedCategory.homologyFunctor _ r).mapIso e) (h.2 r)

private theorem kernel_constructible_realization (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (L : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    kernelConstructible T A ((sfIntrinsicDerivedEquivalence T A).functor.obj L) ↔
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T L := by
  let R := ProEtale.finiteCoefficientIntrinsicRealization T A
  have : R.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact T A).1
  change kernelConstructible T A (R.mapDerivedCategory.obj L) ↔ _
  constructor
  · intro h
    have hb : DerivedCategory.TStructure.t.bounded L :=
      R.bounded_of_bounded_mapDerivedCategory_obj
        ((finite_homology_support_iff_bounded T A _).mp h.1)
    apply ProEtale.DerivedCategory.boundedConstructible_of_homology _ hb
    intro r
    apply ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
    apply (intrinsicRealization_constructible_iff T A _).mp
    exact intrinsicConstructible_of_iso T A
      ((R.mapDerivedCategoryHomologyFunctorIso r).app L).symm (h.2 r)
  · intro h
    have hh := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic L h
    refine ⟨(finite_homology_support_iff_bounded T A _).mpr
      (R.bounded_mapDerivedCategory_obj hh.1), fun r ↦ ?_⟩
    exact intrinsicConstructible_of_iso T A
      ((R.mapDerivedCategoryHomologyFunctorIso r).app L)
      ((intrinsicRealization_constructible_iff T A _).mpr (hh.2 r))

private theorem kernel_constructible_inverse (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] (K : proEtaleDerivedCategory T A)
    (h : kernelConstructible T A K) :
    ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
        ((sfIntrinsicDerivedEquivalence T A).inverse.obj K) :=
  (kernel_constructible_realization T A _).mp
    (kernel_constructible_iso T A
      ((sfIntrinsicDerivedEquivalence T A).counitIso.app K).symm h)

private instance kernel_transport_additive {Y T : Scheme.{u}}
    (A : Type u) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    [F.Additive] : (sfIntrinsicTransport A F).Additive := by
  unfold sfIntrinsicTransport
  infer_instance

private instance kernel_transport_limits {Y T : Scheme.{u}}
    (A : Type u) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    [PreservesFiniteLimits F] : PreservesFiniteLimits (sfIntrinsicTransport A F) := by
  unfold sfIntrinsicTransport
  infer_instance

private instance kernel_transport_colimits {Y T : Scheme.{u}}
    (A : Type u) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    [PreservesFiniteColimits F] : PreservesFiniteColimits (sfIntrinsicTransport A F) := by
  unfold sfIntrinsicTransport
  infer_instance

private def kernel_transport_derived {Y T : Scheme.{u}}
    (A : Type u) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⥤
      Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (sfIntrinsicTransport A F).mapDerivedCategory ≅
      (sfIntrinsicDerivedEquivalence T A).inverse ⋙ F.mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence T A).inverse
      (F ⋙ (sfIntrinsicModuleEquivalence Y A).functor) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryCompIso F (sfIntrinsicModuleEquivalence Y A).functor)

private instance kernel_realization_additive_early (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).functor.Additive := by
  change (ProEtale.finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.Additive
  infer_instance

private instance kernel_inverse_additive_early (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).inverse.Additive :=
  Equivalence.inverse_additive (sfIntrinsicDerivedEquivalence T A)

attribute [local irreducible] sfIntrinsicModuleEquivalence sfIntrinsicDerivedEquivalence
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor

attribute [local irreducible] kernel_transport_derived

private def kernel_derived_pull_iso {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    (sfConstantModulePullback f A).mapDerivedCategory ≅
      (sfIntrinsicDerivedEquivalence T A).inverse ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor :=
  Functor.mapDerivedCategoryNatIso (kernel_pull_iso f A) ≪≫
    kernel_transport_derived A
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)

attribute [local irreducible] kernel_derived_pull_iso

private def kernel_derived_push_iso {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] :
    (sfConstantModuleDirectImage f A).rightDerivedFunctor ≅
      (sfIntrinsicDerivedEquivalence Y A).inverse ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence T A).functor := by
  let e := sfIntrinsicDerivedEquivalence Y A
  let F := proEtaleConstantDerivedDirectImage f A
  exact Functor.rightDerivedFunctorNatIso (eqToIso (kernel_push_eq f A)) ≪≫
    (Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight e.counitIso.symm F ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e.inverse (sfIntrinsicDerivedDirectImageComparison f A)

attribute [local irreducible] kernel_derived_push_iso

private def kernel_exact_push_iso {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A]
    [PreservesFiniteColimits (sfConstantModuleDirectImage f A)] :
    (sfConstantModuleDirectImage f A).mapDerivedCategory ≅
      (sfIntrinsicDerivedEquivalence Y A).inverse ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
          (sfIntrinsicDerivedEquivalence T A).functor :=
  (sfConstantModuleDirectImage f A).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    kernel_derived_push_iso f A

attribute [local irreducible] kernel_exact_push_iso

private theorem kernel_pull_constructible {Y T : Scheme.{u}} (f : Y ⟶ T)
    (A : Type u) [CommRing A] [Finite A] (K : proEtaleDerivedCategory T A)
    (hK : kernelConstructible T A K) :
    kernelConstructible Y A ((sfConstantModulePullback f A).mapDerivedCategory.obj K) :=
  kernel_constructible_iso Y A ((kernel_derived_pull_iso f A).app K).symm
    ((kernel_constructible_realization Y A _).mpr
      ((kernel_constructible_inverse T A K hK).mapDerivedCategory_upperStar f))

private def kernel_comp_obj_iso
    {C D F C' D' F' : Type*} [Category C] [Category D] [Category F]
    [Category C'] [Category D'] [Category F']
    (ec : C ≌ C') (ed : D ≌ D') (ef : F ≌ F')
    (L : C ⥤ D) (M : D ⥤ F) (L' : C' ⥤ D') (M' : D' ⥤ F')
    (eL : L' ≅ ec.inverse ⋙ L ⋙ ed.functor)
    (eM : M' ≅ ed.inverse ⋙ M ⋙ ef.functor) (K : C') :
    M'.obj (L'.obj K) ≅ ef.functor.obj (M.obj (L.obj (ec.inverse.obj K))) :=
  eM.app _ ≪≫ (ed.inverse ⋙ M ⋙ ef.functor).mapIso (eL.app K) ≪≫
    ef.functor.mapIso (M.mapIso (ed.unitIso.app _).symm)

attribute [local irreducible] kernel_comp_obj_iso

private theorem kernel_essImage
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (ec : C ≌ C') (ed : D ≌ D') (F : C ⥤ D) (F' : C' ⥤ D')
    (eF : F' ≅ ec.inverse ⋙ F ⋙ ed.functor) (K : D')
    (h : F.essImage (ed.inverse.obj K)) : F'.essImage K := by
  obtain ⟨P, ⟨e⟩⟩ := h
  exact ⟨ec.functor.obj P, ⟨eF.app _ ≪≫
    ed.functor.mapIso (F.mapIso (ec.unitIso.app P).symm) ≪≫
      ed.functor.mapIso e ≪≫ ed.counitIso.app K⟩⟩

private theorem kernel_ordinary
    {T Z U : Type*} [Category T] [Category Z] [Category U]
    [Preadditive T] [Preadditive Z] [Preadditive U]
    [HasZeroObject T] [HasZeroObject Z] [HasZeroObject U]
    [HasShift T ℤ] [HasShift Z ℤ] [HasShift U ℤ]
    [∀ m : ℤ, (shiftFunctor T m).Additive]
    [∀ m : ℤ, (shiftFunctor Z m).Additive]
    [∀ m : ℤ, (shiftFunctor U m).Additive]
    [Pretriangulated T] [Pretriangulated Z] [Pretriangulated U]
    (iLeft : T ⥤ Z) (iStar : Z ⥤ T) (jBang : U ⥤ T) (jStar : T ⥤ U)
    [iLeft.CommShift ℤ] [jStar.CommShift ℤ]
    [iLeft.IsTriangulated] [jStar.IsTriangulated]
    (ai : iLeft ⊣ iStar) (ab : jBang ⊣ jStar)
    [iStar.Full] [iStar.Faithful] [IsIso ab.unit]
    (hzero : ∀ P, IsZero (iLeft.obj (jBang.obj P)))
    (hess : ∀ C, IsZero (jStar.obj C) → iStar.essImage C) (M : T) :
    ∃ δ, Triangle.mk (ab.counit.app M) (ai.unit.app M) δ ∈ distTriang T := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle (ab.counit.app M)
  have hz : IsZero (jStar.obj C) := by
    apply (Triangle.isZero₃_iff_isIso₁ _ (jStar.map_distinguished _ hT)).2
    change IsIso (jStar.map (ab.counit.app M))
    rw [← IsIso.inv_eq_of_hom_inv_id (ab.right_triangle_components M)]
    infer_instance
  have hg : IsIso (iLeft.map g) :=
    (Triangle.isZero₁_iff_isIso₂ _ (iLeft.map_distinguished _ hT)).1 (hzero _)
  have hc : IsIso (ai.unit.app C) :=
    ai.isIso_unit_app_iff_mem_essImage.mpr (hess C hz)
  let e := asIso (ai.unit.app C) ≪≫ iStar.mapIso (asIso (iLeft.map g)).symm
  have he : g ≫ e.hom = ai.unit.app M := by
    have hn := ai.unit.naturality g
    dsimp at hn
    simp only [e, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
    rw [reassoc_of% hn, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  refine ⟨e.inv ≫ h, isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_
  · change ab.counit.app M ≫ 𝟙 M = 𝟙 _ ≫ ab.counit.app M
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change ai.unit.app M ≫ e.inv = 𝟙 M ≫ g
    rw [← he]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · change (e.inv ≫ h) ≫ (shiftFunctor T (1 : ℤ)).map (𝟙 _) = e.inv ≫ h
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]

private def kernel_derived_shriek_iso
    (A : Type u) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [PreservesFiniteColimits (sfConstantModuleDirectImage i A)]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (a0 : sfConstantModuleDirectImage i A ⊣ sfIntrinsicClosedUpperShriek i j A) :
    (sfIntrinsicClosedUpperShriek i j A).rightDerivedFunctor ≅
      (sfIntrinsicDerivedEquivalence X A).inverse ⋙
        (ProEtale.closedUpperShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          i j).rightDerivedFunctor ⋙ (sfIntrinsicDerivedEquivalence Z A).functor := by
  let ex := sfIntrinsicDerivedEquivalence X A
  let ez := sfIntrinsicDerivedEquivalence Z A
  let b := ((ez.symm.toAdjunction.comp
    (ProEtale.derivedLowerStarClosedUpperShriekAdjunction
      (R := ULift.{u + 1, u} A) i j hij)).comp ex.toAdjunction).ofNatIsoLeft
        (kernel_exact_push_iso i A).symm
  exact a0.mapDerivedCategoryRightDerivedAdjunction.rightAdjointUniq b

attribute [local irreducible] kernel_derived_shriek_iso

private abbrev kernel_linear (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    CategoryTheory.Linear (ULift.{u + 1, u} A) (proEtaleDerivedCategory T A) where
  homModule K L :=
    ({ toEquiv := (sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.homEquiv
       map_add' := fun f g ↦ (sfIntrinsicDerivedEquivalence T A).inverse.map_add } :
      (K ⟶ L) ≃+ _).module (ULift.{u + 1, u} A)
  smul_comp K L M a f g := by
    apply (sfIntrinsicDerivedEquivalence T A).inverse.map_injective
    change (sfIntrinsicDerivedEquivalence T A).inverse.map
        ((sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.preimage
          (a • (sfIntrinsicDerivedEquivalence T A).inverse.map f) ≫ g) =
      (sfIntrinsicDerivedEquivalence T A).inverse.map
        ((sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.preimage
          (a • (sfIntrinsicDerivedEquivalence T A).inverse.map (f ≫ g)))
    rw [Functor.map_comp,
      (sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.map_preimage,
      (sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.map_preimage,
      Functor.map_comp, Linear.smul_comp]
  comp_smul K L M f a g := by
    apply (sfIntrinsicDerivedEquivalence T A).inverse.map_injective
    change (sfIntrinsicDerivedEquivalence T A).inverse.map
        (f ≫ (sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.preimage
          (a • (sfIntrinsicDerivedEquivalence T A).inverse.map g)) =
      (sfIntrinsicDerivedEquivalence T A).inverse.map
        ((sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.preimage
          (a • (sfIntrinsicDerivedEquivalence T A).inverse.map (f ≫ g)))
    rw [Functor.map_comp,
      (sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.map_preimage,
      (sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.map_preimage,
      Functor.map_comp, Linear.comp_smul]

private theorem kernel_inverse_linear (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    letI := kernel_linear T A
    (sfIntrinsicDerivedEquivalence T A).inverse.Linear (ULift.{u + 1, u} A) := by
  let := kernel_linear T A
  constructor
  intro K L f a
  exact (sfIntrinsicDerivedEquivalence T A).fullyFaithfulInverse.homEquiv.apply_symm_apply _

private theorem kernel_shriek_scalar
    (A : Type u) [CommRing A] [Finite A]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [PreservesFiniteColimits (sfConstantModuleDirectImage i A)]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (a0 : sfConstantModuleDirectImage i A ⊣ sfIntrinsicClosedUpperShriek i j A)
    (K L : proEtaleDerivedCategory X A) (a : A) (f : K ⟶ L) :
    (sfIntrinsicClosedUpperShriek i j A).rightDerivedFunctor.map (sfKernelScalar X A a f) =
      sfKernelScalar Z A a ((sfIntrinsicClosedUpperShriek i j A).rightDerivedFunctor.map f) := by
  let := kernel_linear X A
  let := kernel_linear Z A
  have := kernel_inverse_linear X A
  have := kernel_inverse_linear Z A
  have : (sfIntrinsicDerivedEquivalence Z A).symm.functor.Linear
      (ULift.{u + 1, u} A) := by
    change (sfIntrinsicDerivedEquivalence Z A).inverse.Linear (ULift.{u + 1, u} A)
    exact kernel_inverse_linear Z A
  have : (sfIntrinsicDerivedEquivalence Z A).functor.Linear (ULift.{u + 1, u} A) :=
    Equivalence.inverseLinear (ULift.{u + 1, u} A)
      (sfIntrinsicDerivedEquivalence Z A).symm
  have : (ProEtale.closedUpperShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i j).rightDerivedFunctor.Linear
        (ULift.{u + 1, u} A) :=
    (ProEtale.derivedLowerStarClosedUpperShriekAdjunction
      (R := ULift.{u + 1, u} A) i j hij).right_adjoint_linear
  have := Functor.linear_of_iso (ULift.{u + 1, u} A)
    (kernel_derived_shriek_iso A i j hij a0).symm
  exact Functor.map_smul _ (ULift.up a) f

private theorem kernel_coefficient_killed (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) : ((l ^ n : ℕ) : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) = 0 := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  apply ULift.down_injective
  change ((l ^ n : ℕ) :
    Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
  rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
    Ideal.Quotient.eq_zero_iff_mem]
  simpa only [Nat.cast_pow] using hpow

set_option linter.unusedVariables false in
/-- All assertions concern intrinsic bounded constructibility, with no finite-Tor
condition. The exceptional counit is the actual kernel inclusion transported by the
closed unit. Its derived adjunction is the canonical K-injective one. The ordinary
closed counit is the localized termwise sheaf counit, with its signed-shift comparison.
The ordinary triangle is asserted for every ambient object, before restriction.

Source: blueprint prop-sf-localization-all-stages proof, "Finite stage" and "Vanishing"
(blueprint: lem-sf-finite-kernel-constructible-localization).

Proof plan (the ten DAG steps):
1. The DVR factorization of ℓ and finite quotient theorem make A finite and killed
by ℓ^(n+1), a unit in k. Finite type over a field makes X Noetherian, and every open
quasi-compact. Thus the ringed small-pro-etale open-closed results apply, using the
canonical constant-ring inverse-image identifications.
2. Apply lem-sf-ringed-closed-kernel-adjoint and transport the coefficient rings by
these canonical identifications. It gives i_* ⊣ i!_0, the normalized kernel counit,
the other three adjunctions, invertible closed and open counits, and j*i_*=0.
3. Exact functors descend termwise. Grothendieck module categories have K-injective
resolutions. lem-sp-canonical-right-derived-adjunction-shift and the triangulated
right-adjoint theorem make Ri!_0 and Rj_* exact with the canonical shifts. Kernels
and inverse image are A-linear; lem-weil-kinjective-total-derived-linear derives
this without any assumption on the linearity of resolution choices.
4. Apply the ringed open-closed short exact sequence degreewise to an arbitrary
unbounded representative. lem-weil-pbc-complex-ses-triangle gives the ordinary
triangle with the actual open counit and closed unit.
5. Complete the exceptional counit to a cone triangle. Apply
lem-sf-ordinary-triangle-counit-cone to the four ambient adjunctions and Step 4.
Its comparison with Rj_*j*K carries the second arrow to the actual open unit.
Transport this distinguished triangle. The same lemma gives shifted Hom vanishing.
This construction precedes every boundedness claim about Ri!_0 K.
6. Descend a constructible open input to the etale site by the arbitrary-finite-ring
constructible-origin equivalence. cor-fin-deligne-open-finite-coefficients makes
its open direct image bounded constructible. The qcqs comparison-direct-image
isomorphism transports this assertion back to the intrinsic pro-etale category.
7. lem-weil-proetale-dbc-triangulated gives closure under shifts, cones and fibres.
8. Pull back finite constructible stratifications for i*,j*. For i_* extend the
stratification on Z by the open complement with zero coefficients. Exactness
preserves the cohomological intervals, so these three functors preserve D^b_c.
9. In the supported triangle the other two vertices are constructible by Steps
6 and 8. Thus i_*Ri!_0 K is constructible by Step 7. The invertible closed counit
gives Ri!_0 K ≅ i*i_*Ri!_0 K, hence its constructibility. The ambient Hom bijections,
linearity and exactness restrict to the full subcategories with the same maps.
10. On complexes the closed counit's degree-r component is the sheaf counit.
It is invertible degreewise, so is a chain isomorphism. In a signed shift both
differentials have the same factor (-1)^m; its component becomes the original
component at degree r+m. Localization preserves this counit and its shift square.
-/
theorem finiteKernelConstructibleLocalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    {X Z U : Scheme.{u}} (t : X ⟶ Spec (.of k))
    [LocallyOfFiniteType t] [QuasiCompact t] [IsSeparated t]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (_hij : Set.range j = (Set.range i)ᶜ) :
    ∃ hcol : PreservesFiniteColimits (sfConstantModuleDirectImage i (sfKernelCoefficient l E n)),
    (fun [hc : PreservesFiniteColimits
        (sfConstantModuleDirectImage i (sfKernelCoefficient l E n))] ↦
      ∃ a0 : sfConstantModuleDirectImage i (sfKernelCoefficient l E n) ⊣
          sfIntrinsicClosedUpperShriek i j (sfKernelCoefficient l E n),
        (∀ N,
          IsIso ((sfConstantModuleAdjunction i (sfKernelCoefficient l E n)).unit.app
            ((sfIntrinsicSectionsWithSupport j (sfKernelCoefficient l E n)).obj N)) ∧
          (sfConstantModuleAdjunction i (sfKernelCoefficient l E n)).unit.app
              ((sfIntrinsicSectionsWithSupport j (sfKernelCoefficient l E n)).obj N) ≫
            a0.counit.app N =
              kernel.ι ((sfConstantModuleAdjunction j (sfKernelCoefficient l E n)).unit.app N)) ∧
        Functor.IsTriangulated
          (sfIntrinsicClosedUpperShriek i j (sfKernelCoefficient l E n)).rightDerivedFunctor ∧
        Functor.Additive
          (sfIntrinsicClosedUpperShriek i j (sfKernelCoefficient l E n)).rightDerivedFunctor ∧
        (∀ (K L : proEtaleDerivedCategory X (sfKernelCoefficient l E n))
          (a : sfKernelCoefficient l E n) (f : K ⟶ L),
          (sfIntrinsicClosedUpperShriek i j (sfKernelCoefficient l E n)).rightDerivedFunctor.map
              (sfKernelScalar X (sfKernelCoefficient l E n) a f) =
            sfKernelScalar Z (sfKernelCoefficient l E n) a
              ((sfIntrinsicClosedUpperShriek i j
                (sfKernelCoefficient l E n)).rightDerivedFunctor.map f)) ∧
        (∀ K, intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X K →
          intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z
            ((sfIntrinsicClosedUpperShriek i j (sfKernelCoefficient l E n)).rightDerivedFunctor.obj
              K)) ∧
        (∀ K, intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X K →
          intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z
            ((sfConstantModulePullback i (sfKernelCoefficient l E n)).mapDerivedCategory.obj K) ∧
          intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U
            ((sfConstantModulePullback j (sfKernelCoefficient l E n)).mapDerivedCategory.obj K)) ∧
        (∀ P, intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z P →
          intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
            ((sfConstantModuleDirectImage i
              (sfKernelCoefficient l E n)).mapDerivedCategory.obj P)) ∧
        (∀ G, intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U G →
          intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
            ((sfConstantModuleDirectImage j (sfKernelCoefficient l E n)).rightDerivedFunctor.obj
              G)) ∧
        (∀ M : proEtaleDerivedCategory X (sfKernelCoefficient l E n),
          ∃ δ : (proEtaleConstantDerivedDirectImage i (sfKernelCoefficient l E n)).obj
              ((finiteDerivedPullback l E n i).obj M) ⟶
              (sfIntrinsicDerivedOpen (sfKernelCoefficient l E n) j).obj
                ((finiteDerivedPullback l E n j).obj M)⟦(1 : ℤ)⟧,
            Triangle.mk
              ((exceptionalOpenAdjunction j (sfKernelCoefficient l E n)).counit.app M)
              ((finiteRecollementDerivedAdjunction i (sfKernelCoefficient l E n)).unit.app M) δ ∈
              distTriang (proEtaleDerivedCategory X (sfKernelCoefficient l E n))) ∧
        (∀ (K : proEtaleDerivedCategory X (sfKernelCoefficient l E n)),
          intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X K →
          ∃ δ : (sfConstantModuleDirectImage j (sfKernelCoefficient l E n)).rightDerivedFunctor.obj
              ((sfConstantModulePullback j (sfKernelCoefficient l E n)).mapDerivedCategory.obj K) ⟶
              ((sfConstantModuleDirectImage i (sfKernelCoefficient l E n)).mapDerivedCategory.obj
                ((sfIntrinsicClosedUpperShriek i j
                  (sfKernelCoefficient l E n)).rightDerivedFunctor.obj K))⟦(1 : ℤ)⟧,
            Triangle.mk (a0.mapDerivedCategoryRightDerivedAdjunction.counit.app K)
              ((Adjunction.mapDerivedCategoryRightDerivedAdjunction
                (sfConstantModuleAdjunction j (sfKernelCoefficient l E n))).unit.app K) δ ∈
              distTriang (proEtaleDerivedCategory X (sfKernelCoefficient l E n))) ∧
        (∀ (P : proEtaleDerivedCategory Z (sfKernelCoefficient l E n))
          (G : proEtaleDerivedCategory U (sfKernelCoefficient l E n)) (m : ℤ),
          intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z P →
          intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U G →
          Subsingleton
            (((sfConstantModuleDirectImage i (sfKernelCoefficient l E n)).mapDerivedCategory.obj
              P)⟦m⟧ ⟶
              (sfConstantModuleDirectImage j (sfKernelCoefficient l E n)).rightDerivedFunctor.obj
                G)) ∧
        (∀ P : proEtaleDerivedCategory Z (sfKernelCoefficient l E n),
          intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z P →
          IsIso ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
            (sfConstantModuleAdjunction i (sfKernelCoefficient l E n))).counit.app P)) ∧
        NatTrans.CommShift
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
            (sfConstantModuleAdjunction i (sfKernelCoefficient l E n))).counit ℤ ∧
        (∀ I : CochainComplex
          (proEtaleRingModules Z (proEtaleConstantRing Z (sfKernelCoefficient l E n))) ℤ,
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
              (sfConstantModuleAdjunction i (sfKernelCoefficient l E n))).counit.app
              (DerivedCategory.Q.obj I) =
            (sfConstantModulePullback i (sfKernelCoefficient l E n)).mapDerivedCategory.map
              ((sfConstantModuleDirectImage i
                (sfKernelCoefficient l E n)).mapDerivedCategoryFactors.hom.app I) ≫
            (sfConstantModulePullback i
              (sfKernelCoefficient l E n)).mapDerivedCategoryFactors.hom.app
              (((sfConstantModuleDirectImage i (sfKernelCoefficient l E n)).mapHomologicalComplex
                (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map
              (((sfConstantModuleAdjunction i (sfKernelCoefficient l E n)).mapHomologicalComplex
                (.up ℤ)).counit.app I))) (hc := hcol) := by
  let A := sfKernelCoefficient l E n
  let C := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType t
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [_hij]
    exact isCompl_compl
  have := (sfIntrinsicClosedAmbientAdjunction A i j hij).1
  refine ⟨inferInstance, ?_⟩
  obtain ⟨a0, ha0⟩ := kernel_sheaf_data A i j _hij
  let ex := sfIntrinsicDerivedEquivalence X A
  let ez := sfIntrinsicDerivedEquivalence Z A
  let eu := sfIntrinsicDerivedEquivalence U A
  let Pi := (ProEtale.lowerStar C i).rightDerivedFunctor
  let Li := (ProEtale.upperStar C i).mapDerivedCategory
  let Lj := (ProEtale.upperStar C j).mapDerivedCategory
  let Bj := (ProEtale.openImmersionLowerShriek C j).mapDerivedCategory
  let ip := (sfConstantModuleDirectImage i A).mapDerivedCategory
  let jp := (sfConstantModuleDirectImage j A).rightDerivedFunctor
  let il := (sfConstantModulePullback i A).mapDerivedCategory
  let jl := (sfConstantModulePullback j A).mapDerivedCategory
  let ib := sfIntrinsicDerivedOpen A j
  let ei := kernel_exact_push_iso i A
  let ej := kernel_derived_push_iso j A
  let eli := kernel_derived_pull_iso i A
  let elj := kernel_derived_pull_iso j A
  let eb := kernel_transport_derived A (ProEtale.openImmersionLowerShriek C j)
  have : ip.Full := Functor.Full.of_iso ei.symm
  have : ip.Faithful := Functor.Faithful.of_iso ei.symm
  have hfj := (ProEtale.mapDerivedUpperStarLowerStarAdjunction
    (ULift.{u + 1, u} A) j).fullyFaithfulROfIsIsoCounit
  have := hfj.full
  have := hfj.faithful
  have : jp.Full := Functor.Full.of_iso ej.symm
  have : jp.Faithful := Functor.Faithful.of_iso ej.symm
  have : IsIso (ProEtale.openImmersionLowerShriekUpperStarAdjunction C j).unit :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction C j).unit_isIso_of_L_fully_faithful
  have : IsIso (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction C j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have hfb :=
    (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction C j).fullyFaithfulLOfIsIsoUnit
  have := hfb.full
  have := hfb.faithful
  have : ib.Full := Functor.Full.of_iso eb.symm
  have : ib.Faithful := Functor.Faithful.of_iso eb.symm
  let ai := SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (sfConstantModuleAdjunction i A)
  let aj := (sfConstantModuleAdjunction j A).mapDerivedCategoryRightDerivedAdjunction
  let ab := (exceptionalOpenAdjunction j A).ofNatIsoRight
    (Functor.mapDerivedCategoryNatIso (kernel_pull_iso j A)).symm
  have : IsIso ai.counit := ai.counit_isIso_of_R_fully_faithful
  have : IsIso aj.counit := aj.counit_isIso_of_R_fully_faithful
  have : IsIso ab.unit := ab.unit_isIso_of_L_fully_faithful
  have hd (P) : IsZero (jl.obj (ip.obj P)) :=
    (eu.functor.map_isZero
      (ProEtale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedFunctor_lowerStar
        i j hij (ez.inverse.obj P))).of_iso
      (kernel_comp_obj_iso ez ex eu Pi Lj ip jl ei elj P)
  have hz (P) : IsZero (il.obj (ib.obj P)) :=
    (ez.functor.map_isZero
      (ProEtale.isZero_mapDerivedCategoryUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek
        i j hij.disjoint (eu.inverse.obj P))).of_iso
      (kernel_comp_obj_iso eu ex ez Bj Li ib il eb eli P)
  have hess (K) (hK : IsZero (jl.obj K)) : ip.essImage K := by
    have hh : IsZero (eu.functor.obj (Lj.obj (ex.inverse.obj K))) :=
      hK.of_iso (elj.app K).symm
    have hh' := IsZero.of_full_of_faithful_of_isZero eu.functor _ hh
    exact kernel_essImage ez ex Pi ip ei K
      (ProEtale.rightDerivedFunctor_lowerStar_essImage_of_isZero i j hij hh')
  have hord := kernel_ordinary il ip ib jl ai ab hz hess
  have hsuppEss (K) (hK : IsZero (jl.obj K)) : ip.essImage K := by
    obtain ⟨δ, hδ⟩ := hord K
    have : IsIso (ai.unit.app K) :=
      (Triangle.isZero₁_iff_isIso₂ _ hδ).1 (ib.map_isZero hK)
    exact ⟨il.obj K, ⟨(asIso (ai.unit.app K)).symm⟩⟩
  have hsup := Recollement.exists_distTriang_counit_unit aj
    a0.mapDerivedCategoryRightDerivedAdjunction (Functor.FullyFaithful.ofFullyFaithful ip)
    hd hsuppEss
  let intrinsicPi := proEtaleConstantDerivedDirectImage i A
  let epi : intrinsicPi ≅ ez.inverse ⋙ Pi ⋙ ex.functor :=
    (Functor.rightDerivedFunctorNatIso (eqToIso (kernel_push_eq i A))).symm ≪≫
      kernel_derived_push_iso i A
  let eli' := kernel_transport_derived A (ProEtale.upperStar C i)
  let elj' := kernel_transport_derived A (ProEtale.upperStar C j)
  have : intrinsicPi.Full := Functor.Full.of_iso epi.symm
  have : intrinsicPi.Faithful := Functor.Faithful.of_iso epi.symm
  have : IsIso (exceptionalOpenAdjunction j A).unit :=
    (exceptionalOpenAdjunction j A).unit_isIso_of_L_fully_faithful
  have hz' (P) : IsZero ((sfIntrinsicDerivedPullback A i).obj (ib.obj P)) :=
    (ez.functor.map_isZero
      (ProEtale.isZero_mapDerivedCategoryUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek
        i j hij.disjoint (eu.inverse.obj P))).of_iso
      (kernel_comp_obj_iso eu ex ez Bj Li ib _ eb eli' P)
  have hess' (K) (hK : IsZero ((sfIntrinsicDerivedPullback A j).obj K)) :
      intrinsicPi.essImage K := by
    have hh : IsZero (eu.functor.obj (Lj.obj (ex.inverse.obj K))) :=
      hK.of_iso (elj'.app K).symm
    have hh' := IsZero.of_full_of_faithful_of_isZero eu.functor _ hh
    exact kernel_essImage ez ex Pi intrinsicPi epi K
      (ProEtale.rightDerivedFunctor_lowerStar_essImage_of_isZero i j hij hh')
  have hord' := kernel_ordinary (sfIntrinsicDerivedPullback A i) intrinsicPi ib
    (sfIntrinsicDerivedPullback A j) (finiteRecollementDerivedAdjunction i A)
    (exceptionalOpenAdjunction j A) hz' hess'
  have hk : ((l ^ (n + 1) : ℕ) : ULift.{u + 1, u} A) = 0 :=
    kernel_coefficient_killed l E (n + 1)
  have hu : IsUnit ((l ^ (n + 1) : ℕ) : k) := by
    simpa only [Nat.cast_pow] using _hl.pow (n + 1)
  refine ⟨a0, ha0, inferInstance, inferInstance, kernel_shriek_scalar A i j hij a0,
    ?_, ?_, ?_, ?_, hord', ?_, ?_, ?_, ?_, ?_⟩
  · intro K hK
    apply kernel_constructible_iso Z A ((kernel_derived_shriek_iso A i j hij a0).app K).symm
    apply (kernel_constructible_realization Z A _).mpr
    exact ProEtale.boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj
      i j (l ^ (n + 1)) hu.ne_zero hk t hij (kernel_constructible_inverse X A K hK)
  · intro K hK
    exact ⟨kernel_pull_constructible i A K hK, kernel_pull_constructible j A K hK⟩
  · intro P hP
    apply kernel_constructible_iso X A (ei.app P).symm
    apply (kernel_constructible_realization X A _).mpr
    exact ProEtale.boundedConstructible_rightDerivedFunctor_lowerStar_of_isClosedImmersion
      i (l ^ (n + 1)) hu.ne_zero hk t (kernel_constructible_inverse Z A P hP)
  · intro G hG
    apply kernel_constructible_iso X A (ej.app G).symm
    apply (kernel_constructible_realization X A _).mpr
    exact ProEtale.boundedConstructible_rightDerivedFunctor_lowerStar_of_isOpenImmersion
      j (l ^ (n + 1)) hu.ne_zero hk t (kernel_constructible_inverse U A G hG)
  · intro K hK
    exact hsup K
  · intro P G m hP hG
    exact Recollement.subsingleton_hom_shift ip jl aj hd P G m
  · intro P hP
    infer_instance
  · have hunit : NatTrans.CommShift ai.unit ℤ :=
      (sfConstantModuleAdjunction i A).mapExactDerivedCategory_unit_commShift.2
    have := Adjunction.CommShift.mk' ai ℤ hunit
    infer_instance
  · exact exactDerivedAdjunction_counit (sfConstantModuleAdjunction i A)

end WeilConjectures
