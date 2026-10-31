/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingMappingTower
import WeilConjectures.AlgebraicGeometry.CoefficientDuality
import WeilConjectures.CategoryTheory.ExactDerivedMonoidalConstruction
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.CoefficientConstantTowerRoosComparisonSupplement
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # The resolved coefficient Hom tower comparison

Source: current blueprint prop-coef-integral-dualizing, final displayed comparison;
Stacks 0941 and 08J9.

(blueprint: lem-coef-integral-dualizing-coefficient-hom-tower-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped MonoidalClosed.FunctorCategory
namespace WeilConjectures

section ClosedAdjunction
open MonoidalCategory MonoidalClosed
variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  (F : C ⥤ D) [F.Monoidal] (G : D ⥤ C) (a : F ⊣ G)

private def closedRightAdjointComponent (X : C) :
    ihom (F.obj X) ⋙ G ≅ G ⋙ ihom X :=
  conjugateIsoEquiv (a.comp (ihom.adjunction (F.obj X)))
    ((ihom.adjunction X).comp a) (Functor.Monoidal.commTensorLeft F X).symm

private theorem closedRightAdjoint_natural {X X' : C} (f : X' ⟶ X) :
    Functor.whiskerRight (pre (F.map f)) G ≫
        (closedRightAdjointComponent F G a X').hom =
      (closedRightAdjointComponent F G a X).hom ≫ Functor.whiskerLeft G (pre f) := by
  simp only [closedRightAdjointComponent, conjugateIsoEquiv, Equiv.coe_fn_mk, pre]
  rw [← conjugateEquiv_whiskerLeft (ihom.adjunction (F.obj X))
      (ihom.adjunction (F.obj X')) a,
    ← conjugateEquiv_whiskerRight (ihom.adjunction X) (ihom.adjunction X') a,
    conjugateEquiv_comp, conjugateEquiv_comp]
  congr 1
  ext Y
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.Monoidal.commTensorLeft_inv_app]
  change Functor.OplaxMonoidal.δ F X' Y ≫ (F.map f ▷ F.obj Y) =
    F.map (f ▷ Y) ≫ Functor.OplaxMonoidal.δ F X Y
  exact Functor.OplaxMonoidal.δ_natural_left F f Y

@[irreducible]
private def closedRightAdjointIso (Y : D) :
    F.op ⋙ internalHom.flip.obj Y ⋙ G ≅ internalHom.flip.obj (G.obj Y) :=
  NatIso.ofComponents (fun X ↦ (closedRightAdjointComponent F G a X.unop).app Y)
    (fun f ↦ congr_app (closedRightAdjoint_natural F G a f.unop) Y)

include a in
private theorem existsClosedRightAdjointIso (Y : D) :
    Nonempty (F.op ⋙ internalHom.flip.obj Y ⋙ G ≅ internalHom.flip.obj (G.obj Y)) :=
  ⟨closedRightAdjointIso F G a Y⟩

end ClosedAdjunction

private theorem closedRightAdjointIsoOfExists
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (F : C ⥤ D) (G : D ⥤ C) (hm : Nonempty F.Monoidal) (ha : Nonempty (F ⊣ G))
    (Y : D) :
    Nonempty (F.op ⋙ MonoidalClosed.internalHom.flip.obj Y ⋙ G ≅
      MonoidalClosed.internalHom.flip.obj (G.obj Y)) := by
  obtain ⟨m⟩ := hm
  let := m
  obtain ⟨a⟩ := ha
  exact existsClosedRightAdjointIso F G a Y

section ExactDerivedClosed
universe a b v
variable {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasColimitsOfSize.{0, 0} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [HasDerivedCategory.{v} A]
  {B : Type b} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
  [HasColimitsOfSize.{0, 0} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  [HasDerivedCategory.{v} B]

private theorem exactDerivedMonoidal (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesColimitsOfSize.{0, 0} F] [F.PreservesFlat] [F.Monoidal] :
    Nonempty F.mapDerivedCategory.Monoidal := by
  obtain ⟨m, _⟩ :=
    CategoryTheory.ConstantModuleDerivedProjection.exact_monoidal_normalization F
      (inferInstance : F.Monoidal)
  exact ⟨m⟩

end ExactDerivedClosed

section ModuleLimit
universe r
private theorem moduleLimitOfSurjective (R : Type r) [CommRing R]
    [HasDerivedCategory (ModuleCat.{r} R)]
    (X : CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{r} R) ℤ)
    (hX : ∀ (p : ℤ) (n : ℕ), Epi ((X.X p).map (homOfLE n.le_succ).op)) :
    Nonempty ((CoefTower.totalLimit R).obj (DerivedCategory.Q.obj X) ≅
      DerivedCategory.Q.obj (limit X.asFunctor)) := by
  let A := ModuleCat.{r} R
  let : IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A) :=
    { ab5OfSize := ⟨fun _ _ _ ↦ inferInstance⟩ }
  let L : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let η : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.rightDerivedFunctor :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  let β := (Functor.isoWhiskerRight (strictTowerLimitIso (A := A))
    DerivedCategory.Q).hom ≫ η
  obtain ⟨e, _⟩ := normalizedRoosIso L.rightDerivedFunctor β (fun I hI ↦ by
    have := hI
    dsimp only [β, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, η]
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    exact ((DerivedCategory.Q.mapIso ((strictTowerLimitIso (A := A)).app I)) ≪≫
      (L.rightDerivedFunctorObjQIso I).symm).isIso_hom)
  let K := fun n : ℕ ↦ X.asFunctor.obj (op n)
  let P : Fan K := Fan.mk (roosP X) (Pi.π K)
  let s : P.pt ⟶ P.pt := towerProductShift
    (fun n ↦ X.asFunctor.map (homOfLE n.le_succ).op)
  have hs (n : ℕ) : s ≫ P.proj n =
      P.proj (n + 1) ≫ X.asFunctor.map (homOfLE n.le_succ).op := Pi.lift_π _ _
  have hu (p : ℤ) : Epi ((roosU X).f p) := by
    let ev := HomologicalComplex.eval A (.up ℤ) p
    let F := X.asFunctor ⋙ ev
    let B : Fan (fun n : ℕ ↦ F.obj (op n)) :=
      Fan.mk (P.pt.X p) (fun n ↦ (P.proj n).f p)
    have hB : IsLimit B :=
      (Fan.isLimitMapConeEquiv ev K P) (isLimitOfPreserves ev (productIsProduct K))
    have hsp (n : ℕ) : s.f p ≫ B.proj n =
        B.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op := by
      change s.f p ≫ (P.proj n).f p =
        (P.proj (n + 1)).f p ≫ (X.asFunctor.map (homOfLE n.le_succ).op).f p
      simpa only [HomologicalComplex.comp_f] using congrArg (fun f ↦ f.f p) (hs n)
    have he : Epi (𝟙 (P.pt.X p) - s.f p) :=
      ModuleCat.epi_one_sub_of_epi hB (s.f p) hsp (fun n ↦ hX p n)
    exact he
  obtain ⟨_, _, _, ⟨q⟩⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi (roosU X) hu
  have hk := Fan.IsLimit.isLimitKernelForkOneSub (productIsProduct K) s hs
    (limit.isLimit X.asFunctor)
  let k := hk.conePointUniqueUpToIso (kernelIsKernel (roosU X))
  exact ⟨(e.app X).symm ≪≫ q.symm ≪≫ DerivedCategory.Q.mapIso k.symm⟩
private theorem moduleConeLimitOfFamilies (R : Type r) [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{r} R) (c : Cone F)
    (h : ∀ b : ∀ j, F.obj j,
      (∀ ⦃i j : ℕᵒᵖ⦄ (f : i ⟶ j), F.map f (b i) = b j) →
        ∃! x : c.pt, ∀ j, c.π.app j x = b j) : Nonempty (IsLimit c) := by
  classical
  refine ⟨isLimitOfReflects (forget (ModuleCat.{r} R)) ?_⟩
  apply Classical.choice
  exact (Types.isLimit_iff _).2 h

private instance constantTower_preservesFlat (R : Type r) [CommRing R] :
    (Functor.const ℕᵒᵖ : ModuleCat.{r} R ⥤
      (ℕᵒᵖ ⥤ ModuleCat.{r} R)).PreservesFlat where
  flat_obj {M} hM := by
    rw [ObjectProperty.flat_iff_preservesFiniteLimits]
    have : PreservesFiniteLimits (MonoidalCategory.tensorLeft M) :=
      (ObjectProperty.flat_iff_preservesFiniteLimits M).1 hM
    exact preservesFiniteLimits_of_evaluation _ fun n ↦
      inferInstanceAs (PreservesFiniteLimits
        ((evaluation ℕᵒᵖ (ModuleCat.{r} R)).obj n ⋙
          MonoidalCategory.tensorLeft M))

end ModuleLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- The cone is constructed from the actual reduction maps, not from a chosen witness.
private def quotientScalarMap (n : ℕ) :
    ModuleCat.of (coefTraceRing l E) (coefTraceRing l E) ⟶
      coefTraceQuotientModule l E n :=
  ModuleCat.ofHom (R := coefTraceRing l E)
    (X := ModuleCat.of (coefTraceRing l E) (coefTraceRing l E))
    (Y := coefTraceQuotientModule l E n)
    { toFun := coefTraceQuotient l E n
      map_add' := (coefTraceQuotient l E n).map_add
      map_smul' := fun r x ↦ (coefTraceQuotient l E n).map_mul r x }

private def quotientCone : Cone (coefCurryingQuotients l E) where
  pt := ModuleCat.of (coefTraceRing l E) (coefTraceRing l E)
  π := NatTrans.ofOpSequence (quotientScalarMap l E) (fun n ↦ by
    simp only [Functor.const_obj_map, coefCurryingQuotients,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : coefTraceRing l E →+* finiteDualizingCoeff l E n ↦ f x)
      (coefTraceQuotient_comp l E n.le_succ))

private theorem quotientFamilyUnique
    (b : ∀ n : ℕ, finiteDualizingCoeff l E n)
    (hb : ∀ n : ℕ, finiteDualizingQuotient l E n.le_succ (b (n + 1)) = b n) :
    ∃! x : coefTraceRing l E, ∀ n, coefTraceQuotient l E n x = b n := by
  obtain ⟨e, he, _⟩ :=
    (Padic.coefficientExtension_integers_profinite_tower.{u, 0} l E).1
  let c : Padic.coefficientExtensionPositiveLimit l E :=
    ⟨fun n ↦ (b n).down, by
      simp only [Padic.coefficientExtensionPositiveLimit, Subring.mem_iInf,
        RingHom.mem_eqLocus, RingHom.comp_apply, Pi.evalRingHom_apply]
      intro n
      exact congrArg ULift.down (hb n)⟩
  refine ⟨ULift.up (e.symm c), ?_, ?_⟩
  · intro n
    apply ULift.ext
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      (e.symm c) = (b n).down
    rw [← he, e.apply_symm_apply]
  · intro x hx
    apply ULift.ext
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he, e.apply_symm_apply]
    exact congrArg ULift.down (hx n)

private theorem quotientConeIsLimit : Nonempty (IsLimit (quotientCone l E)) := by
  apply moduleConeLimitOfFamilies (coefTraceRing l E) (coefCurryingQuotients l E)
  intro b hb
  obtain ⟨x, hx, huniq⟩ := quotientFamilyUnique l E (fun n ↦ b (op n)) (fun n ↦ by
    have hn := hb (homOfLE n.le_succ).op
    simp only [coefCurryingQuotients, Functor.ofOpSequence_map_homOfLE_succ] at hn
    change (coefTraceQuotientMap l E n.le_succ).hom (b (op (n + 1))) = b (op n) at hn
    exact hn)
  refine ⟨x, fun j ↦ hx j.unop, ?_⟩
  intro y hy
  exact huniq y (fun n ↦ hy (op n))

private theorem smallConstantComparison :
    letI := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
    Nonempty ((Functor.const ℕᵒᵖ : ModuleCat.{u + 1}
      (integralDualizingCoefficients l E) ⥤ coefPairingModules l E).mapDerivedCategory ⋙
        (integralDualizingTowerEquivalence l E).functor ≅
      CoefTower.constant (integralDualizingCoefficients l E)) := by
  let R := integralDualizingCoefficients l E
  let F := (Functor.const ℕᵒᵖ : ModuleCat.{u + 1} R ⥤ coefPairingModules l E)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Qstd := @DerivedCategory.Q (coefPairingModules l E) _ _
    (CoefTower.moduleTowersDerived R)
  let κstd : DerivedCategory.Q ⋙ CoefTower.constant R ≅ Fc ⋙ Qstd :=
    F.mapDerivedCategoryFactors
  let := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
  let Fs := F.mapDerivedCategory
  let e := integralDualizingTowerEquivalence l E
  exact ⟨Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} R) (.up ℤ)) _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors e.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Fc
        (Localization.compUniqFunctor (integralDualizingSmallTowerQ l E) Qstd
          (HomologicalComplex.quasiIso (coefPairingModules l E) (.up ℤ))) ≪≫ κstd.symm)⟩

private theorem smallConstantAdjunction :
    letI := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
    Nonempty ((Functor.const ℕᵒᵖ : ModuleCat.{u + 1}
      (integralDualizingCoefficients l E) ⥤ coefPairingModules l E).mapDerivedCategory ⊣
      (integralDualizingTowerEquivalence l E).functor ⋙
        CoefTower.totalLimit (integralDualizingCoefficients l E)) := by
  let := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
  let F := (Functor.const ℕᵒᵖ : ModuleCat.{u + 1}
    (integralDualizingCoefficients l E) ⥤ coefPairingModules l E).mapDerivedCategory
  let e := integralDualizingTowerEquivalence l E
  obtain ⟨c⟩ := smallConstantComparison l E
  let d : CoefTower.constant (integralDualizingCoefficients l E) ⋙ e.inverse ≅ F :=
    Functor.isoWhiskerRight c.symm e.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F e.unitIso.symm ≪≫ Functor.rightUnitor F
  exact ⟨((CoefTower.adjunction (integralDualizingCoefficients l E)).comp
    e.symm.toAdjunction).ofNatIsoLeft d⟩

private theorem smallClosedTowerComparison (Y : integralDualizingSmallTower l E) :
    letI := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
    let F := (Functor.const ℕᵒᵖ : ModuleCat.{u + 1}
      (integralDualizingCoefficients l E) ⥤ coefPairingModules l E).mapDerivedCategory
    let G := (integralDualizingTowerEquivalence l E).functor ⋙
      CoefTower.totalLimit (integralDualizingCoefficients l E)
    Nonempty (F.op ⋙ MonoidalClosed.internalHom.flip.obj Y ⋙ G ≅
      MonoidalClosed.internalHom.flip.obj (G.obj Y)) := by
  let := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
  let F := (Functor.const ℕᵒᵖ : ModuleCat.{u + 1}
    (integralDualizingCoefficients l E) ⥤ coefPairingModules l E)
  let : F.IsLeftAdjoint := ⟨_, ⟨constLimAdj⟩⟩
  -- Infer the closed structures from the goal to keep its scalar-instance presentation.
  refine @closedRightAdjointIsoOfExists _ _ _ _ _ _ _ _ _ _ ?_ ?_ _
  · exact exactDerivedMonoidal F
  · exact smallConstantAdjunction l E

private theorem homTowerLimitComparison :
    Nonempty (integralDualizingCoefficientHomTower l E ⋙
      CoefTower.totalLimit (integralDualizingCoefficients l E) ≅
        MonoidalClosed.internalHom.flip.obj
          ((CoefTower.totalLimit (integralDualizingCoefficients l E)).obj
            (coefCurryingTarget l E))) := by
  let R := integralDualizingCoefficients l E
  let e := integralDualizingTowerEquivalence l E
  let Qstd := @DerivedCategory.Q (coefPairingModules l E) _ _
    (CoefTower.moduleTowersDerived R)
  let Sstd := @DerivedCategory.singleFunctor (coefPairingModules l E) _ _
    (CoefTower.moduleTowersDerived R) 0
  let κstd : Sstd ≅ HomologicalComplex.single (coefPairingModules l E) (.up ℤ) 0 ⋙
      Qstd := DerivedCategory.singleFunctorIsoCompQ _ 0
  let := HasDerivedCategory.ofIsGrothendieckAbelian (coefPairingModules l E)
  let Y := (DerivedCategory.singleFunctor (coefPairingModules l E) 0).obj
    (coefCurryingQuotients l E)
  let κ : e.functor.obj Y ≅ coefCurryingTarget l E :=
    e.functor.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
      (coefCurryingQuotients l E)) ≪≫
      (Localization.compUniqFunctor (integralDualizingSmallTowerQ l E) Qstd
        (HomologicalComplex.quasiIso (coefPairingModules l E) (.up ℤ))).app
          ((HomologicalComplex.single (coefPairingModules l E) (.up ℤ) 0).obj
            (coefCurryingQuotients l E)) ≪≫ (κstd.app (coefCurryingQuotients l E)).symm
  obtain ⟨h⟩ := smallClosedTowerComparison l E Y
  dsimp only [integralDualizingCoefficientHomTower]
  refine ⟨(Functor.associator _ _ _) ≪≫
    (Functor.isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫ ?_⟩
  refine h ≪≫ ?_
  exact MonoidalClosed.internalHom.flip.mapIso ((CoefTower.totalLimit R).mapIso κ)

private theorem quotientTotalLimitUnit :
    Nonempty ((CoefTower.totalLimit (integralDualizingCoefficients l E)).obj
      (coefCurryingTarget l E) ≅
        𝟙_ (DerivedCategory (ModuleCat.{u + 1} (integralDualizingCoefficients l E)))) := by
  let R := integralDualizingCoefficients l E
  let A := ModuleCat.{u + 1} R
  let T := coefPairingModules l E
  let S := HomologicalComplex.single T (.up ℤ) 0
  let X := S.obj (coefCurryingQuotients l E)
  have hmap (n : ℕ) : Epi (coefTraceQuotientMap l E n.le_succ) := by
    apply (ModuleCat.epi_iff_surjective (coefTraceQuotientMap l E n.le_succ)).2
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y.down
    refine ⟨ULift.up (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l E (n + 1 + 1)) a), ?_⟩
    apply ULift.ext
    exact ha
  have hX (p : ℤ) (n : ℕ) : Epi ((X.X p).map (homOfLE n.le_succ).op) := by
    by_cases hp : p = 0
    · subst p
      change Epi ((coefCurryingQuotients l E).map (homOfLE n.le_succ).op)
      simp only [coefCurryingQuotients, Functor.ofOpSequence_map_homOfLE_succ]
      change Epi (coefTraceQuotientMap l E n.le_succ)
      exact hmap n
    · have hz : IsZero (X.X p) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp
      exact (Functor.map_isZero ((evaluation ℕᵒᵖ A).obj (op n)) hz).epi _
  obtain ⟨h⟩ := moduleLimitOfSurjective R X hX
  obtain ⟨hcone⟩ := quotientConeIsLimit l E
  let q : limit (coefCurryingQuotients l E) ≅ ModuleCat.of R R :=
    (limit.isLimit _).conePointUniqueUpToIso hcone
  let k : limit X.asFunctor ≅ (HomologicalComplex.single A (.up ℤ) 0).obj (𝟙_ A) :=
    (strictTowerLimitIso (A := A)).app X ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (lim : T ⥤ A) (.up ℤ) 0).app
        (coefCurryingQuotients l E) ≪≫
      (HomologicalComplex.single A (.up ℤ) 0).mapIso q
  exact ⟨(CoefTower.totalLimit R).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ T 0).app (coefCurryingQuotients l E)) ≪≫
    h ≪≫ DerivedCategory.Q.mapIso k ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ A 0).app (𝟙_ A)).symm ≪≫
      DerivedCategory.singleFunctorObjUnitIso A⟩

/--
The resolved comparison map from the constant-coefficient Hom tower to the
coefficient derived dual.  Its construction uses one K-flat representative and
one simultaneous K-injective representative of the quotient tower; the Roos
calculation and completeness identify the resulting map with the derived dual.
The assertion records the natural transformation and the componentwise
isomorphism property separately, so the enclosing functor-isomorphism theorem
only performs the categorical assembly.

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph,
three displayed mapping-complex comparisons; Stacks 0941 and 08J9.
(blueprint: lem-coef-integral-dualizing-coefficient-hom-tower-comparison).
-/
theorem integralDualizing_coefficient_hom_tower_comparison :
    ∃ α : integralDualizingCoefficientHomTower l E ⋙
        CoefTower.totalLimit (integralDualizingCoefficients l E) ⟶
      coefficientDerivedDual (integralDualizingCoefficients l E),
      ∀ C : DerivedCategory (ModuleCat.{u + 1}
        (integralDualizingCoefficients l E)),
        IsIso (α.app (op C)) := by
  obtain ⟨e⟩ := quotientTotalLimitUnit l E
  obtain ⟨h⟩ := homTowerLimitComparison l E
  let i := h ≪≫ MonoidalClosed.internalHom.flip.mapIso e
  exact ⟨i.hom, fun C ↦ (i.app (op C)).isIso_hom⟩

end WeilConjectures
