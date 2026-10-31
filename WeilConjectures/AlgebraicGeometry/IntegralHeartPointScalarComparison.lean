/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralHeartLocalModelData
public import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModelResolutionSupplement
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModelResolutionSupplement
import all Mathlib.Algebra.Module.FinitePresentation
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal

/-! # Comparing the two specified point scalar realizations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale

/-- Ordinary continuous scalar realization with the scalar ring lifted to the module universe.
Source: the scalar matrices in integral-heart-local-model, clause (1)
(blueprint: lem-sfb-integral-heart-point-scalar-comparison). -/
def integralHeartContinuousRealization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E) ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (SmallAdicCompletion.Coefficients.integerRing ℓ E) :=
  letI := SmallAdicCompletion.Coefficients.fieldNorm.{u} ℓ E
  ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : integralHeartScalars.{u} ℓ E ≃+*
        SmallAdicCompletion.Coefficients.integers.{u} ℓ E).symm.toRingHom ⋙
    continuousScalarFunctor (SmallAdicCompletion.Coefficients.integers.{u} ℓ E)

/-- Additivity follows from finite-colimit preservation of continuous scalar extension.
Source: Stacks Tag 03EK (blueprint: lem-sfb-integral-heart-point-scalar-comparison). -/
instance integralHeartContinuousRealization_additive (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    (integralHeartContinuousRealization.{u} ℓ E).Additive := by
  let := SmallAdicCompletion.Coefficients.fieldNorm.{u} ℓ E
  let A := SmallAdicCompletion.Coefficients.integers.{u} ℓ E
  have : PreservesFiniteColimits (continuousScalarFunctor A) :=
    ContinuousScalarPresentation.continuous_colimits A
  have : PreservesBinaryBiproducts (continuousScalarFunctor A) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (continuousScalarFunctor A).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  change (ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : integralHeartScalars.{u} ℓ E ≃+* A).symm.toRingHom ⋙
      continuousScalarFunctor A).Additive
  infer_instance


namespace IntegralHeartScalarComparison
private def scalarForward (A : Type u) [CommRing A] :
    ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
      Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A)) :=
  ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom ⋙
      FiniteConstantModel.scalarModules A

@[instance_reducible] private def scalarOrdinaryModule (A : Type u) [CommRing A]
    (M : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A))) :
    Module (ULift.{u + 1} A) M.X where
  smul a x := (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} A)) M.X).hom (a ⊗ₜ[ℤ] x)
  one_smul x := by
    have h := ConcreteCategory.congr_hom
      (Mod.one_act (A := AddCommGrpCat.of (ULift.{u + 1} A)) M.X)
      (ULift.up (1 : ℤ) ⊗ₜ[ℤ] x)
    change (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} A)) M.X).hom
      ((MonObj.one ▷ M.X).hom (ULift.up 1 ⊗ₜ[ℤ] x)) =
        ((λ_ M.X).hom).hom (ULift.up 1 ⊗ₜ[ℤ] x) at h
    rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul,
      AddCommGrpCat.MonoidalCategory.leftUnitor_hom_tmul] at h
    rw [AddCommGrpCat.ringMonObj_one_apply] at h
    change (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} A)) M.X).hom
      ((1 : ULift.{u + 1} A) ⊗ₜ[ℤ] x) = x
    simpa only [Int.cast_one, one_smul] using h
  mul_smul a b x := ConcreteCategory.congr_hom
    (Mod.mul_act (A := AddCommGrpCat.of (ULift.{u + 1} A)) M.X)
      ((a ⊗ₜ[ℤ] b) ⊗ₜ[ℤ] x)
  smul_zero a := by
    change (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} A)) M.X).hom (a ⊗ₜ[ℤ] 0) = 0
    simp
  smul_add a x y := by
    change (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} A)) M.X).hom
      (a ⊗ₜ[ℤ] (x + y)) = _
    rw [TensorProduct.tmul_add, map_add]
    rfl
  zero_smul x := by
    change (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} A)) M.X).hom (0 ⊗ₜ[ℤ] x) = 0
    simp
  add_smul a b x := by
    change (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} A)) M.X).hom
      ((a + b) ⊗ₜ[ℤ] x) = _
    rw [TensorProduct.add_tmul, map_add]
    rfl

private def scalarInverse (A : Type u) [CommRing A] :
    Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A)) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} A) where
  obj M :=
    letI := scalarOrdinaryModule A M
    ModuleCat.of (ULift.{u + 1} A) M.X
  map {M N} f := by
    letI := scalarOrdinaryModule A M
    letI := scalarOrdinaryModule A N
    exact ModuleCat.ofHom
      { toFun := f.hom
        map_add' := map_add f.hom.hom
        map_smul' := fun a x ↦
          ConcreteCategory.congr_hom (Mod.act_hom f) (a ⊗ₜ[ℤ] x) }

private def scalarEquivalence (A : Type u) [CommRing A] :
    ModuleCat.{u + 1} (ULift.{u + 1} A) ≌
      Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} A)) :=
  CategoryTheory.Equivalence.mk (scalarForward A) (scalarInverse A)
    (NatIso.ofComponents (fun M ↦ ModuleCat.isoMk (Iso.refl _) (by
      intro a
      ext x
      rfl)) (by intros; ext x; rfl))
    (NatIso.ofComponents (fun M ↦ Mod.isoMk (Iso.refl _) (by
      apply AddCommGrpCat.hom_ext_toIntLinearMap
      apply TensorProduct.ext'
      intro a x
      rfl)) (by intros; apply Mod.hom_ext; rfl))

private def constantPresheafAdjunction
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    integralHeartConstantPresheaf.{u} ℓ E ⊣
      PresheafOfModules.evaluation
        ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (integralHeartScalars.{u} ℓ E)))
        (op (Profinite.of PUnit.{u + 1})) := by
  let T : Profinite.{u} := Profinite.of PUnit.{u + 1}
  let hT : IsTerminal T := Profinite.isTerminalPUnit
  let he (M : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E))
      (P : PresheafOfModules.{u + 1}
        ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (integralHeartScalars.{u} ℓ E)))) :
      ((integralHeartConstantPresheaf.{u} ℓ E).obj M ⟶ P) ≃ (M ⟶ P.obj (op T)) :=
    { toFun f := f.app (op T)
      invFun f :=
        { app U := f ≫ P.map (hT.from U.unop).op
          naturality := by
            intro U V i
            ext x
            change P.map (hT.from V.unop).op (f x) =
              P.map i (P.map (hT.from U.unop).op (f x))
            rw [← P.map_comp_apply]
            congr 2 }
      left_inv f := by
        ext U x
        exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op x).symm
      right_inv f := by
        ext x
        have h : hT.from T = 𝟙 T := hT.hom_ext _ _
        change P.map (hT.from T).op (f x) = f x
        rw [h]
        exact ConcreteCategory.congr_hom (P.map_id (op T)) (f x) }
  exact Adjunction.mkOfHomEquiv
    { homEquiv := he
      homEquiv_naturality_left_symm := by intros; ext U x; rfl
      homEquiv_naturality_right := by intros; rfl }

private def extensionRawIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (M : integralHeartConstantModules.{u} ℓ E) :
    SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M ≅
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (integralHeartScalarMap.{u} ℓ E) M := by
  refine PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) ?_
  intro U V f
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact (SheafOfModules.changeOfRingsMap_tmulOfUniverses.{u, u + 1, u + 1, u + 1}
    (integralHeartScalarMap ℓ E) M f 1 m).trans
      (SheafOfModules.CoefficientOrdinaryProof.tensorRestriction_tmul.{u + 1, u + 1, u}
        (integralHeartScalarMap ℓ E) M f 1 m).symm

private def extensionIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    integralHeartExtension.{u} ℓ E ≅
      SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{u + 1, u + 1, u}
        (integralHeartScalarMap.{u} ℓ E) := by
  let L := PresheafOfModules.sheafification.{u + 1} (𝟙 (integralHeartPointRing.{u} ℓ E).obj)
  refine NatIso.ofComponents (fun M ↦ L.mapIso (extensionRawIso ℓ E M)) ?_
  intro M N f
  change L.map _ ≫ L.map _ = L.map _ ≫ L.map _
  rw [← L.map_comp, ← L.map_comp]
  congr 1

attribute [local instance] Sheaf.monoidalCategory
private instance evaluationMonoidal {C D : Type*} [Category C] [Category D]
    [MonoidalCategory D] (U : C) : ((evaluation C D).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

private noncomputable instance sectionsMonoidal :
    ((sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (op (Profinite.of PUnit.{u + 1}))).LaxMonoidal :=
  inferInstanceAs (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
    (evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj
      (op (Profinite.of PUnit.{u + 1}))).LaxMonoidal

private instance constantPresheafAdj_monoidal :
    (constantPresheafAdj Ab.{u + 1} (Profinite.isTerminalPUnit)).IsMonoidal := by
  constructor
  · simp [constantPresheafAdj, Functor.LaxMonoidal.ε, Functor.OplaxMonoidal.η]
  · intro X Y
    simp [constantPresheafAdj, Functor.LaxMonoidal.μ, Functor.OplaxMonoidal.δ]

private instance constantSheafAdj_monoidal :
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).IsMonoidal := by
  unfold constantSheafAdj
  infer_instance

end IntegralHeartScalarComparison

set_option maxHeartbeats 2000000 in
-- Composing the module adjunctions compares several large concrete realization functors.
/-- Sheafified tensor scalar realization agrees naturally with the internal continuous
scalar extension, with the same constant scalar action.
Source: blueprint latest, integral-heart-local-model, clause (1); Stacks Tags 03EK and 093J
(blueprint: lem-sfb-integral-heart-point-scalar-comparison).

Proof: maps from either realization of M to an internal coefficient module N correspond
to scalar-linear maps from M to its sections on the one-point profinite set. For the first
realization, use the section-module equivalence, the tensor/restriction adjunction, and
constant-module sheafification. For continuous realization use internal scalar extension,
constant abelian sheafification, and the equivalence between ordinary modules and internal
modules in abelian groups. In both cases a scalar a acts by its constant continuous function,
by the sheafification adjunction defining the scalar maps. The identity on these Hom sets
is natural in M and N. Uniqueness of representing objects gives the stated natural
isomorphism. This argument includes the zero module and needs no finiteness assumption. -/
theorem integralHeart_pointScalar_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    Nonempty (integralHeartContinuousRealization.{u} ℓ E ≅
      integralHeartPointRealization.{u} ℓ E) := by
  classical
  let := SmallAdicCompletion.Coefficients.fieldNorm.{u} ℓ E
  let A := SmallAdicCompletion.Coefficients.integers.{u} ℓ E
  let J := coherentTopology Profinite.{u}
  let B : Ab.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} A)
  let Λ := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let F := constantSheaf J Ab.{u + 1}
  let adj := constantSheafAdj J Ab.{u + 1} Profinite.isTerminalPUnit
  let e := IntegralHeartScalarComparison.scalarEquivalence A
  let Rn := Mod.comap (FiniteConstantModel.scalarToContinuous A) ⋙
    (((sheafSections J Ab.{u + 1}).obj (op (Profinite.of PUnit.{u + 1}))).mapMod
      (F.obj B) ⋙ Mod.comap (adj.unitAlgHom B)) ⋙ e.inverse
  have an : integralHeartContinuousRealization.{u} ℓ E ⊣ Rn :=
    (e.toAdjunction.comp (adj.mapModAdjunction B)).comp
      (Mod.extendRestrictAdjunction (FiniteConstantModel.scalarToContinuous A))
  let eqv := InternalAbelianSheafModule.sectionModuleEquivalence J Λ
  let r := SheafOfModules.CoefficientOrdinaryProof.restriction.{u + 1, u + 1, u, u + 1}
    (integralHeartScalarMap.{u} ℓ E)
  let Rp := ((eqv.functor ⋙ r) ⋙
    (SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars (integralHeartConstantUnit.{u} ℓ E))) ⋙
    PresheafOfModules.evaluation
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (integralHeartScalars.{u} ℓ E)))
      (op (Profinite.of PUnit.{u + 1}))
  have ae : integralHeartExtension.{u} ℓ E ⊣ r :=
    (SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction.{u + 1, u + 1, u}
      (integralHeartScalarMap.{u} ℓ E)).ofNatIsoLeft
        (IntegralHeartScalarComparison.extensionIso ℓ E).symm
  -- Associate the left functors as in the specified realization, to keep elaboration small.
  let tailAdj := ae.comp eqv.symm.toAdjunction
  let middleAdj := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (integralHeartConstantUnit.{u} ℓ E)).comp tailAdj
  have ap : integralHeartPointRealization.{u} ℓ E ⊣ Rp :=
    (IntegralHeartScalarComparison.constantPresheafAdjunction ℓ E).comp middleAdj
  have scalar_eq (U : Profinite.{u}ᵒᵖ) (a : integralHeartScalars.{u} ℓ E) :
      (integralHeartScalarMap.{u} ℓ E).hom.app U
        ((integralHeartConstantUnit.{u} ℓ E).app U a) =
      (FiniteConstantModel.scalarToContinuous A).hom.app U
        ((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj B)).app U a) := by
    have h₁ := Equiv.apply_symm_apply
      ((CategoryTheory.sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv
        ((Functor.const Profinite.{u}ᵒᵖ).obj
          (CommRingCat.of (integralHeartScalars.{u} ℓ E)))
        (InternalAbelianSheafModule.sectionRingSheaf J Λ))
      (integralHeartConstantMap.{u} ℓ E)
    have h₂ := Equiv.apply_symm_apply
      ((CategoryTheory.sheafificationAdjunction J Ab.{u + 1}).homEquiv
        ((Functor.const Profinite.{u}ᵒᵖ).obj B) Λ)
      (FiniteConstantModel.constantFunctions A)
    exact (ConcreteCategory.congr_hom (congr_app h₁ U) a).trans
      (ConcreteCategory.congr_hom (congr_app h₂ U) a).symm
  let T : Profinite.{u}ᵒᵖ := op (Profinite.of PUnit.{u + 1})
  let G := (sheafSections J Ab.{u + 1}).obj T
  let φ := FiniteConstantModel.scalarToContinuous A
  let ψ := adj.unitAlgHom B ≫ G.map φ
  let Rn' := G.mapMod Λ ⋙ Mod.comap ψ ⋙ e.inverse
  let adjust : Rn ≅ Rn' := NatIso.ofComponents (fun N ↦ e.inverse.mapIso
    ((Mod.comap (adj.unitAlgHom B)).mapIso ((G.mapModComapIso φ).app N) ≪≫
      (Mod.comapComp (adj.unitAlgHom B) (G.map φ)).symm.app ((G.mapMod Λ).obj N))) (by
        intro M N f
        ext x
        rfl)
  let comparison' : Rn' ≅ Rp := NatIso.ofComponents (fun N ↦
    ModuleCat.isoMk (Iso.refl _) (by
      intro a
      ext x
      symm
      change (Mod.act ((G.mapMod Λ).obj N).X).hom ((ψ.hom a) ⊗ₜ[ℤ] x) =
        (Mod.act ((G.mapMod Λ).obj N).X).hom
          (((integralHeartScalarMap.{u} ℓ E).hom.app T
            ((integralHeartConstantUnit.{u} ℓ E).app T a)) ⊗ₜ[ℤ] x)
      have h := scalar_eq T a
      change _ = ψ.hom a at h
      exact congrArg
        (fun r ↦ (Mod.act ((G.mapMod Λ).obj N).X).hom (r ⊗ₜ[ℤ] x)) h.symm)) (by
        intro M N f
        ext x
        rfl)
  let comparison := adjust ≪≫ comparison'
  exact ⟨(an.ofNatIsoRight comparison).leftAdjointUniq ap⟩

end AlgebraicGeometry.ProEtale
