/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralHeartLocalModelData
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.AlgebraicGeometry.IntegralHeartSectionExtension
import WeilConjectures.AlgebraicGeometry.IntegralHeartSectionFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-!
# Exactness and finite free terms of completed scalar realization

Source: blueprint latest, `sec-six-functors-basics/sk-lem-int-integral-heart/`,
`sk-lem-int-integral-heart-dualizable.proof.md`, first two sentences;
Stacks Project, Tags 0AUW, 093J and 093M
(blueprint: lem-integral-heart-realization-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.InternalAbelianSheafModule
open PresheafOfModules.IntegralHeart
open scoped ChangeOfRings CategoryTheory.Obj

private noncomputable abbrev directIntegralPresheaf
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :=
  integralHeartConstantPresheaf.{u} ℓ E ⋙
    sectionExtension.{u + 1, u, u + 1} (integralHeartConstantMap.{u} ℓ E)

private noncomputable abbrev directIntegralSheaf
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :=
  directIntegralPresheaf.{u} ℓ E ⋙ PresheafOfModules.sheafification
    (R := integralHeartPointRing.{u} ℓ E) (𝟙 _)

private noncomputable def integralExtensionIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    integralHeartExtension.{u} ℓ E ≅
      sheafSectionExtension.{u + 1, u, u + 1} (integralHeartScalarMap.{u} ℓ E) := by
  let L := PresheafOfModules.sheafification (R := integralHeartPointRing.{u} ℓ E) (𝟙 _)
  refine NatIso.ofComponents
    (fun M ↦ L.mapIso (rawComparison.{u + 1, u, u + 1} (integralHeartScalarMap.{u} ℓ E) M)) ?_
  intro M N f
  change L.map _ ≫ L.map (rawComparison _ N).hom =
    L.map (rawComparison _ M).hom ≫ L.map _
  rw [← L.map_comp, ← L.map_comp]
  congr 1

private theorem integralScalarMap_fac
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    toSheafify (coherentTopology Profinite.{u})
        ((Functor.const Profinite.{u}ᵒᵖ).obj
          (CommRingCat.of (integralHeartScalars.{u} ℓ E))) ≫
      (integralHeartScalarMap.{u} ℓ E).hom = integralHeartConstantMap.{u} ℓ E := by
  let adj := CategoryTheory.sheafificationAdjunction
    (coherentTopology Profinite.{u}) CommRingCat.{u + 1}
  exact Equiv.apply_symm_apply (adj.homEquiv
    ((Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of (integralHeartScalars.{u} ℓ E)))
    (sectionRingSheaf (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)))
    (integralHeartConstantMap.{u} ℓ E)

private noncomputable def integralSectionIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    integralHeartConstantPresheaf.{u} ℓ E ⋙
      PresheafOfModules.sheafification
        (R := (sheafCompose (coherentTopology Profinite.{u})
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (integralHeartConstantRing.{u} ℓ E)) (integralHeartConstantUnit.{u} ℓ E) ⋙
        integralHeartExtension.{u} ℓ E ≅ directIntegralSheaf.{u} ℓ E := by
  let η := toSheafify (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj
      (CommRingCat.of (integralHeartScalars.{u} ℓ E)))
  have : Presheaf.IsLocallyInjective (coherentTopology Profinite.{u})
      (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    integralHeartConstantUnit_isLocallyInjective.{u} ℓ E
  have : Presheaf.IsLocallySurjective (coherentTopology Profinite.{u})
      (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) :=
    integralHeartConstantUnit_isLocallySurjective.{u} ℓ E
  let e := sheafificationSectionExtensionIso.{u + 1, u, u + 1} (integralHeartScalarMap.{u} ℓ E) η
  have he : η ≫ (integralHeartScalarMap.{u} ℓ E).hom =
      integralHeartConstantMap.{u} ℓ E := integralScalarMap_fac ℓ E
  refine Functor.isoWhiskerLeft (integralHeartConstantPresheaf.{u} ℓ E)
    (Functor.isoWhiskerLeft (PresheafOfModules.sheafification
        (R := (sheafCompose (coherentTopology Profinite.{u})
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (integralHeartConstantRing.{u} ℓ E)) (integralHeartConstantUnit.{u} ℓ E))
      (integralExtensionIso ℓ E) ≪≫ e) ≪≫ ?_
  exact eqToIso (by dsimp [directIntegralSheaf, directIntegralPresheaf]; rw [he]; rfl)

private theorem directIntegralSheaf_exact
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    PreservesFiniteLimits (directIntegralSheaf.{u} ℓ E) ∧
      PreservesFiniteColimits (directIntegralSheaf.{u} ℓ E) := by
  have hL : PreservesFiniteLimits (directIntegralPresheaf.{u} ℓ E) := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ ?_⟩
    intro U
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (integralHeartConstantMap_flat.{u} ℓ E U)
    exact isLimitOfPreserves
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        ((integralHeartConstantMap.{u} ℓ E).app U).hom) hc
  have hC : PreservesFiniteColimits (directIntegralPresheaf.{u} ℓ E) := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ ?_⟩
    intro U
    have := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      ((integralHeartConstantMap.{u} ℓ E).app U).hom).leftAdjoint_preservesColimits
    exact isColimitOfPreserves
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        ((integralHeartConstantMap.{u} ℓ E).app U).hom) hc
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

private noncomputable def directIntegralUnitRawIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    (directIntegralPresheaf.{u} ℓ E).obj
        (ModuleCat.of (integralHeartScalars.{u} ℓ E) (integralHeartScalars.{u} ℓ E)) ≅
      (SheafOfModules.unit (integralHeartPointRing.{u} ℓ E)).val := by
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · exact (Functor.Monoidal.εIso
      (ModuleCat.extendScalars ((integralHeartConstantMap.{u} ℓ E).app U).hom)).symm
  · intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro a
    change Functor.OplaxMonoidal.η
        (ModuleCat.extendScalars ((integralHeartConstantMap.{u} ℓ E).app V).hom)
        (((sectionExtension.{u + 1, u, u + 1} (integralHeartConstantMap.{u} ℓ E)).obj
          ((integralHeartConstantPresheaf.{u} ℓ E).obj
            (ModuleCat.of (integralHeartScalars.{u} ℓ E)
              (integralHeartScalars.{u} ℓ E)))).map i
            ((1 : (integralHeartPointRing.{u} ℓ E).obj.obj U)
            ⊗ₜ[integralHeartScalars.{u} ℓ E,
              ((integralHeartConstantMap.{u} ℓ E).app U).hom] a)) = _
    erw [sectionExtension_map_tmul.{u + 1, u, u + 1}
      (integralHeartConstantMap.{u} ℓ E)
      ((integralHeartConstantPresheaf.{u} ℓ E).obj
        (ModuleCat.of (integralHeartScalars.{u} ℓ E) (integralHeartScalars.{u} ℓ E))) i 1 a]
    simp only [map_one]
    change (integralHeartConstantMap.{u} ℓ E).app V a * 1 =
      (sectionRingSheaf (coherentTopology Profinite.{u})
        (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)).obj.map i
        ((integralHeartConstantMap.{u} ℓ E).app U a * 1)
    simp only [mul_one]
    exact ConcreteCategory.congr_hom ((integralHeartConstantMap.{u} ℓ E).naturality i) a

private noncomputable def directIntegralUnitIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    (directIntegralSheaf.{u} ℓ E).obj
        (ModuleCat.of (integralHeartScalars.{u} ℓ E) (integralHeartScalars.{u} ℓ E)) ≅
      SheafOfModules.unit (integralHeartPointRing.{u} ℓ E) :=
  (PresheafOfModules.sheafification (R := integralHeartPointRing.{u} ℓ E) (𝟙 _)).mapIso
      (directIntegralUnitRawIso ℓ E) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := integralHeartPointRing.{u} ℓ E) (𝟙 _)).counit).app
        (SheafOfModules.unit (integralHeartPointRing.{u} ℓ E))

private noncomputable def integralRegularSectionIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    (sectionModuleEquivalence (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)).functor.obj
        (Mod.regular (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)) ≅
      SheafOfModules.unit (integralHeartPointRing.{u} ℓ E) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun _ ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    apply ConcreteCategory.hom_ext
    intro m
    rfl
  · intro U V i
    ext
    rfl

private noncomputable def integralRealizationUnitIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u}) :
    (integralHeartRealization.{u} ℓ E X).obj
        (ModuleCat.of (integralHeartScalars.{u} ℓ E) (integralHeartScalars.{u} ℓ E)) ≅
      𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) X)) := by
  let e := sectionModuleEquivalence (coherentTopology Profinite.{u})
    (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)
  let A := ModuleCat.of (integralHeartScalars.{u} ℓ E) (integralHeartScalars.{u} ℓ E)
  let h := (integralSectionIso.{u} ℓ E).app A ≪≫ directIntegralUnitIso ℓ E
  let h' := e.inverse.mapIso (h ≪≫ (integralRegularSectionIso ℓ E).symm) ≪≫
    (e.unitIso.app (Mod.regular (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E))).symm
  exact ((upperStarFromPoint X).mapMod
    (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)).mapIso h' ≪≫
      SmallAdicCompletion.Coefficients.regularPullbackIso ℓ E X

/-- Completed scalar realization is exact and sends every finite free scalar module
into a dualizable completed coefficient module sheaf.

Source: blueprint latest, integral-heart-dualizable, proof, first two sentences
(blueprint: lem-integral-heart-realization-exact).

Proof: (1) By lem-weil-l-adic-extension-integers-dvr, the small integer ring is a
DVR and hence a PID; transport this along ULift.ringEquiv to integralHeartScalars.
By def-weil-pbc-internal-abelian-sheaf-module-equivalence, each reconstructed
section ring on a profinite U is ULift C(U,O), with pointwise multiplication and
constant scalar action. A nonzero scalar cannot annihilate a nonzero function,
as is seen by evaluation at every point. Thus these modules are torsion-free,
and therefore flat over the DVR. This also covers empty U, whose module is zero.
(2) Sheafify U ↦ R(U) tensor_A M. The tensor and sheafification adjunctions
identify this functor naturally with integralHeartPointRealization of
def-sfb-integral-heart-local-model-data: both Hom bijections evaluate at
1 tensor m, and their naturality follows from the sheafification-unit squares.
Use uniqueness of left adjoints for the comparison. Sectionwise flat scalar
extension preserves finite limits and colimits, as does sheafification, so
the comparison gives exactness on the point.
(3) The section-module equivalence and inverse image from the point are exact,
giving exactness on X. Sectionwise, R(U) tensor_A A ≅ R(U) by s tensor a ↦ s*a
with inverse s ↦ s tensor 1. Sheafification, the section-module equivalence and
regularPullbackIso identify the realized rank-one module with the tensor unit.
Finite-biproduct preservation identifies the realization of A^(Fin n) with the
biproduct of n copies of the unit. The proved isDualizable_biproduct_unit gives
dualizability for every n, including n=0. -/
theorem integralHeartRealization_exact_free
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u}) :
    PreservesFiniteLimits (integralHeartRealization.{u} ℓ E X) ∧
    PreservesFiniteColimits (integralHeartRealization.{u} ℓ E X) ∧
    ∀ n : ℕ, IsDualizable ((integralHeartRealization.{u} ℓ E X).obj
      (ModuleCat.of (integralHeartScalars.{u} ℓ E)
        (Fin n → integralHeartScalars.{u} ℓ E))) := by
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteColimits pointUpperStar.{u} := by
    have : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have := (directIntegralSheaf_exact.{u} ℓ E).1
  have := (directIntegralSheaf_exact.{u} ℓ E).2
  let e := Functor.isoWhiskerRight (integralSectionIso.{u} ℓ E)
    (sectionModuleEquivalence (coherentTopology Profinite.{u})
      (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)).inverse
  have : PreservesFiniteLimits (integralHeartPointRealization.{u} ℓ E) :=
    preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (integralHeartPointRealization.{u} ℓ E) :=
    preservesFiniteColimits_of_natIso e.symm
  have hL : PreservesFiniteLimits (integralHeartRealization.{u} ℓ E X) :=
    comp_preservesFiniteLimits _ _
  have hC : PreservesFiniteColimits (integralHeartRealization.{u} ℓ E X) :=
    comp_preservesFiniteColimits _ _
  refine ⟨hL, hC, ?_⟩
  intro n
  let F := integralHeartRealization.{u} ℓ E X
  let A := ModuleCat.of (integralHeartScalars.{u} ℓ E) (integralHeartScalars.{u} ℓ E)
  let j := F.mapIso (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ A)).symm ≪≫
    F.mapBiproduct (fun _ : Fin n ↦ A) ≪≫
      biproduct.mapIso (fun _ : Fin n ↦ integralRealizationUnitIso ℓ E X)
  exact IsDualizable.of_iso j.symm (isDualizable_biproduct_unit n)

end AlgebraicGeometry.ProEtale
