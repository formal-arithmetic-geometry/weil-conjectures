/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.Paper.FiniteConstantModelResolution
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.Paper.CompletedConstantSheafReduction
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import all Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
import Sheaf.Paper.CompactAdicContinuousIdentification
import Sheaf.NumberTheory.Padics.IntegersCosetBasis
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Field.ULift
import all Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
import Sheaf.Paper.ContinuousCoefficientModuleEncoding
import Sheaf.Paper.ConstantToContinuousScalarFlat
import Sheaf.CategoryTheory.InternalSectionModuleFlat
import all Sheaf.Paper.CompletedConstantAlgebraFlatQuotients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-!
# Exact scalar realization for admissible continuous coefficients

Source: Stacks Project, Modules on Sites, Tags 093J and 093M; blueprint main-20261015,
internal-Hom stability proof, paragraphs 2--3
(blueprint: lem-sfb-admissible-scalar-realization-exact).

The scalar realization is the existing `FiniteConstantModel.modelFunctor`. The algebraic
closure below uses all continuous functions. Universe lifts of the three standard scalar
rings carry their induced topologies and do not change their rings or sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.MonObj
open scoped TensorProduct Topology

namespace AlgebraicGeometry.ProEtale.AdmissibleScalarRealization

open FiniteConstantModel

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Restrict the actual realized module sheaf to the localized site over `U`.
Source: Stacks 00Y0, localization, and 093J, constant modules
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def localizedModel (T : Scheme.{u}) (U : T.ProEt) :=
  modelFunctor A T ⋙
    InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ⋙
    SheafOfModules.overFunctor _ U

/-- Noetherian scalars, additive exact realization on all scalar modules, and the same
assertion for the actual restricted coefficient sheaf on every localized site.
Source: Stacks 093J and 093M and the field split-sequence argument
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def ScalarAssertions (T : Scheme.{u}) : Prop :=
  IsNoetherianRing A ∧ (modelFunctor A T).Additive ∧
    PreservesFiniteLimits (modelFunctor A T) ∧
    PreservesFiniteColimits (modelFunctor A T) ∧
    ∀ U : T.ProEt, (localizedModel A T U).Additive ∧
      PreservesFiniteLimits (localizedModel A T U) ∧
      PreservesFiniteColimits (localizedModel A T U)

/-- The pulled-back canonical scalar map, with domain `p_T^*` of the constant scalar ring.
The canonical `constantSchemeIso` identifies its domain with the constant ring on `T`.
Source: Stacks 093J, constant functions
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
abbrev scalarMap (T : Scheme.{u}) :
    (upperStarFromPoint T).obj
      ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A))) ⟶
      condensedRingObj (Profinite.continuousCoefficientRingObj A) T :=
  (upperStarFromPoint T).map (scalarToContinuous A)

/-- The actual completed coefficient assertion: an isomorphism of ring sheaves with the
positive constant quotient tower, and flatness over constant scalars on all sheaf modules,
also on every localized site. Here `p` is the specified uniformizer.
Source: Stacks 093M and the integral coefficient limit comparison
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def CompletedIdentification (T : Scheme.{u}) (p : A) : Prop :=
  (∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ≅
    Scheme.adicLisseCompletedRing T
      (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))),
    ∀ (U : T.ProEtᵒᵖ) (a : A) (n : ℕ),
      ((limit.π (Scheme.adicLisseRingSystem T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)))) (op n)).hom.app U)
        ((e.hom.hom.app U)
          ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
            ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
                (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A)))).app U (ULift.up a)))) =
      (toSheafify (D := CommRingCat.{u + 1}) (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} A ⧸
            (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))))).app U
          (Ideal.Quotient.mk
            ((Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))
            (ULift.up a)))

/-- Flatness of the actual restricted coefficient module on every localized site.
Source: Stacks 093M and 00Y0
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def LocalizedFlatness (T : Scheme.{u}) : Prop :=
  ∀ U : T.ProEt, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
    (R := (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      ((upperStarFromPoint T).obj
        ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
          (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A))))).over U)
    (((InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology T)
      ((upperStarFromPoint T).obj
        ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
          (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A))))).obj
      ((Mod.comap (scalarMap A T)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj A) T)))).over U)

/-- The completed identification and exact tensor extension on all sheaf modules.
Source: Stacks 093M
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def CompletedAssertions (T : Scheme.{u}) (p : A) : Prop :=
  CompletedIdentification A T p ∧
    PreservesFiniteLimits (Mod.extendScalars (scalarMap A T)) ∧
    PreservesFiniteColimits (Mod.extendScalars (scalarMap A T)) ∧
    LocalizedFlatness A T

/-- Integral extension scalars have their spectral absolute value topology.
Source: blueprint internal-Hom proof paragraphs 2--3 and Stacks 093M
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def IntegralAssertions (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (T : Scheme.{u}) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  ScalarAssertions (Padic.coefficientExtensionIntegers ℓ E) T ∧
    ∀ π : Padic.coefficientExtensionIntegers ℓ E,
      Ideal.span ({π} : Set (Padic.coefficientExtensionIntegers ℓ E)) =
        Padic.coefficientExtensionMaximalIdeal ℓ E →
      CompletedAssertions (Padic.coefficientExtensionIntegers ℓ E) T π

/-- Rational extension scalars retain the topology of their spectral absolute value.
Source: blueprint internal-Hom proof paragraphs 2--3, field case
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def RationalAssertions (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (T : Scheme.{u}) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  ScalarAssertions E T

omit [TopologicalSpace A] [IsTopologicalRing A] in
private lemma scalarModules_preservesFiniteLimits :
    PreservesFiniteLimits (scalarModules A) := by
  have : PreservesFiniteLimits (scalarModules A ⋙
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A))) :=
    inferInstanceAs (PreservesFiniteLimits (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A)))

omit [TopologicalSpace A] [IsTopologicalRing A] in
private lemma scalarModules_preservesFiniteColimits :
    PreservesFiniteColimits (scalarModules A) := by
  let V : ModuleCat.{u + 1} A ⥤ Ab.{u + 1} := forget₂ _ _
  have : PreservesColimitsOfSize.{0, 0} V := by
    exact ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u, 0, 0} A
  have : PreservesFiniteColimits V := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits (scalarModules A ⋙
      Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A))) :=
    inferInstanceAs (PreservesFiniteColimits V)
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (Mod.forget (AddCommGrpCat.of (ULift.{u + 1} A)))


private lemma modelFunctor_exact (T : Scheme.{u})
    (hflat : PreservesFiniteLimits (Mod.extendScalars (scalarToContinuous A))) :
    PreservesFiniteLimits (modelFunctor A T) ∧
      PreservesFiniteColimits (modelFunctor A T) ∧ (modelFunctor A T).Additive := by
  let : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteColimits pointUpperStar.{u} := by
    have : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint T) := by
    dsimp [upperStarFromPoint]; infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint T) := by
    dsimp [upperStarFromPoint]; infer_instance
  have : PreservesFiniteLimits (scalarModules A) := scalarModules_preservesFiniteLimits A
  have : PreservesFiniteColimits (scalarModules A) := scalarModules_preservesFiniteColimits A
  have : PreservesFiniteLimits (Mod.extendScalars (scalarToContinuous A)) := hflat
  have : PreservesFiniteLimits
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits
      ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A))) := by
    infer_instance
  have : PreservesFiniteLimits
      ((upperStarFromPoint T).mapMod (Profinite.continuousCoefficientRingObj A)) := by
    infer_instance
  have hlim : PreservesFiniteLimits (modelFunctor A T) := by
    unfold modelFunctor
    infer_instance
  have hcolim : PreservesFiniteColimits (modelFunctor A T) := by
    dsimp [modelFunctor]
    infer_instance
  exact ⟨hlim, hcolim, rightExactFunctor_le_additiveFunctor _ _ _ (by
    rw [rightExactFunctor_iff]
    infer_instance)⟩

private theorem scalar_assertions (T : Scheme.{u}) [IsNoetherianRing A]
    (hflat : PreservesFiniteLimits (Mod.extendScalars (scalarToContinuous A))) :
    ScalarAssertions A T := by
  obtain ⟨hl, hc, ha⟩ := modelFunctor_exact A T hflat
  let := hl
  let := hc
  let := ha
  refine ⟨inferInstance, ha, hl, hc, ?_⟩
  intro U
  let R := condensedRingObj (Profinite.continuousCoefficientRingObj A) T
  have : IsCommMonObj R := inferInstance
  have : (InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) R).IsEquivalence :=
    inferInstanceAs ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) R).functor.IsEquivalence)
  have : (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) R)) U).IsLeftAdjoint := by
    dsimp [SheafOfModules.overFunctor]
    infer_instance
  let O := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) R)
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{u + 1} O U ⋙
      SheafOfModules.toSheaf.{u + 1} (O.over U)) := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} O ⋙
      (Scheme.ProEt.topology T).overPullback Ab.{u + 1} U)
    infer_instance
  have : PreservesFiniteLimits (SheafOfModules.overFunctor.{u + 1} O U) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf (O.over U))
  have hll : PreservesFiniteLimits (localizedModel A T U) := by
    dsimp [localizedModel]
    infer_instance
  have hcc : PreservesFiniteColimits (localizedModel A T U) := by
    dsimp [localizedModel]
    infer_instance
  exact ⟨rightExactFunctor_le_additiveFunctor _ _ _ (by
    rw [rightExactFunctor_iff]
    exact hcc), hll, hcc⟩

private theorem pid_scalar_assertions [IsDomain A] [IsPrincipalIdealRing A]
    (T : Scheme.{u}) : ScalarAssertions A T := by
  apply scalar_assertions A T
  apply constantToContinuous_preservesFiniteLimits A (scalarToContinuous A)
  intro S a
  have h := ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
    ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))
    (Profinite.continuousCoefficientRingObj A)).apply_symm_apply (constantFunctions A)
  exact ConcreteCategory.congr_hom (congr_app h S) a

private local instance constantFunctions_locallySurjective [Finite A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u}) (constantFunctions A) where
  imageSieve_mem {S} s := by
    let f : C(S, A) := s.down
    have hclosed (a : A) : IsClosed {x : S | f x = a} :=
      isClosed_singleton.preimage f.continuous
    let (a : A) : CompactSpace {x : S // f x = a} :=
      isCompact_iff_compactSpace.mp (hclosed a).isCompact
    let := Fintype.ofFinite A
    let e := (Fintype.equivFin A).symm
    let U (i : Fin (Fintype.card A)) : Profinite.{u} :=
      Profinite.of {x : S // f x = e i}
    let incl (i : Fin (Fintype.card A)) : U i ⟶ S :=
      CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl :=
      Profinite.effectiveEpiFamily_of_jointly_surjective U incl
        (fun x ↦ ⟨e.symm (f x), ⟨x, (e.apply_symm_apply (f x)).symm⟩, rfl⟩)
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨Fin (Fintype.card A), inferInstance, U, incl, hι, ?_⟩
    intro i
    refine ⟨ULift.up (e i), ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

private local instance constantFunctions_locallyInjective :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u}) (constantFunctions A) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (ULift.ext a b (congrArg
        (fun t : ULift.{u + 1} C(S.unop, A) ↦ t.down x) h))⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

private theorem finite_scalar_iso [Finite A] [DiscreteTopology A] :
    IsIso (scalarToContinuous A) := by
  let J := coherentTopology Profinite.{u}
  have hφ : J.W (A := Ab.{u + 1}) (constantFunctions A) :=
    J.W_of_isLocallyBijective (constantFunctions A)
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map (constantFunctions A)) :=
    (J.W_iff _).mp hφ
  unfold scalarToContinuous
  rw [Adjunction.homEquiv_counit]
  infer_instance

private theorem finite_scalar_assertions [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) : ScalarAssertions A T ∧
    IsIso (FiniteDiscreteOrdinary.canonicalAbelianMap A T) := by
  have : IsIso (scalarToContinuous A) := finite_scalar_iso A
  constructor
  · apply scalar_assertions A T
    exact preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv
      (scalarToContinuous A)).symm
  · change IsIso ((constantSchemeIso T).hom.app _ ≫
      (upperStarFromPoint T).map (scalarToContinuous A))
    infer_instance

private noncomputable local instance localEquivalences (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective Ab.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
    u + 2, u + 1, u + 1, u + 1} (Scheme.ProEt.topology T)

private noncomputable local instance sliceLocalEquivalences (T : Scheme.{u}) (U : T.ProEt) :
    ((Scheme.ProEt.topology T).over U).WEqualsLocallyBijective Ab.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
    u + 2, u + 1, u + 1, u + 1} ((Scheme.ProEt.topology T).over U)

private theorem flat_over (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R) M) (U : T.ProEt) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := R.over U) (M.over.{u + 1} U) := by
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
    (R.over U) (M.over.{u + 1} U)
  intro V n a s hs
  obtain ⟨S, hS, hlocal⟩ :=
    SheafOfModules.local_equationalCriterion_of_isFlatOnSite.{u + 1, u, u + 1, u + 1} R M hM
      V.left n a s hs
  refine ⟨(Sieve.overEquiv V).symm S,
    (Scheme.ProEt.topology T).overEquiv_symm_mem_over V S hS, ?_⟩
  intro W f hf
  exact hlocal W.left f.left hf

private theorem localized_flatness_of_extension (T : Scheme.{u})
    (hlim : PreservesFiniteLimits (Mod.extendScalars (scalarMap A T))) :
    LocalizedFlatness A T := by
  let R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} := (upperStarFromPoint T).obj
    ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))
  let B := condensedRingObj (Profinite.continuousCoefficientRingObj A) T
  let N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R :=
    (Mod.comap (scalarMap A T)).obj (Mod.regular B)
  let := hlim
  have : PreservesFiniteLimits (tensorLeft N ⋙ Mod.forget R) :=
    preservesFiniteLimits_of_natIso (Mod.extendForgetTensorIso (scalarMap A T))
  have : PreservesFiniteLimits (tensorLeft N) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (Mod.forget R)
  have hN : ObjectProperty.flat N :=
    (ObjectProperty.flat_iff_preservesFiniteLimits N).mpr inferInstance
  have hf := (InternalAbelianSheafModule.flat_iff_sectionModule.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) R N).mp hN
  intro U
  exact flat_over T _ _ hf U

private def constantSectionRingMapAux
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [UnivLE.{_, u + 1}] [HasSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (B : Type (u + 1)) [CommRing B]
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (φ : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B) ⟶ R.obj)
    [@IsMonHom _ _ _ _ _
      ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ] :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of B) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf J R).obj where
  app U := by
    letI := CommRingCat.commRing
      ((InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U)
    refine CommRingCat.ofHom
      (R := B) (S := (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U) ?_
    refine
      { toFun := fun a ↦ φ.app U a
        map_zero' := map_zero _
        map_add' := map_add _
        map_one' := ?_
        map_mul' := ?_ }
    · have h := @IsMonHom.one_hom _ _ _ _ _
        ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
        ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ inferInstance
      convert! ConcreteCategory.congr_hom (congr_app h U) (ULift.up 1) using 1
      simp only [Functor.const_obj_obj, Monoidal.tensorUnit_obj, ObjectProperty.ι_obj,
        Functor.obj.η_def, Category.assoc, NatTrans.comp_app, Functor.const_map_app,
        AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
      change (φ.app U) (1 : B) = (φ.app U) ((η[AddCommGrpCat.of B]).hom (ULift.up 1))
      rw [AddCommGrpCat.ringMonObj_one_apply]
      simp
    · intro a b
      have h := @IsMonHom.mul_hom _ _ _ _ _
        ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
        ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ inferInstance
      have he := ConcreteCategory.congr_hom (congr_app h U) (a ⊗ₜ[ℤ] b)
      convert! he using 1
  naturality U V f := by
    ext a
    exact ConcreteCategory.congr_hom (φ.naturality f) a

private def constantPresheafRingMap (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ R) [IsMonHom ψ] :
    (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) R).obj := by
  let J := Scheme.ProEt.topology T
  let X := AddCommGrpCat.of (ULift.{u + 1} A)
  let P := (Functor.const T.ProEtᵒᵖ).obj X
  let eta := toSheafify J P
  let : MonObj P := (Functor.const T.ProEtᵒᵖ).monObjObj X
  let : MonObj R.obj := (sheafToPresheaf J Ab.{u + 1}).monObjObj R
  let : MonObj ((constantSheaf J Ab.{u + 1}).obj X).obj :=
    (sheafToPresheaf J Ab.{u + 1}).monObjObj ((constantSheaf J Ab.{u + 1}).obj X)
  have hη : @IsMonHom _ _ _ _ _
      ((Functor.const T.ProEtᵒᵖ).monObjObj X)
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        ((constantSheaf J Ab.{u + 1}).obj X)) eta := by
    have h := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
    have hm := Functor.monObjObj_comp (Functor.const T.ProEtᵒᵖ)
      (presheafToSheaf J Ab.{u + 1}) X
    exact @IsMonHom.of_eq _ _ _ _ _ _ _ _ _ _ rfl
      (congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
        (sheafToPresheaf J Ab.{u + 1}) _ _ m) hm).symm h
  let := hη
  have hpsi : @IsMonHom _ _ _ _ _
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        ((constantSheaf J Ab.{u + 1}).obj X))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) ψ.hom := by
    exact inferInstanceAs (IsMonHom ((sheafToPresheaf J Ab.{u + 1}).map ψ))
  let := hpsi
  let φ := eta ≫ ψ.hom
  have hphi : @IsMonHom _ _ _ _ _ ((Functor.const T.ProEtᵒᵖ).monObjObj X)
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ :=
    FiniteDiscreteOrdinary.monHomCompExplicit
      ((Functor.const T.ProEtᵒᵖ).monObjObj X)
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        ((constantSheaf J Ab.{u + 1}).obj X))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) eta ψ.hom hη hpsi
  exact @constantSectionRingMapAux _ _ J inferInstance inferInstance inferInstance
      (ULift.{u + 1} A) inferInstance R inferInstance inferInstance φ hphi

private def constantRingMap (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ R) [IsMonHom ψ] :
    Scheme.adicLisseConstantRing T (ULift.{u + 1} A) ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) R :=
  ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    _ _).symm (constantPresheafRingMap A T R ψ)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem constantRingMap_normalization (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ R) [IsMonHom ψ]
    (U : T.ProEtᵒᵖ) (a : ULift.{u + 1} A) :
    (constantRingMap A T R ψ).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
    ψ.hom.app U ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    _ (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) R)).apply_symm_apply (constantPresheafRingMap A T R ψ)
  change _ = (constantPresheafRingMap A T R ψ).app U a
  exact ConcreteCategory.congr_hom (congr_app h U) a

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem constantRingMap_isIso (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ R) [IsMonHom ψ] [IsIso ψ] :
    IsIso (constantRingMap A T R ψ) := by
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : J.PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification J V
  let F := sheafCompose J V
  let e := (constantCommuteCompose J V).app (CommRingCat.of B)
  let g : F.obj (realizationRing J B) ⟶ R :=
    F.map (constantRingMap A T R ψ)
  have hg : e.inv ≫ g = ψ := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (R).property
    have he : toSheafify J
        ((Functor.const T.ProEtᵒᵖ).obj (V.obj (CommRingCat.of B))) ≫ e.inv.hom =
        Functor.whiskerRight
          (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of B))) V := by
      change _ ≫ (sheafifyMap J (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of B) V).inv ≫
        (sheafifyComposeIso J V _).hom) = _
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
        sheafComposeIso_hom_fac]
      ext U a
      rfl
    change _ ≫ (e.inv.hom ≫ g.hom) = _
    rw [← Category.assoc, he]
    ext U a
    exact constantRingMap_normalization A T R ψ U a
  have : IsIso (e.inv ≫ g) := hg.symm ▸ inferInstance
  have : IsIso g := by
    have hh : g = e.hom ≫ (e.inv ≫ g) := by simp
    rw [hh]
    infer_instance
  exact isIso_of_reflects_iso (constantRingMap A T R ψ) F

attribute [local irreducible] constantPresheafRingMap constantRingMap

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Reconstructed section actions need a larger elaboration budget; compilation stays under 60 s.
private theorem completed_of_identification [IsNoetherianRing A] (T : Scheme.{u}) (p : A)
    (h : CompletedIdentification A T p) : CompletedAssertions A T p := by
  let J := Scheme.ProEt.topology T
  let B := condensedRingObj (Profinite.continuousCoefficientRingObj A) T
  let R := (upperStarFromPoint T).obj
    ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))
  let α : (constantSheaf J Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ R :=
    (constantSchemeIso T).hom.app _
  have hα : IsMonHom α := by
    let X := Mon.mk (AddCommGrpCat.of (ULift.{u + 1} A))
    let e := (Functor.mapMonNatIso (constantSchemeIso T)).app X ≪≫
      Functor.mapMonCompIso.app X
    exact e.hom.isMonHom_hom
  let := hα
  have : IsMonHom (FiniteDiscreteOrdinary.canonicalAbelianMap A T) :=
    FiniteDiscreteOrdinary.canonicalAbelianMap_isMonHom A T
  let i := constantRingMap A T R α
  have : IsIso α := inferInstanceAs (IsIso ((constantSchemeIso T).hom.app _))
  have : IsIso i := constantRingMap_isIso A T R α
  let c := FiniteDiscreteOrdinary.canonicalRingMap A T
  let a := CondensedRing.sectionRingMap T (scalarMap A T)
  have hcomp : i ≫ a = c := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (InternalAbelianSheafModule.sectionRingSheaf J B).property
    ext U x
    change a.hom.app U (i.hom.app U ((toSheafify J
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U x)) = _
    rw [constantRingMap_normalization A T R α U x]
    exact (FiniteDiscreteOrdinary.canonicalRingMap_normalization A T U x).symm
  let I := Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))
  obtain ⟨e, he, huniq⟩ := h
  have hc (n : ℕ) : c ≫ e.hom ≫ limit.π (Scheme.adicLisseRingSystem T I) (op n) =
      (constantSheaf J CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _
      ((Scheme.adicLisseRingSystem T I).obj (op n)).property
    ext U x
    cases x with
    | up x =>
      have hn := he U x n
      rw [← FiniteDiscreteOrdinary.canonicalRingMap_normalization A T U (ULift.up x)] at hn
      exact hn.trans (ConcreteCategory.congr_hom
        (congr_app (toSheafify_naturality J ((Functor.const T.ProEtᵒᵖ).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) U) (ULift.up x))
  have : IsNoetherianRing (ULift.{u + 1} A) :=
    isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  let N₀ := (SheafOfModules.restrictScalars ((Scheme.adicLisseForget T).map c)).obj
    (SheafOfModules.unit ((Scheme.adicLisseForget T).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J B)))
  have hf₀ : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} N₀ :=
    Scheme.CompletedConstantAlgebra.flat_presented_completion T I e.symm c hc
  let N := (Mod.comap (scalarMap A T)).obj (Mod.regular B)
  let M := (InternalAbelianSheafModule.sectionModuleFunctor.{u + 1, u + 1, u} J R).obj N
  let β := (CondensedRing.sectionModuleComapIso T (scalarMap A T)).app (Mod.regular B) ≪≫
    (SheafOfModules.restrictScalars ((Scheme.adicLisseForget T).map a)).mapIso
      (CondensedRing.sectionModuleRegularIso T B)
  have haction (V : T.ProEtᵒᵖ)
      (r : (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj V)
      (y : M.val.obj V) : r • y = a.hom.app V r *
        (show (InternalAbelianSheafModule.sectionRingSheaf J B).obj.obj V from y) := by
    exact (β.hom.val.app V).hom.map_smul r y
  have hflat : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} M := by
    apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R) M
    intro U n x y hxy
    let x₀ : Fin n → (Scheme.adicLisseConstantRing T (ULift.{u + 1} A)).obj.obj (op U) :=
      fun j ↦ (inv i).hom.app (op U) (x j)
    have hi (V : T.ProEtᵒᵖ) (z :
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R).obj.obj V) :
        c.hom.app V ((inv i).hom.app V z) = a.hom.app V z := by
      have hh : inv i ≫ c = a := by rw [← hcomp]; simp
      exact congrArg (fun f ↦ f.hom.app V z) hh
    have hxy₀ : (∑ j, x₀ j • (show N₀.val.obj (op U) from y j)) = 0 := by
      change (∑ j, c.hom.app (op U) (x₀ j) *
        (show (InternalAbelianSheafModule.sectionRingSheaf J B).obj.obj (op U) from y j)) = 0
      simpa only [x₀, hi, haction] using hxy
    obtain ⟨S, hS, hl⟩ :=
      SheafOfModules.local_equationalCriterion_of_isFlatOnSite.{u + 1, u, u + 1, u + 1}
        (Scheme.adicLisseConstantRing T (ULift.{u + 1} A)) N₀ hf₀ U n x₀ y hxy₀
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨l, b, t, hy, hx⟩ := hl V f hf
    refine ⟨l, fun j k ↦ i.hom.app (op V) (b j k), t, ?_, ?_⟩
    · intro j
      simp only [haction]
      change M.val.map f.op (y j) =
        ∑ k, a.hom.app (op V) (i.hom.app (op V) (b j k)) *
          (show (InternalAbelianSheafModule.sectionRingSheaf J B).obj.obj (op V) from t k)
      have hh (z) : a.hom.app (op V) (i.hom.app (op V) z) = c.hom.app (op V) z :=
        congrArg (fun g ↦ g.hom.app (op V) z) hcomp
      have hj := hy j
      change M.val.map f.op (y j) =
        ∑ k, c.hom.app (op V) (b j k) *
          (show (InternalAbelianSheafModule.sectionRingSheaf J B).obj.obj (op V)
            from t k) at hj
      simpa only [hh] using hj
    · intro k
      have hh := congrArg (i.hom.app (op V)) (hx k)
      simp only [map_sum, map_mul, map_zero] at hh
      have hn (j) : i.hom.app (op V)
          ((Scheme.adicLisseConstantRing T (ULift.{u + 1} A)).obj.map f.op (x₀ j)) =
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J R).obj.map f.op
            (x j) := by
        rw [← NatTrans.naturality_apply]
        exact congrArg (fun g ↦ g.hom.app (op V)
          ((InternalAbelianSheafModule.sectionRingSheaf J R).obj.map f.op (x j)))
            (IsIso.inv_hom_id i)
      simpa only [hn] using hh
  have hN := (InternalAbelianSheafModule.flat_iff_sectionModule.{u + 1, u + 1, u} J R N).mpr
    hflat
  have : PreservesFiniteLimits (tensorLeft N) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits N).mp hN
  have : PreservesFiniteLimits (Mod.extendScalars (scalarMap A T) ⋙ Mod.forget B) :=
    preservesFiniteLimits_of_natIso (Mod.extendForgetTensorIso (scalarMap A T)).symm
  have hlim : PreservesFiniteLimits (Mod.extendScalars (scalarMap A T)) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (Mod.forget B)
  exact ⟨⟨e, he, huniq⟩, hlim, inferInstance,
    localized_flatness_of_extension A T hlim⟩

/-- All six admissible scalar realizations are additive and exact, including the continuous
algebraic closure without a finite-subextension condition. Integral coefficients are the
actual completed constant sheaf and are flat on all constant-ring module sheaves.

Source: Stacks 093J, 093M; blueprint main-20261015, internal-Hom stability proof paragraphs
2--3 (blueprint: lem-sfb-admissible-scalar-realization-exact).

Proof:
1. Evaluation on a point identifies each scalar ring with the underlying ordinary ring.
Finite rings (including zero) and fields are Noetherian; integral extension rings are DVRs,
hence PIDs and Noetherian (lem-weil-l-adic-extension-integers-dvr and
lem-weil-pbc-pid-noetherian-normal). The degree-one extension gives the integer case.
2. Constant sheafification and ordinary balanced tensor are additive, on pure tensors.
3. Apply lem-weil-pbc-finite-type-constant-exact (Stacks 093J) to an arbitrary scalar short
exact sequence. No finite-generation hypothesis on any module is used.
4. For finite discrete rings the canonical constant function map is an isomorphism, by
lem-sf-finite-discrete-normalized-encoding and
lem-sf-module-object-ordinary-coefficient-equivalence. Scalar realization is constants.
5. det-prop-sfb-qlbar-colimit-x-integral-limit identifies the actual integral coefficient
ring with the positive tower of constant uniformizer quotients. Every projection carries
a constant scalar to its residue, so the comparison respects the constant scalar map.
Any other uniformizer generates the same ideal, so the assertion covers every choice.
The same argument applies to the standard integer ring with uniformizer ell.
6. lem-weil-pbc-completed-constant-sheaf-reduction (Stacks 093M) gives flatness on all
constant-ring sheaf modules. Apply it to the constant exact sequence in step 3.
7. Every scalar sequence over each of the three fields splits by vector-space projectivity
(lem-weil-pbc-vector-space-projective). Additivity preserves its splitting, hence exactness.
This uses the actual continuous algebraic-closure coefficient ring throughout.
8. lem-sfb-coefficient-sections-localization identifies the localized site and its actual
coefficients with those of the pro-etale object scheme. Repeat steps 2--7 there; restriction
of the scalar map is still constant functions. Ring identifications restrict as well. -/
theorem admissible_scalar_realization_exact (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [Finite A] [DiscreteTopology A],
      (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) →
      ScalarAssertions A T ∧ IsIso (FiniteDiscreteOrdinary.canonicalAbelianMap A T)) ∧
    (ScalarAssertions (ULift.{u} ℤ_[ℓ]) T ∧
      CompletedAssertions (ULift.{u} ℤ_[ℓ]) T (ℓ : ULift.{u} ℤ_[ℓ])) ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E],
      IntegralAssertions ℓ E T ∧ RationalAssertions ℓ E T) ∧
    ScalarAssertions (ULift.{u} ℚ_[ℓ]) T ∧
    ScalarAssertions (ULift.{u} (PadicAlgCl ℓ)) T := by
  have : IsDomain (ULift.{u} ℤ_[ℓ]) :=
    MulEquiv.isDomain ℤ_[ℓ] (ULift.ringEquiv (R := ℤ_[ℓ])).toMulEquiv
  have : IsDomain (ULift.{u} ℚ_[ℓ]) :=
    MulEquiv.isDomain ℚ_[ℓ] (ULift.ringEquiv (R := ℚ_[ℓ])).toMulEquiv
  have : IsDomain (ULift.{u} (PadicAlgCl ℓ)) :=
    MulEquiv.isDomain (PadicAlgCl ℓ) (ULift.ringEquiv (R := PadicAlgCl ℓ)).toMulEquiv
  have hZ : ScalarAssertions (ULift.{u} ℤ_[ℓ]) T := by
    have : IsPrincipalIdealRing (ULift.{u} ℤ_[ℓ]) :=
      ⟨(isPrincipalIdealRing_iff _).1
        (.of_surjective _ (ULift.ringEquiv (R := ℤ_[ℓ])).symm.surjective)⟩
    exact pid_scalar_assertions _ T
  refine ⟨?_, ⟨hZ, ?_⟩, ?_, pid_scalar_assertions _ T, pid_scalar_assertions _ T⟩
  · intro A _ _ _ _ _ _
    exact finite_scalar_assertions A T
  · let : IsNoetherianRing (ULift.{u} ℤ_[ℓ]) := hZ.1
    apply completed_of_identification
    let R := ULift.{u} ℤ_[ℓ]
    let e : R ≃+* ℤ_[ℓ] := ULift.ringEquiv
    have hmap (n : ℕ) : Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ (n + 1) =
        Ideal.map e.toRingHom (Ideal.span ({(ℓ : R)} : Set R) ^ (n + 1)) := by
      rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]
    have hquot (n : ℕ) (x y : R) :
        Ideal.Quotient.mk (Ideal.span ({(ℓ : R)} : Set R) ^ (n + 1)) y =
          Ideal.Quotient.mk (Ideal.span ({(ℓ : R)} : Set R) ^ (n + 1)) x ↔
        Ideal.Quotient.mk (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ (n + 1)) y.down =
          Ideal.Quotient.mk (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ (n + 1)) x.down := by
      let q := Ideal.quotientEquiv _ _ e (hmap n)
      exact q.injective.eq_iff.symm
    apply compact_adic_continuous_identification R (ℓ : R)
    · intro h
      have h₀ := congrArg ULift.down h
      exact (PadicInt.irreducible_p (p := ℓ)).ne_zero h₀
    · intro n
      have hsurj : Function.Surjective (PadicInt.toZModPow (p := ℓ) (n + 1)) :=
        ZMod.ringHom_surjective _
      let q₀ := (Ideal.quotEquivOfEq (by
        rw [PadicInt.ker_toZModPow, Ideal.span_singleton_pow] :
        Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ (n + 1) =
          RingHom.ker (PadicInt.toZModPow (p := ℓ) (n + 1)))).trans
        ((PadicInt.toZModPow (p := ℓ) (n + 1)).quotientKerEquivOfSurjective hsurj)
      let q := (Ideal.quotientEquiv _ _ e (hmap n)).trans q₀
      have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
      exact Finite.of_injective q q.injective
    · intro x
      have h₀ (n : ℕ) :
          Metric.closedBall x.down ((ℓ : ℝ) ^ (-(n + 1 : ℤ))) =
          {y : ℤ_[ℓ] | Ideal.Quotient.mk
            (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ (n + 1)) y =
            Ideal.Quotient.mk
              (Ideal.span ({(ℓ : ℤ_[ℓ])} : Set ℤ_[ℓ]) ^ (n + 1)) x.down} := by
        ext y
        change ‖y - x.down‖ ≤ (ℓ : ℝ) ^ (-(n + 1 : ℕ) : ℤ) ↔ _
        rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← Ideal.span_singleton_pow]
        exact Ideal.Quotient.eq.symm
      have hb : (𝓝 x.down).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
          Metric.closedBall x.down ((ℓ : ℝ) ^ (-(n + 1 : ℤ)))) := by
        apply Metric.nhds_basis_closedBall.to_hasBasis'
        · intro ε hε
          obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt ℓ hε
          refine ⟨n, trivial, Metric.closedBall_subset_closedBall ?_⟩
          exact (zpow_le_zpow_right₀ (by exact_mod_cast
            (Fact.out : ℓ.Prime).one_lt.le) (by omega)).trans hn.le
        · intro n _
          exact Metric.closedBall_mem_nhds _ (zpow_pos (by exact_mod_cast
            (Fact.out : ℓ.Prime).pos) _)
      rw [Topology.IsEmbedding.uliftDown.isInducing.nhds_eq_comap x]
      simpa only [h₀, Set.preimage_ofPred_eq, ← hquot] using hb.comap (ULift.down : R → ℤ_[ℓ])
  · intro E _ _ _
    let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
    have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers ℓ E) := by
      have h := (Padic.extension_integers_dvr ℓ E
        (Padic.coefficientExtensionAbsoluteValue ℓ E)
        (spectralNorm_extends (K := ℚ_[ℓ]) (L := E))).choose_spec.choose_spec
      exact h.2.2.2.2.2.2.2.2.1
    refine ⟨⟨pid_scalar_assertions _ T, ?_⟩, pid_scalar_assertions _ T⟩
    intro π hπ
    apply completed_of_identification
    have hd := Padic.coefficientExtension_integers_profinite_tower.{u, u} ℓ E
    have htop : (inferInstance : TopologicalSpace (Padic.coefficientExtensionIntegers ℓ E)) =
        Padic.coefficientExtensionIntegersTopology ℓ E :=
      Scheme.coefficientIntegersTopology_eq ℓ E
    have hπ₀ : π ≠ 0 := by
      intro hzero
      have hmax := hπ
      rw [hzero, Ideal.span_singleton_zero] at hmax
      have h := (Padic.extension_integers_dvr ℓ E
        (Padic.coefficientExtensionAbsoluteValue ℓ E)
        (spectralNorm_extends (K := ℚ_[ℓ]) (L := E))).choose_spec.choose_spec
      exact h.2.2.2.2.2.2.2.2.2.1 hmax.symm
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ℓ E} :
        Set (Padic.coefficientExtensionIntegers ℓ E)) =
        Padic.coefficientExtensionMaximalIdeal ℓ E := by
      have h := (Padic.extension_integers_dvr ℓ E
        (Padic.coefficientExtensionAbsoluteValue ℓ E)
        (spectralNorm_extends (K := ℚ_[ℓ]) (L := E))).choose_spec.choose_spec
      exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    have heq (n : ℕ) : Padic.coefficientExtensionIdeal ℓ E n =
        Ideal.span ({π} : Set (Padic.coefficientExtensionIntegers ℓ E)) ^ n := by
      unfold Padic.coefficientExtensionIdeal
      rw [hgen, hπ]
    have : CompactSpace (Padic.coefficientExtensionIntegers ℓ E) := by
      change @CompactSpace _ (inferInstance : TopologicalSpace
        (Padic.coefficientExtensionIntegers ℓ E))
      rw [htop]
      exact hd.2.1
    have : T2Space (Padic.coefficientExtensionIntegers ℓ E) := inferInstance
    apply compact_adic_continuous_identification _ π hπ₀
    · intro n
      rw [← heq]
      exact Padic.finite_coefficientExtensionRing ℓ E (n + 1) (Nat.succ_pos n)
    · have hb := Padic.coefficientExtension_integers_coset_basis ℓ E
      change ∀ x, (@nhds _ (inferInstance : TopologicalSpace
        (Padic.coefficientExtensionIntegers ℓ E)) x).HasBasis _ _
      rw [htop]
      intro x
      apply (hb x).congr (fun _ ↦ Iff.rfl)
      intro n _
      congr 1
      funext y
      rw [heq]

end AlgebraicGeometry.ProEtale.AdmissibleScalarRealization
