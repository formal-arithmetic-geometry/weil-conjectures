/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.AlgebraicGeometry.AdmissibleScalarHomologyData
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientSectionsLocalization
import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections

/-!
# Exact scalar realization for the current admissible coefficients

Source: current blueprint, det-thm-sf-ctf-stability-internal-hom, paragraphs 1--2;
det-prop-sfb-qlbar-colimit-x-integral-limit (3), and
det-prop-integral-criterion-constant-coefficients (1)
(blueprint: lem-sfb-admissible-scalar-realization-exact).

The algebraic-closure case is the finite-subextension-valued coefficient in
`IsLocalizingAdmissibleCoefficient`. The old module supplies the unchanged integral
comparison and flatness predicates, and the proof below takes from its theorem only the
conjuncts whose statements are unchanged (finite constants, `ℤ_ℓ` completion, integral
assertions); its old all-continuous algebraic-closure clause is not used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CurrentAdmissibleScalarRealization

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing scalar local-model functor restricted to the actual slice site.
Source: current internal-Hom stability proof, locality of scalar models;
Stacks 00Y0 (blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def localizedScalarRealization (T : Scheme.{u}) (U : T.ProEt) :=
  finiteConstantScalarExtension Λ T ⋙
    InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology T)
      (condensedRingObj Λ T) ⋙ SheafOfModules.overFunctor _ U

/-- Noetherian scalars and additive exact scalar realization, on T and each actual slice.
The domain of finiteConstantScalarExtension is all scalar modules, with no finiteness
condition. Source: current internal-Hom stability proof, paragraphs 1--2
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def ScalarAssertions (T : Scheme.{u}) : Prop :=
  IsNoetherianRing (condensedScalarRing Λ) ∧
    (finiteConstantScalarExtension Λ T).Additive ∧
    PreservesFiniteLimits (finiteConstantScalarExtension Λ T) ∧
    PreservesFiniteColimits (finiteConstantScalarExtension Λ T) ∧
    ∀ U : T.ProEt, (localizedScalarRealization Λ T U).Additive ∧
      PreservesFiniteLimits (localizedScalarRealization Λ T U) ∧
      PreservesFiniteColimits (localizedScalarRealization Λ T U)

private theorem noetherian_of_mon_iso
    {Λ Ω : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Ω] [IsCommMonObj Ω]
    (e : Mon.mk Λ ≅ Mon.mk Ω) [IsNoetherianRing (condensedScalarRing Ω)] :
    IsNoetherianRing (condensedScalarRing Λ) := by
  let : IsNoetherianRing (MonObj.Γ Ω) :=
    isNoetherianRing_of_ringEquiv (condensedScalarRing Ω)
      (InternalAbelianSheafModule.sectionGlobalEquiv
        (coherentTopology Profinite.{u}) Ω (⊤_ Profinite.{u}) terminalIsTerminal).symm
  let ef : Λ ⟶ Ω := (Mon.forget (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})).map e.hom
  let ei : Ω ⟶ Λ := (Mon.forget (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})).map e.inv
  let : IsMonHom ef := by
    dsimp [ef]
    exact e.hom.isMonHom_hom
  let : IsMonHom ei := by
    dsimp [ei]
    exact e.inv.isMonHom_hom
  have hs : Function.Surjective (MonObj.Γ.map (R := Ω) (S := Λ) ei) := by
    intro x
    refine ⟨MonObj.Γ.map (R := Λ) (S := Ω) ef x, ?_⟩
    apply MonObj.Γ.ext
    simp only [MonObj.Γ.map_hom]
    have hei : ef ≫ ei = 𝟙 _ := by
      dsimp [ef, ei]
      change e.hom.hom ≫ e.inv.hom = 𝟙 Λ
      simpa only [Mon.comp_hom', Mon.id_hom'] using
        congrArg (fun f : Mon.mk Λ ⟶ Mon.mk Λ => f.hom) e.hom_inv_id
    rw [Category.assoc, hei, Category.comp_id]
  let : IsNoetherianRing (MonObj.Γ Λ) :=
    isNoetherianRing_of_surjective (MonObj.Γ Ω) (MonObj.Γ Λ)
      (MonObj.Γ.map (R := Ω) (S := Λ) ei) hs
  have hring : IsNoetherianRing
      ((InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) Λ).obj.obj (op (⊤_ Profinite.{u}))) :=
    isNoetherianRing_of_ringEquiv _
      (InternalAbelianSheafModule.sectionGlobalEquiv
        (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u}) terminalIsTerminal)
  exact hring

private theorem continuousMap_scalar_noetherian
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsNoetherianRing A] :
    IsNoetherianRing (condensedScalarRing (Profinite.continuousMapRingObj.{u} A)) := by
  let : IsNoetherianRing (MonObj.Γ (Profinite.continuousMapRingObj.{u} A)) :=
    isNoetherianRing_of_surjective A _ (Profinite.continuousMapConstRingHom A)
      (Profinite.continuousMapConstRingHom_surjective A)
  have hring : IsNoetherianRing
      ((InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) (Profinite.continuousMapRingObj.{u} A)).obj.obj
          (op (⊤_ Profinite.{u}))) :=
    isNoetherianRing_of_ringEquiv _
      (InternalAbelianSheafModule.sectionGlobalEquiv
        (coherentTopology Profinite.{u}) (Profinite.continuousMapRingObj.{u} A)
        (⊤_ Profinite.{u}) terminalIsTerminal)
  exact hring

private theorem padicAlgCl_scalar_noetherian (ℓ : ℕ) [Fact ℓ.Prime] :
    IsNoetherianRing (condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ)) := by
  let : IsNoetherianRing (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) :=
    isNoetherianRing_of_surjective (PadicAlgCl ℓ) _
      (Profinite.PadicAlgCl.constRingHom ℓ)
      (Profinite.PadicAlgCl.constRingHom_surjective ℓ)
  have hring : IsNoetherianRing
      ((InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) (Profinite.padicAlgClRingObj.{u} ℓ)).obj.obj
          (op (⊤_ Profinite.{u}))) :=
    isNoetherianRing_of_ringEquiv _
      (InternalAbelianSheafModule.sectionGlobalEquiv
        (coherentTopology Profinite.{u}) (Profinite.padicAlgClRingObj.{u} ℓ)
        (⊤_ Profinite.{u}) terminalIsTerminal)
  exact hring

/-- Exact scalar realization for the six current admissible coefficients, together with
finite constant-function identification and the normalized integral limit and flatness
assertions, including flatness on all constant-ring sheaf modules on slices.

Source: current blueprint det-thm-sf-ctf-stability-internal-hom, paragraphs 1--2;
det-prop-sfb-qlbar-colimit-x-integral-limit (3), and
det-prop-integral-criterion-constant-coefficients (1)
(blueprint: lem-sfb-admissible-scalar-realization-exact).

Proof:
1. Singleton evaluation gives the usual scalar rings. Finite rings and fields are
Noetherian; the integral rings are DVRs, hence principal ideal rings and Noetherian.
For the algebraic closure a singleton value always lies in a finite subextension.
2. The second assertion of lem-sfb-admissible-scalar-homology-data supplies finite
limits for the existing finiteConstantScalarExtension, for every admissible coefficient.
Its internal scalar modules are ordinary modules by the internal-module equivalence.
3. Constant sheafification preserves finite colimits (Stacks 093J), as does scalar
extension, its left adjoint. On pure tensors the extension preserves addition and zero.
Preserving kernels and cokernels gives preservation of all short exact sequences.
4. For finite discrete A the canonical constant-function map is locally bijective:
use the clopen fibres of each function, including the empty cover and the zero ring.
Sheafification and inverse image therefore make the specified scalar map invertible.
5. The current integral coefficient limit theorem identifies the actual coefficient
with the positive constant quotient tower. Its projections send constants to residues;
this is exactly CompletedIdentification. Every uniformizer generates the same ideal.
The case E = Q_l gives Z_l with uniformizer l.
6. The current integral criterion (1) makes the canonical constant-scalar map flat
on all sheaf modules. This gives the finite-limit and finite-colimit assertions for
Mod.extendScalars in CompletedAssertions, not merely its constant-module restriction.
7. Coefficient-sections localization identifies the restricted coefficients with those
on the pro-etale object scheme. Constants, scalar maps, tensor products and quotient
projections restrict to the same constructions; repeat steps 1--6 there. This supplies
all localized assertions and the restricted integral flatness.
-/
theorem admissible_scalar_realization_exact (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    (∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ], IsLocalizingAdmissibleCoefficient ℓ Λ →
        ScalarAssertions Λ T) ∧
    (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [Finite A] [DiscreteTopology A],
      (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) →
        IsIso (FiniteDiscreteOrdinary.canonicalAbelianMap A T)) ∧
    AdmissibleScalarRealization.CompletedAssertions (ULift.{u} ℤ_[ℓ]) T
      (ℓ : ULift.{u} ℤ_[ℓ]) ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E],
      AdmissibleScalarRealization.IntegralAssertions ℓ E T) := by
  have hold :=
    AlgebraicGeometry.ProEtale.AdmissibleScalarRealization.admissible_scalar_realization_exact
      ℓ T
  refine ⟨?_, ?_, hold.2.1.2, ?_⟩
  · intro Λ _ _ hΛ
    have hnoeth : IsNoetherianRing (condensedScalarRing Λ) := by
      rcases hΛ with h | h | h | h | h | h
      · obtain ⟨A, _, _, _, _, hfin, _, ⟨e⟩⟩ := h
        let : Finite A := hfin
        let : IsNoetherianRing A := isNoetherian_of_finite A A
        let := continuousMap_scalar_noetherian A
        exact noetherian_of_mon_iso e
      · obtain ⟨e⟩ := h
        let := continuousMap_scalar_noetherian ℤ_[ℓ]
        exact noetherian_of_mon_iso e
      · obtain ⟨e⟩ := h
        let := continuousMap_scalar_noetherian ℚ_[ℓ]
        exact noetherian_of_mon_iso e
      · obtain ⟨E, ⟨e⟩⟩ := h
        let := PadicAlgCl.normedFieldOfAlgebra ℓ E
        let := continuousMap_scalar_noetherian E
        exact noetherian_of_mon_iso e
      · obtain ⟨E, ⟨e⟩⟩ := h
        let := PadicAlgCl.normedFieldOfAlgebra ℓ E
        let := continuousMap_scalar_noetherian (PadicAlgCl.integers ℓ E)
        exact noetherian_of_mon_iso e
      · obtain ⟨e⟩ := h
        let := padicAlgCl_scalar_noetherian ℓ
        exact noetherian_of_mon_iso e
    obtain ⟨_, hlimAll⟩ :=
      AlgebraicGeometry.ProEtale.admissibleScalarHomologyData ℓ Λ hΛ
    have hlim := hlimAll T
    have hcol : PreservesFiniteColimits (finiteConstantScalarExtension Λ T) := by
      have hcc : PreservesFiniteColimits (scalarConstant T) := by
        have hp : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
          pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
        unfold scalarConstant upperStarFromPoint
        infer_instance
      have hm : PreservesFiniteColimits
          ((scalarConstant T).mapMod (scalarRingObj Λ)) := by
        infer_instance
      have he : PreservesFiniteColimits
          (Mod.extendScalars (scalarCoefficientHom Λ T)) := by
        infer_instance
      unfold finiteConstantScalarExtension
      infer_instance
    have hadd : (finiteConstantScalarExtension Λ T).Additive := by
      have hp : PreservesBinaryBiproducts (finiteConstantScalarExtension Λ T) :=
        preservesBinaryBiproducts_of_preservesBinaryCoproducts _
      exact Functor.additive_of_preservesBinaryBiproducts _
    refine ⟨hnoeth, hadd, hlim, hcol, ?_⟩
    intro U
    have hsec : (InternalAbelianSheafModule.sectionModuleFunctor
          (Scheme.ProEt.topology T) (condensedRingObj Λ T)).IsEquivalence := by
      exact inferInstanceAs ((InternalAbelianSheafModule.sectionModuleEquivalence
        (Scheme.ProEt.topology T) (condensedRingObj Λ T)).functor.IsEquivalence)
    let := hsec
    have : PreservesFiniteLimits
        (InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology T)
          (condensedRingObj Λ T)) := by
      infer_instance
    have : PreservesFiniteColimits
        (InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology T)
          (condensedRingObj Λ T)) := by
      infer_instance
    have : (SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (condensedRingObj Λ T))) U).IsLeftAdjoint := by
      dsimp [SheafOfModules.overFunctor]
      infer_instance
    let O := (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) (condensedRingObj Λ T))
    have : PreservesFiniteLimits
        (SheafOfModules.overFunctor.{u + 1} O U ⋙
          SheafOfModules.toSheaf.{u + 1} (O.over U)) := by
      change PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} O ⋙
        (Scheme.ProEt.topology T).overPullback Ab.{u + 1} U)
      infer_instance
    have : PreservesFiniteLimits
        (SheafOfModules.overFunctor.{u + 1} O U) :=
      preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf (O.over U))
    have : PreservesFiniteColimits
        (SheafOfModules.overFunctor.{u + 1} O U) := by infer_instance
    dsimp [localizedScalarRealization]
    exact ⟨rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      exact inferInstance), inferInstance, inferInstance⟩
  · intro A _ _ _ _ _ hkill
    exact (hold.1 A hkill).2
  · intro E _ _ _
    exact (hold.2.2.1 E).1

end AlgebraicGeometry.ProEtale.CurrentAdmissibleScalarRealization
