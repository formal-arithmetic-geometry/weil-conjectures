/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
/-!
# Intrinsic and finite constant-model coefficient domains

Source: current blueprint, thm-sf-biduality-class, identification of Dctf;
Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
private local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
private theorem intrinsic_comap_iff
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    (φ : Λ ⟶ Γ) [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X)) :
    IsConstructibleModuleObject (condensedRingObj Λ X)
        ((Mod.comap ((upperStarFromPoint X).map φ)).obj M) ↔
      IsConstructibleModuleObject (condensedRingObj Γ X) M := by
  constructor
  · intro h
    have hh := _root_.constructible_comap (inv ((upperStarFromPoint X).map φ)) h
    exact _root_.constructible_of_iso
      (((Mod.comapComp (inv ((upperStarFromPoint X).map φ))
          ((upperStarFromPoint X).map φ)).symm ≪≫
        Mod.comapCongr (IsIso.inv_hom_id _) ≪≫ Mod.comapId _).app M) hh
  · exact _root_.constructible_comap _

private theorem heart_transport
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    (e : Mon.mk Λ ≅ Mon.mk Γ) (X : Scheme.{u})
    (hΓ : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Γ X),
      IsConstructibleModuleObject (condensedRingObj Γ X) M ↔
        IsConstantModelConstructible Γ X M)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
      IsConstantModelConstructible Λ X M := by
  rw [← intrinsic_comap_iff e.inv.hom X M, hΓ,
    constantModel_comap_iff e.inv.hom X M]

private theorem bounded_eq_of_heart
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (h : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
        IsConstantModelConstructible Λ X M) :
    constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
  funext K
  apply propext
  exact and_congr_right fun _ ↦ forall_congr' fun n ↦ (h _).symm

private theorem finite_heart (B : Type) [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [Finite B] [DiscreteTopology B]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj B) X)) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj B) X) M ↔
      IsConstantModelConstructible (Profinite.continuousMapRingObj B) X M := by
  obtain ⟨eR, hR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  let : IsMonHom eR.hom := hR
  let E := CondensedRing.finiteDiscreteCoefficientEquivalence B eR
    (internalToModule (ULift.{u + 1} B)) rfl X
  constructor
  · intro hM
    have h := CondensedRing.finiteDiscreteCoefficient_constructible B eR
      (internalToModule (ULift.{u + 1} B)) rfl X M hM
    have h' := (encoding_constructible_iff B X eR (E.inverse.obj M)).mp h
    exact constructible_iso (E.counitIso.app M) h'
  · intro hM
    exact constructible_of_finiteConstantStratified _ X M (by
      simpa only [IsConstantModelConstructible, if_pos
        (show CompactSpace X ∧ QuasiSeparatedSpace X from ⟨inferInstance, inferInstance⟩)]
        using hM)

private theorem integral_heart (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) M ↔
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.1) X M := by
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.1) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.1)).symm.finiteDimensional
  obtain ⟨e⟩ := integralCoefficientIso.{u} ℓ E
  exact heart_transport e.symm X
    (comparison_of_local_models _ (integral_lfp_hasFiniteConstantLocalModel ℓ
      (ULift.{u} E.1)) X) M

private theorem heart_of_localFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
      IsConstantModelConstructible Λ X M := by
  apply comparison_of_local_models Λ _ X M
  intro Y _ N hN
  obtain ⟨U, hU⟩ := hLF Y N hN
  apply free_hasConstantModel Λ N
  refine ⟨U, fun i ↦ ?_⟩
  let ψ := condensedPullbackHom Λ (U.f i)
  exact free_of_iso (free_comap (inv ψ) (hU i))
    ((Mod.extendScalarsIsoComapInv ψ).app _).symm

/-- Finite discrete scalar rings have canonically isomorphic constant and continuous
condensed presentations. Source: thm-sf-biduality-class, finite comparison
(blueprint: lem-sf-intrinsic-coefficient-domain).
Proof: constant-to-continuous functions are locally bijective; sheafification makes
their ring map invertible. Forget the ring encoding, retaining its monoid structure. -/
theorem sfDiscreteCoefficientIso (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    Nonempty (Mon.mk (IntegralModelsEmbedded.discreteObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} A)) := by
  let J := coherentTopology Profinite.{u}
  let f := Profinite.constantToContinuousRing.{u} A
  have : Presheaf.IsLocallyInjective J f :=
    ⟨fun a b h ↦ Presheaf.equalizerSieve_mem J
      (Profinite.constantToContinuousAb.{u} A) a b h⟩
  have : Presheaf.IsLocallySurjective J f :=
    ⟨fun a ↦ Presheaf.imageSieve_mem J (Profinite.constantToContinuousAb.{u} A) a⟩
  have hf : J.W f := J.W_of_isLocallyBijective f
  have : IsIso ((presheafToSheaf J RingCat.{u + 1}).map f) := (J.W_iff f).mp hf
  have : IsIso (IntegralModelsEmbedded.constantToContinuous.{u} A) := by
    unfold IntegralModelsEmbedded.constantToContinuous
    rw [Adjunction.homEquiv_counit]
    change IsIso (_ ≫ (presheafToSheaf J RingCat.{u + 1}).map f ≫ _)
    infer_instance
  let e := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
    (asIso (IntegralModelsEmbedded.constantToContinuous.{u} A))
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map J
    (IntegralModelsEmbedded.constantToContinuous.{u} A)
  exact ⟨Mon.mkIso' e⟩

/-- Intrinsic bounded constructibility agrees with finite constant-model bounded
constructibility for the four coefficient alternatives on a Noetherian scheme.

Source: current blueprint thm-sf-biduality-class and the finite coefficient comparison;
Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11.
(blueprint: lem-sf-intrinsic-coefficient-domain).

Proof: scalar restriction along a coefficient isomorphism preserves and reflects
intrinsic finite presentations and constant local models. For finite coefficients,
the sectionwise encoding identifies intrinsic constructibility with ordinary
constructibility. Its inverse identifies finite locally constant modules with
finite constant scalar models. The encoding counit returns the original module.
For integral coefficients, local finite presentations admit constant scalar models
by continuous local Smith elimination, and the explicit integer-ring isomorphism
compares the lifted extension with the embedded ring of integers. For fields and
the algebraic closure, local finite presentations are locally free of finite rank,
hence have finite free constant scalar models. Apply these heart comparisons to
each cohomology module, retaining the same boundedness predicate. Finite rings
include the zero ring; empty schemes and zero cohomology require no exclusions. -/
theorem sfIntrinsicCoefficientDomain
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ+)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
        (PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ)))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (X : Scheme.{u}) [IsNoetherian X] :
    constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
  apply bounded_eq_of_heart Λ X
  intro M
  rcases hΛ with hf | hi | he | hb
  · obtain ⟨e⟩ := hf
    let A := PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ)
    let : Finite A := by
      dsimp [A]
      rw [hπ]
      infer_instance
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := ⟨rfl⟩
    let : IsTopologicalRing A := inferInstance
    obtain ⟨i⟩ := sfDiscreteCoefficientIso.{u} A
    exact heart_transport (e ≪≫ i) X (finite_heart A X) M
  · obtain ⟨e⟩ := hi
    exact heart_transport e X (integral_heart ℓ E X) M
  · obtain ⟨e⟩ := he
    exact heart_transport e X
      (heart_of_localFree _ (finite_lf ℓ E) X) M
  · obtain ⟨e⟩ := hb
    exact heart_transport e X
      (heart_of_localFree _ (algcl_lf ℓ) X) M

end AlgebraicGeometry.ProEtale
