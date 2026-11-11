/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralDualTorsionHeartSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstructibleLocalModel
import all WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.CategoryTheory.Integral.IntegralStratumHomFormula
import all WeilConjectures.CategoryTheory.Integral.IntegralDualTorsionHeartSections

/-!
# Duals of integral constructible sheaves on strata

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ`. A sheaf `N` of `𝒪_{E,S}`-modules which is
pro-étale locally `𝒪_{E,S} ⊗_{𝒪_E} P` with `P` finitely generated
(`HasFiniteConstantLocalModel`) is, placed in degree `0`, dualizable of Tor amplitude
`[-1, 0]`, and its dual `RHom(N, 𝒪_{E,S})` has Tor amplitude `[0, 1]`
(`ProEtale.CondensedRing.isDualizable_and_torAmplitudeIn_of_hasFiniteConstantLocalModel`):
locally, a finitely generated module `P` over the discrete valuation ring `𝒪_E` has a free
resolution `0 ⟶ 𝒪_E^r ⟶ 𝒪_E^s ⟶ P ⟶ 0` of length one.

Combined with the local structure of constructible sheaves, this gives blueprint
`lemma-structure-integral-constructible-complexes--3`
(`AlgebraicGeometry.ProEtale.CondensedRing.exists_stratification_isDualizable_torAmplitudeIn`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

section LocalResolution

attribute [local instance] constantScalarSheaf_laxBraided

attribute [local irreducible] CondensedRing.upperStar Functor.mapDerivedCategory
  Functor.mapDerivedCategoryHomologyFunctorIso Functor.mapDerivedCategorySingleFunctor
  _root_.DerivedCategory.instMonoidalCategory

/-- Let `Λ` be the condensed ring of continuous functions with values in a topological principal
ideal domain `A`. A sheaf of `Λ_S`-modules with a finite constant local model has, pro-étale
locally, a resolution `0 ⟶ T₁ ⟶ T₂ ⟶ N ⟶ 0` by dualizable (finite free) modules. -/
private lemma exists_localResolution_of_continuous_pid
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A)) (S : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hN : HasFiniteConstantLocalModel Λ S N) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ a : U.I₀,
      ∃ T : ShortComplex (supportModules Λ (U.X a)),
        T.ShortExact ∧ IsDualizable T.X₁ ∧ IsDualizable T.X₂ ∧
        Nonempty (T.X₃ ≅ (upperStar Λ (U.f a)).obj N) := by
  obtain ⟨U, hU⟩ := (finiteConstantLocalModel_iff_exists_cover Λ N).mp hN
  have hε := counitExtension_transport Λ _ e (counitExtension_leftExact A)
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, ⟨n, m, f, ⟨ef⟩⟩, ⟨eP⟩⟩ := hU i
  have := scalarExtension_leftExact Λ hε (U.X i)
  let j := scalarSections.mapMon.mapIso e
  have : IsDomain (ULift.{u + 1} A) :=
    MulEquiv.isDomain A (ULift.ringEquiv (R := A)).toMulEquiv
  have : IsPrincipalIdealRing (ULift.{u + 1} A) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := A)).symm.toRingHom
      (ULift.ringEquiv (R := A)).symm.surjective
  let g := cokernel.π f ≫ ef.inv
  have : Epi g := by dsimp only [g]; infer_instance
  let T := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hT : T.ShortExact := ⟨ShortComplex.exact_kernel g⟩
  let F := finiteConstantScalarExtension Λ (U.X i)
  obtain ⟨a, ⟨ea⟩⟩ := scalar_pid_kernel_free Λ (ULift.{u + 1} A)
    (continuousScalarHom A ≫ j.inv.hom) n P g
  have h₁ : IsDualizable (F.obj T.X₁) :=
    (CategoryTheory.isDualizable_biproduct_unit a).of_iso
      (F.mapIso ea ≪≫ scalarFreeIso Λ (U.X i) a).symm
  have h₂ : IsDualizable (F.obj T.X₂) :=
    (CategoryTheory.isDualizable_biproduct_unit n).of_iso (scalarFreeIso Λ (U.X i) n).symm
  exact ⟨T.map F, hT.map_of_exact F, h₁, h₂, ⟨eP.symm⟩⟩

/-- A sheaf of `𝒪_{E,S}`-modules with a finite constant local model has, pro-étale locally, a
resolution `0 ⟶ T₁ ⟶ T₂ ⟶ N ⟶ 0` by dualizable (finite free) modules. -/
private lemma exists_localResolution_of_hasFiniteConstantLocalModel (S : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) S))
    (hN : HasFiniteConstantLocalModel (Profinite.padicIntegersRingObj.{u} ℓ E) S N) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ a : U.I₀,
      ∃ T : ShortComplex (supportModules (Profinite.padicIntegersRingObj.{u} ℓ E) (U.X a)),
        T.ShortExact ∧ IsDualizable T.X₁ ∧ IsDualizable T.X₂ ∧
        Nonempty (T.X₃ ≅ (upperStar (Profinite.padicIntegersRingObj.{u} ℓ E) (U.f a)).obj N) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : IsTopologicalRing (PadicAlgCl.integers ℓ E) := PadicAlgCl.isTopologicalRing_integers ℓ E
  exact exists_localResolution_of_continuous_pid (Profinite.padicIntegersRingObj.{u} ℓ E)
    (PadicAlgCl.integers ℓ E) (Iso.refl (Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E))) S N hN

end LocalResolution

/-- A sheaf `N` of `Λ_S`-modules which has, pro-étale locally, a resolution by two dualizable
modules is, placed in degree `0`, dualizable of Tor amplitude `[-1, 0]`, and its dual
`RHom(N, Λ_S)` has Tor amplitude `[0, 1]`. -/
private theorem isDualizable_and_torAmplitudeIn_of_localResolution
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (S : Scheme.{u}) (N : supportModules Λ S)
    (hres : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ a : U.I₀,
      ∃ T : ShortComplex (supportModules Λ (U.X a)),
        T.ShortExact ∧ IsDualizable T.X₁ ∧ IsDualizable T.X₂ ∧
        Nonempty (T.X₃ ≅ (upperStar Λ (U.f a)).obj N)) :
    IsDualizable ((DerivedCategory.singleFunctor _ 0).obj N) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0 ((DerivedCategory.singleFunctor _ 0).obj N) ∧
      DerivedCategory.torAmplitudeIn _ 0 1 (stratumModuleDual Λ S N) := by
  obtain ⟨U, hU⟩ := hres
  have hlocal (a : U.I₀) :
      IsDualizable ((DerivedCategory.singleFunctor (supportModules Λ (U.X a)) 0).obj
        ((upperStar Λ (U.f a)).obj N)) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0
        ((DerivedCategory.singleFunctor (supportModules Λ (U.X a)) 0).obj
          ((upperStar Λ (U.f a)).obj N)) := by
    obtain ⟨T, hT, h₁, h₂, ⟨e⟩⟩ := hU a
    have h := shortExact_dualizable_tor_of_iso hT h₁ h₂ e
    exact ⟨dualizableRootTransport Λ (U.X a) _ h.1, h.2⟩
  let R : Profinite.CondensedRing.{u} := ⟨Λ⟩
  have hd : IsDualizable ((DerivedCategory.singleFunctor (supportModules Λ S) 0).obj N) := by
    apply (condensed_dualizable_iff_proetale_cover R S U _).mpr
    intro a
    let e := ((upperStar Λ (U.f a)).mapDerivedCategorySingleFunctor 0).app N
    have hr := dualizableRootOfSource Λ (U.X a) _ (hlocal a).1
    exact dualizableRootTransport Λ (U.X a) _ (rootDualizable_of_iso _ _ e.symm hr)
  exact ⟨hd, (integralHeart_local_duality_descent Λ S N U (-1) 0 hlocal).2,
    dual_data Λ S N ⟨U, hU⟩⟩

/-- Let `N` be a sheaf of `𝒪_{E,S}`-modules which is pro-étale locally `𝒪_{E,S} ⊗_{𝒪_E} P` with
`P` finitely generated (`HasFiniteConstantLocalModel`). Then `N`, placed in degree `0`, is
dualizable of Tor amplitude `[-1, 0]`, and its dual `RHom(N, 𝒪_{E,S})`
(`stratumModuleDual`) has Tor amplitude `[0, 1]`. -/
theorem isDualizable_and_torAmplitudeIn_of_hasFiniteConstantLocalModel (S : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) S))
    (hN : HasFiniteConstantLocalModel (Profinite.padicIntegersRingObj.{u} ℓ E) S N) :
    IsDualizable ((DerivedCategory.singleFunctor _ 0).obj N) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0 ((DerivedCategory.singleFunctor _ 0).obj N) ∧
      DerivedCategory.torAmplitudeIn _ 0 1
        (stratumModuleDual (Profinite.padicIntegersRingObj.{u} ℓ E) S N) :=
  isDualizable_and_torAmplitudeIn_of_localResolution _ S N
    (exists_localResolution_of_hasFiniteConstantLocalModel ℓ E S N hN)

/-- Blueprint `lemma-structure-integral-constructible-complexes--3`: for a constructible
`𝒪_E`-sheaf `C` on a noetherian scheme `X` there is a finite stratification `X = ∐ₐ Xₐ` on whose
strata `C` is pro-étale locally `𝒪_{E,Xₐ} ⊗_{𝒪_E} P` with `P` finitely generated (clause (2)),
and on each such stratum `C|_{Xₐ}` (placed in degree `0`) is dualizable of Tor amplitude
`[-1, 0]`, its dual `RHom(C|_{Xₐ}, 𝒪_{E,Xₐ})` having Tor amplitude `[0, 1]`. -/
theorem exists_stratification_isDualizable_torAmplitudeIn {X : Scheme.{u}} [IsNoetherian X]
    {C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)}
    (hC : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) C) :
    ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
      HasFiniteConstantLocalModel (Profinite.padicIntegersRingObj.{u} ℓ E) (S.domain a)
        ((upperStar (Profinite.padicIntegersRingObj.{u} ℓ E) (S.immersion a)).obj C) ∧
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((upperStar (Profinite.padicIntegersRingObj.{u} ℓ E) (S.immersion a)).obj C)) ∧
      DerivedCategory.torAmplitudeIn _ (-1) 0 ((DerivedCategory.singleFunctor _ 0).obj
        ((upperStar (Profinite.padicIntegersRingObj.{u} ℓ E) (S.immersion a)).obj C)) ∧
      DerivedCategory.torAmplitudeIn _ 0 1
        (stratumModuleDual (Profinite.padicIntegersRingObj.{u} ℓ E) (S.domain a)
          ((upperStar (Profinite.padicIntegersRingObj.{u} ℓ E) (S.immersion a)).obj C)) := by
  obtain ⟨S, hS⟩ := exists_stratification_hasFiniteConstantLocalModel ℓ E hC
  exact ⟨S, fun a ↦ ⟨hS a,
    isDualizable_and_torAmplitudeIn_of_hasFiniteConstantLocalModel ℓ E _ _ (hS a)⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
