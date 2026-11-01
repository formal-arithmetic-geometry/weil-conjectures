/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierKernel
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude

import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Derived realization of the condensed Artin--Schreier module

Source: current blueprint, sec-fourier-transform/sk-thm-inversion/def-fd-kernel.md,
and the integrand paragraph of lem-fd-convolution-kernel.proof.md
(blueprint: def-fd-adic-fourier-realization).

The coefficient module is the existing image of the character projector over the
pulled-back condensed ring. Its derived realization places this module in degree zero.
The integrand uses the total derived pullback and relative derived tensor over that ring.
The former common-stage declarations are preserved in
`Sheaf.Paper.FourierAdicArtinSchreierCompatibility` for their existing consumers.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

attribute [local irreducible] condensedArtinSchreierSheaf

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The degree-zero realization of the actual condensed Artin--Schreier module.
This applies to every admissible coefficient ring and includes trivial characters.
Source: current blueprint, def-fd-artin-schreier-sheaf, condensed clause, and
lem-fd-convolution-kernel, Step 1 (blueprint: def-fd-adic-fourier-realization). -/
def fourierCondensedArtinSchreier (k : Type u) [Field k] [Fintype k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (ψ : AddChar k (MonObj.Γ Λ)) (b : Γ(X, ⊤)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (DerivedCategory.singleFunctor _ 0).obj (condensedArtinSchreierSheafOf Λ k X ψ b)

/-- The degree-zero condensed Fourier kernel for the characteristic condition `p = 0`.
The condition allows the empty scheme. No integral lattice or completion is chosen.
Source: current blueprint, def-fd-kernel (blueprint: def-fd-adic-fourier-realization). -/
def fourierCondensedKernel (p : ℕ) [Fact p.Prime]
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    (hp : (p : Γ(pullback π π', ⊤)) = 0)
    (Ψ : AddChar (ZMod p) (MonObj.Γ Λ)) (b : Γ(pullback π π', ⊤)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (pullback π π')) Ab.{u + 1})
      (condensedRingObj Λ (pullback π π'))) :=
  (DerivedCategory.singleFunctor _ 0).obj (condensedPrimeFourierKernel Λ p π π' hp Ψ b)

/-- The ambient Fourier integrand, formed with the coefficient ring on the product.
Source: current blueprint, lem-fd-convolution-kernel, Step 1
(blueprint: def-fd-adic-fourier-realization). -/
def fourierCondensedIntegrand (p : ℕ) [Fact p.Prime]
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    (hp : (p : Γ(pullback π π', ⊤)) = 0)
    (Ψ : AddChar (ZMod p) (MonObj.Γ Λ)) (b : Γ(pullback π π', ⊤))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (pullback π π')) Ab.{u + 1})
      (condensedRingObj Λ (pullback π π'))) :=
  ((CondensedRing.derivedTensor Λ (pullback π π')).obj
    ((CondensedRing.moduleObjectDerivedPullback Λ (pullback.fst π π')).obj K)).obj
      (fourierCondensedKernel Λ p π π' hp Ψ b)

private def pointRegularIso (X : Scheme.{u}) :
    ((upperStarFromPoint X).mapMod Λ).obj (Mod.regular Λ) ≅
      Mod.regular (condensedRingObj Λ X) :=
  Mod.isoMk (Iso.refl _) (by simp only [Iso.refl_hom, Category.comp_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp])

omit [IsCommMonObj Λ] in
private theorem regular_finitelyPresented : Mod.IsFinitelyPresented Λ (Mod.regular Λ) := by
  refine ⟨1, 0, 0, ⟨?_⟩⟩
  exact (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular Λ)).symm ≪≫
    cokernelZeroIsoTarget.symm

private theorem model_iso (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e.symm ≪≫ eP⟩⟩

private theorem model_stratified (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : HasFiniteConstantLocalModel Λ X M) : IsFiniteConstantStratified Λ X M := by
  refine ⟨Scheme.Stratification.trivial X, fun _ ↦ ?_⟩
  exact model_iso Λ X ((CondensedRing.upperStarId Λ X).app M).symm h

private theorem model_zero (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  have (T : Scheme.{u}) : ((upperStarFromPoint T).mapMod Λ).Additive := by
    have : PreservesFiniteLimits (upperStarFromPoint T) := by
      unfold upperStarFromPoint pointUpperStar
      infer_instance
    exact Functor.additive_of_preserves_binary_products _
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((CondensedRing.upperStar Λ _).map_isZero h).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

private theorem constructible_zero (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsZero M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact model_stratified Λ X M (model_zero Λ X M h)
  · exact fun U _ ↦ model_stratified Λ U.toScheme _
      (model_zero Λ U.toScheme _ ((CondensedRing.upperStar Λ U.ι).map_isZero h))

private theorem constructible_iso (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hs (T : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
      (e : A ≅ B) (h : IsFiniteConstantStratified Λ T A) :
      IsFiniteConstantStratified Λ T B := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ model_iso Λ _
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  classical
  unfold IsConstantModelConstructible at *
  split_ifs at * with hX
  · exact hs X e h
  · exact fun U hU ↦ hs U.toScheme ((CondensedRing.upperStar Λ U.ι).mapIso e) (h U hU)

/-- The actual realization is bounded constructible and has Tor amplitude `[0,0]`.
Its rank-one local models are supplied by `prop_kernel_lisse`, including the trivial
character. The theorem uses the finite constant scalar model definition of constructibility.

Source: current blueprint, def-fd-kernel and prop-kernel-lisse
(blueprint: def-fd-adic-fourier-realization).
Proof: use the regular-module trivializations of the character image from
prop-kernel-lisse. The regular module on each chart is the pullback of the regular
condensed module on the point, which is finitely presented. The one-stratum
stratification gives constructibility. In degree zero the homology is this module;
in all other degrees it is zero, with a finite constant zero model. The Tor-amplitude
assertion is precisely the degree-q condensed branch of prop-kernel-lisse. -/
theorem fourierCondensedArtinSchreier_mem (k : Type u) [Field k] [Fintype k]
    (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
    (hΛ : CondensedRing.IsAdmissibleCoefficient Λ)
    (X : Scheme.{u}) [IsNoetherian X] [X.Over (Spec (.of k))]
    (ψ : AddChar k (MonObj.Γ Λ)) (b : Γ(X, ⊤)) :
    constantModelBoundedConstructible Λ X (fourierCondensedArtinSchreier Λ k X ψ b) ∧
      DerivedCategory.torAmplitudeIn
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) 0 0
        (fourierCondensedArtinSchreier Λ k X ψ b) := by
  have h := Etale.prop_kernel_lisse.2.2.2 Λ k hq hΛ X ψ ψ b
  refine ⟨?_, h.2.2.2.2⟩
  have hM : IsConstantModelConstructible Λ X (condensedArtinSchreierSheafOf Λ k X ψ b) := by
    rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
    apply model_stratified Λ X
    obtain ⟨U, hU⟩ := h.2.1
    exact ⟨U, fun i ↦ ⟨Mod.regular Λ, regular_finitelyPresented Λ,
      ⟨(hU i).some ≪≫ (pointRegularIso Λ (U.X i)).symm⟩⟩⟩
  change constantModelBoundedConstructible Λ X
    ((DerivedCategory.singleFunctor _ 0).obj (condensedArtinSchreierSheafOf Λ k X ψ b))
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact constructible_iso Λ X
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm hM
  · apply constructible_zero Λ X
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn

/-- The prime-field kernel is bounded constructible and has Tor amplitude `[0,0]`.
Source: current blueprint, def-fd-kernel and prop-kernel-lisse
(blueprint: def-fd-adic-fourier-realization).
Proof: use the canonical prime-field structure already present in
condensedPrimeFourierKernel. Apply the degree-q realization theorem with
k = ULift F_p; its cardinality is p, so the coefficient unit hypothesis is unchanged. -/
theorem fourierCondensedKernel_mem (p : ℕ) [Fact p.Prime]
    (hunit : IsUnit (p : MonObj.Γ Λ))
    (hΛ : CondensedRing.IsAdmissibleCoefficient Λ)
    {S V V' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S)
    [IsNoetherian (pullback π π')]
    (hp : (p : Γ(pullback π π', ⊤)) = 0)
    (Ψ : AddChar (ZMod p) (MonObj.Γ Λ)) (b : Γ(pullback π π', ⊤)) :
    constantModelBoundedConstructible Λ (pullback π π')
        (fourierCondensedKernel Λ p π π' hp Ψ b) ∧
      DerivedCategory.torAmplitudeIn
        (Mod (Sheaf (Scheme.ProEt.topology (pullback π π')) Ab.{u + 1})
          (condensedRingObj Λ (pullback π π'))) 0 0
        (fourierCondensedKernel Λ p π π' hp Ψ b) := by
  let : (pullback π π').Over (Spec (.of (ULift.{u} (ZMod p)))) :=
    ⟨(pullback π π').toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      ((ZMod.castHom (ringChar.dvd hp) Γ(pullback π π', ⊤)).comp
        ULift.ringEquiv.toRingHom))⟩
  have hcard : IsUnit (Fintype.card (ULift.{u} (ZMod p)) : MonObj.Γ Λ) := by
    simpa only [Fintype.card_ulift, ZMod.card] using hunit
  simpa only [fourierCondensedKernel, condensedPrimeFourierKernel,
    condensedFourierKernel, fourierCondensedArtinSchreier] using
    fourierCondensedArtinSchreier_mem Λ (ULift.{u} (ZMod p)) hcard hΛ
      (pullback π π') (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) b

end WeilConjectures
