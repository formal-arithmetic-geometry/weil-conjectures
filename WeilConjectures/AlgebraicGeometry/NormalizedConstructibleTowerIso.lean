/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerInjectiveComponents
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor

/-! # Isomorphism invariance of normalized constructible towers

Source: latest blueprint, sk-lem-sp-tower.proof.md, Conversely paragraph, final sentence.
The counit identifies the reconstructed tower with the given normalized tower; its
constructibility, uniform bounds, and normalization must therefore be invariant under
isomorphism (blueprint: lem-sp-normalized-constructible-tower-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

private theorem reconstruction_constructible_of_iso (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    {F G : Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)} (e : F ≅ G)
    (hF : Scheme.IsConstructibleProEtaleModuleSheaf T A F) :
    Scheme.IsConstructibleProEtaleModuleSheaf T A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' := (Scheme.proEtaleConstantRingPullback A (S.immersion i)).mapIso e
  obtain ⟨I, U, f, hc, ht⟩ := (hS i).1
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, ?_⟩
  · obtain ⟨P, ⟨hP⟩⟩ := ht j
    exact ⟨P, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso e'.symm ≪≫ hP⟩⟩
  · intro Ω _ _ y
    let E := Scheme.geometricRingModuleStalkFunctor y
      (Scheme.proEtaleConstantRing (S.domain i) A)
    have : Finite (E.obj ((Scheme.proEtaleConstantRingPullback A
        (S.immersion i)).obj F)) := (hS i).2 Ω y
    exact Finite.of_injective (E.mapIso e'.symm).toLinearEquiv
      (E.mapIso e'.symm).toLinearEquiv.injective

private theorem reconstruction_tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude T A K a b) :
    Scheme.HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem reconstruction_finite_ctf_of_iso (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    {K L : Scheme.proEtaleDerivedCategory T A} (e : K ≅ L)
    (hK : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hb⟩, hc, c, d, ht⟩ := hK
  refine ⟨⟨a, b, hab, ?_⟩, ?_, c, d, reconstruction_tor_of_iso T A e ht⟩
  · intro i hi
    exact (hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro i
    exact reconstruction_constructible_of_iso T A
      ((DerivedCategory.homologyFunctor _ i).mapIso e) (hc i)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Normalized constructible towers are invariant under isomorphism, retaining the
same cohomological and Tor bounds, without changing the recorded presentation D.
Source: latest blueprint, sk-lem-sp-tower.proof.md, last sentence of Conversely
(blueprint: lem-sp-normalized-constructible-tower-iso).

Proof: apply exact derived evaluation to the isomorphism at each level. Its homology
isomorphisms transport vanishing and constructibility. For constructibility, retain
the strata and covers, compose each local trivialization with the restricted inverse
isomorphism, and transport finiteness through the induced geometric-stalk isomorphism.
The definition of Tor amplitude tests all representatives isomorphic to the object,
so compose those isomorphisms with the inverse given isomorphism. Use the same common
bounds. Finally naturality of every specified reduction expresses the new reduction
as a composite of the old reduction and two isomorphisms, proving normalization. -/
theorem spNormalizedConstructibleTorTowers_of_iso (D : SpCoefficientTowersAbelian l E T)
    {K L : spDerivedCoefficientTowers l E T D} (e : K ≅ L)
    (hK : spNormalizedConstructibleTorTowers l E T D K) :
    spNormalizedConstructibleTorTowers l E T D L := by
  let := D.hasDerived
  have hctf : spConstructibleTorTowers l E T D L := by
    refine ⟨fun n ↦ reconstruction_finite_ctf_of_iso T _
      ((spDerivedCoefficientEvaluation l E T D n).mapIso e) (hK.1.1 n), ?_⟩
    obtain ⟨a, b, c, d, hab, hcd, h⟩ := hK.1.2
    refine ⟨a, b, c, d, hab, hcd, fun n ↦ ⟨?_, ?_⟩⟩
    · intro i hi
      exact ((h n).1 i hi).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso
          ((spDerivedCoefficientEvaluation l E T D n).mapIso e)).symm
    · exact reconstruction_tor_of_iso T _
        ((spDerivedCoefficientEvaluation l E T D n).mapIso e) (h n).2
  refine ⟨hctf, ?_⟩
  intro m n h
  exact (NatTrans.isIso_app_iff_of_iso (D.reduction h) e).1 (hK.2 m n h)

local instance towerIsoInputDerived :
    HasDerivedCategory.{u + 2} (spCoefficientTowers l E T) :=
  HasDerivedCategory.standard _

end AlgebraicGeometry.ProEtale
