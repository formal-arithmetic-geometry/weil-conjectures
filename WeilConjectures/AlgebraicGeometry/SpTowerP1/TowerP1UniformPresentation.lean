/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Data
import WeilConjectures.AlgebraicGeometry.SpTowerP1Uniform.TowerP1UniformCtfDomains

/-! # Constructible tower bounds in the recorded presentation

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md
(blueprint: lem-sp-tower-p1-uniform-presentation).
-/

@[expose] public noncomputable section
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerP1
open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

private theorem constructible_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {F G : proEtaleRingModules T (proEtaleConstantRing T A)} (e : F ≅ G)
    (h : IsConstructibleProEtaleModuleSheaf T A F) :
    IsConstructibleProEtaleModuleSheaf T A G := by
  obtain ⟨strata, hn, hs⟩ := h
  refine ⟨strata, hn, fun i ↦ ?_⟩
  let e' := (proEtaleConstantRingPullback A (strata.immersion i)).mapIso e
  obtain ⟨I, U, f, hc, ht⟩ := (hs i).1
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, ?_⟩
  · obtain ⟨P, ⟨hP⟩⟩ := ht j
    exact ⟨P, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso e'.symm ≪≫ hP⟩⟩
  · intro Ω _ _ y
    let H := geometricRingModuleStalkFunctor y (proEtaleConstantRing (strata.domain i) A)
    have : Finite (H.obj ((proEtaleConstantRingPullback A
        (strata.immersion i)).obj F)) := (hs i).2 Ω y
    exact Finite.of_injective (H.mapIso e'.symm).toLinearEquiv
      (H.mapIso e'.symm).toLinearEquiv.injective

private theorem tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P he f hf hp M i hi
  exact h.2 C P (he.map (fun z ↦ z ≪≫ e.symm)) f hf hp M i hi

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
