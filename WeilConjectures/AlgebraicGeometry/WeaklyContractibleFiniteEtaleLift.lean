/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Sites.Subcanonical
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Lifting finite etale covers over weakly contractible objects -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

private theorem section_of_cover {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [J.Subcanonical] {P W : C} (f : P ⟶ W)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J W)
    (hW : J.IsWeaklyContractible.{u + 1} W) : ∃ s : W ⟶ P, s ≫ f = 𝟙 W := by
  have hloc : Sheaf.IsLocallySurjective (J.uliftYoneda.{u + 1}.map f) := by
    constructor
    intro U s
    apply J.superset_covering ?_ (J.pullback_stable s.down hf)
    intro V a ha
    obtain ⟨Z, b, c, hc, hbc⟩ := ha
    cases hc
    exact ⟨ULift.up b, by apply ULift.ext; exact hbc⟩
  obtain ⟨s, hs⟩ := hW _ hloc (ULift.up (𝟙 W))
  exact ⟨s.down, congrArg ULift.down hs⟩

/-- A finite etale surjection to X lifts the structure map of every weakly
contractible object W of X_proet. The singleton cover remains covering after
base change to W. The associated representable map is locally surjective, and
weak contractibility lifts the identity of W to a section. Its other projection
is the claimed lift.
Source: the final lifting paragraph of the scope counterexample.
(blueprint: lem-sf-weakly-contractible-finite-etale-lift) -/
theorem weaklyContractibleFiniteEtaleLift {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Etale f] [Surjective f] (W : X.ProEt)
    (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W) :
    ∃ s : W.left ⟶ Y, s ≫ f = W.hom := by
  have hf : Presieve.ofArrows (fun _ : PUnit.{1} ↦ Y) (fun _ ↦ f) ∈
      Scheme.proetalePrecoverage X := by
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage inferInstance
  have hcov := Scheme.ProEt.ofArrows_baseChange_mem_topology W (fun _ : PUnit.{1} ↦ f) hf
  rw [Sieve.ofArrows, Presieve.ofArrows_pUnit] at hcov
  obtain ⟨s, hs⟩ := section_of_cover _ (Scheme.ProEt.baseChangeHom f W) hcov hW
  refine ⟨s.left ≫ pullback.snd W.hom f, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  have hs' := congrArg (fun a ↦ a.left) hs
  change s.left ≫ pullback.fst W.hom f = 𝟙 _ at hs'
  rw [hs', Category.id_comp]

end AlgebraicGeometry
