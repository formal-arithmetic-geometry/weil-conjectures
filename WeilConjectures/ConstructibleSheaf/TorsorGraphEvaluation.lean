/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
import WeilConjectures.Mathlib.CategoryTheory.Extensive

/-!
# Equivariant functions are determined on the graph of a torsor section

## Implementation details

Base changing the torsor isomorphism along a section `f` splits `W ×_V c.P` into copies of `W`
indexed by the group, the `g`-th copy being the graph of `f` translated by `g`. Two equivariant
functions agreeing on the graph therefore agree on every translate. No connectedness,
primality or sheaf condition is used.

## References

* [Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R]
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- Evaluation on the graph of a torsor section `f` over `W` determines an equivariant locally
constant function on `W ×_V c.P`. -/
theorem graphEvaluation_injective
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (N : Rep.{u + 1} (ZMod ℓ) P) (W : V.Etale)
    (f : W ⟶ c.sectionObject) :
    Function.Injective (fun s : c.equivariantSections ℓ N W ↦
      LocallyConstant.comap
        (pullback.lift (f := W.hom) (g := c.π) (𝟙 W.left) f.left
          (by simpa using (MorphismProperty.Over.w f).symm)).base.hom s.val) := by
  let D := Sigma.desc fun g : ULift.{u + 1} P ↦
    pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P) (by simp [c.smul_π])
  have : IsIso D := c.isIso_sigmaDesc
  let E := Sigma.desc fun g : ULift.{u + 1} P ↦
    pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (c.smul g) (by simp [c.smul_π])
  have hE : E = D ≫ (pullbackSymmetry c.π c.π).hom := by
    apply Sigma.hom_ext
    intro g
    apply pullback.hom_ext <;> simp [E, D]
  have : IsIso E := by rw [hE]; infer_instance
  have hw : f.left ≫ c.π = W.hom := MorphismProperty.Over.w f
  let T := Sigma.desc fun g : ULift.{u + 1} P ↦
    pullback.lift (f := f.left ≫ c.π) (g := c.π) (𝟙 W.left)
      (f.left ≫ c.smul g) (by simp [c.smul_π])
  have : IsIso T := FinitaryPreExtensive.isIso_sigmaDesc_lift_comp
    c.π c.smul c.smul_π f.left
  let graph : W.left ⟶ c.sectionSpace W :=
    pullback.lift (𝟙 W.left) f.left hw.symm
  let S : (∐ fun _ : ULift.{u + 1} P ↦ W.left) ⟶ c.sectionSpace W :=
    Sigma.desc fun g ↦ graph ≫ c.sectionAction W g.down
  have hS : IsIso S := by
    have hST : S = T ≫ (pullback.congrHom hw rfl).hom := by
      apply Sigma.hom_ext
      intro g
      apply pullback.hom_ext <;>
        simp [S, T, graph, sectionAction, pullback.congrHom]
    rw [hST]
    infer_instance
  have hs : Function.Surjective S := by
    have := hS
    exact Surjective.surj (f := S)
  intro a b hab
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  obtain ⟨z, hz⟩ := hs x
  obtain ⟨g, w, hwz⟩ := (sigmaOpenCover fun _ : ULift.{u + 1} P ↦ W.left).exists_eq z
  have hpoint : c.sectionAction W g.down (graph w) = x := by
    have ht := congrArg (fun k ↦ S k) hwz
    have hi : Sigma.ι (fun _ : ULift.{u + 1} P ↦ W.left) g ≫ S =
        graph ≫ c.sectionAction W g.down := by simp [S]
    rw [← Scheme.Hom.comp_apply, ← hi, Scheme.Hom.comp_apply]
    exact ht.trans hz
  rw [← hpoint, a.property, b.property]
  congr 1
  exact congrArg (fun t : LocallyConstant W.left N.V ↦ t w) hab

end AlgebraicGeometry.Scheme.GaloisCover
