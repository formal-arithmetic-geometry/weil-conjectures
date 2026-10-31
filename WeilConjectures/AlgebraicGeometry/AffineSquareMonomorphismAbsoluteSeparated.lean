/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Monomorphisms into an affine square and absolute separatedness

Source: Stacks Project, Spaces, Tag 0265, first proof paragraph
(blueprint: lem-trf-affine-square-monomorphism-absolute-separated).

The absolute base is the terminal scheme, namely the universe-lifted spectrum of the integers.
The comparison map is constructed from the two relative projections by the pullback universal
property. No finite-type or separated-base hypothesis is used.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The canonical map from a relative square to the absolute square, with the same projections.
Source: Stacks Project, Spaces, Tag 0265, first proof paragraph
(blueprint: lem-trf-affine-square-monomorphism-absolute-separated).
The equality needed for the pullback lift holds because the absolute base is terminal. -/
noncomputable def Scheme.relativeToAbsoluteSquare {S U : Scheme.{u}} (f : U ⟶ S) :
    pullback f f ⟶ pullback (terminal.from U) (terminal.from U) :=
  pullback.lift (pullback.fst f f) (pullback.snd f f) (Subsingleton.elim _ _)

/-- A monomorphism into the relative square of an affine scheme embeds monomorphically into
its absolute affine square and has absolutely separated source.
Source: Stacks Project, Spaces, Tag 0265, first proof paragraph
(blueprint: lem-trf-affine-square-monomorphism-absolute-separated).

Proof plan: apply `lem-weil-pbc-fibre-product-affine-spectra`, represented by
`pullbackSpecIso`, over the integers with both algebras equal to `A`, and transport along `e`.
The resulting absolute-square isomorphism respects the two tensor-factor projections.
Cancel the two absolute projections to see that the comparison is monic, using the
uniqueness in `def-pc-fibre-product` for the relative square. Its composite with `j` is
therefore monic. Apply `lem-trf-scheme-monomorphism-separated`, represented by
`IsSeparated.isSeparated_of_mono`, to that composite. Finally apply
`lem-sc-separated-over-affine-scheme-separated`, represented by
`IsSeparated.hasAffineProperty`, since the absolute square is affine by the first step.
This gives separatedness of the structure map of `R` to the terminal scheme. -/
theorem affine_square_monomorphism_absolute_separated
    (S U R : Scheme.{u}) (f : U ⟶ S) (r : R ⟶ S)
    (A : Type u) [CommRing A] (e : U ≅ Spec (CommRingCat.of A))
    (j : R ⟶ pullback f f) (hj : j ≫ pullback.fst f f ≫ f = r) [Mono j] :
    (∃ eP : pullback (terminal.from U) (terminal.from U) ≅
        Spec (CommRingCat.of (A ⊗[ℤ] A)),
      eP.hom ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[ℤ] A)) =
        pullback.fst (terminal.from U) (terminal.from U) ≫ e.hom ∧
      eP.hom ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] A ⊗[ℤ] A).toRingHom) =
        pullback.snd (terminal.from U) (terminal.from U) ≫ e.hom) ∧
    Mono (Scheme.relativeToAbsoluteSquare f) ∧
    Mono (j ≫ Scheme.relativeToAbsoluteSquare f) ∧
    IsSeparated (j ≫ Scheme.relativeToAbsoluteSquare f) ∧
    IsSeparated (terminal.from R) := by
  have _compatibility := hj
  let : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
  have : TensorProduct.CompatibleSMul ℤ (ULift.{u} ℤ) A A := ⟨fun n x y ↦ by
    change (n.down • x) ⊗ₜ[ℤ] y = x ⊗ₜ[ℤ] (n.down • y)
    exact TensorProduct.smul_tmul _ _ _⟩
  let t : A ⊗[ULift.{u} ℤ] A ≃ₐ[ℤ] A ⊗[ℤ] A :=
    Algebra.TensorProduct.equivOfCompatibleSMul ℤ (ULift.{u} ℤ) ℤ A A
  let z : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  let a := Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A))
  let c := pullback.map (terminal.from U) (terminal.from U) a a e.hom e.hom z.hom
    (specULiftZIsTerminal.hom_ext _ _) (specULiftZIsTerminal.hom_ext _ _)
  let eP := asIso c ≪≫ pullbackSpecIso (ULift.{u} ℤ) A A ≪≫
    Scheme.Spec.mapIso t.toRingEquiv.toCommRingCatIso.symm.op
  have hfst : eP.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[ℤ] A)) =
      pullback.fst (terminal.from U) (terminal.from U) ≫ e.hom := by
    change c ≫ (pullbackSpecIso (ULift.{u} ℤ) A A).hom ≫
      Spec.map (CommRingCat.ofHom t.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[ℤ] A) ≫
        CommRingCat.ofHom t.symm.toRingHom =
        CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[ULift.{u} ℤ] A) := by
      ext x
      rfl
    rw [h]
    exact (congrArg (fun k ↦ c ≫ k)
      (pullbackSpecIso_hom_fst (ULift.{u} ℤ) A A)).trans (pullback.lift_fst _ _ _)
  have hsnd : eP.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] A ⊗[ℤ] A).toRingHom) =
      pullback.snd (terminal.from U) (terminal.from U) ≫ e.hom := by
    change c ≫ (pullbackSpecIso (ULift.{u} ℤ) A A).hom ≫
      Spec.map (CommRingCat.ofHom t.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) = _
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] A ⊗[ℤ] A).toRingHom ≫
        CommRingCat.ofHom t.symm.toRingHom =
        CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            A →ₐ[ULift.{u} ℤ] A ⊗[ULift.{u} ℤ] A).toRingHom := by
      ext x
      rfl
    rw [h]
    exact (congrArg (fun k ↦ c ≫ k)
      (pullbackSpecIso_hom_snd (ULift.{u} ℤ) A A)).trans (pullback.lift_snd _ _ _)
  have : Mono (Scheme.relativeToAbsoluteSquare f) := ⟨by
    intro T b d h
    apply pullback.hom_ext
    · simpa [Scheme.relativeToAbsoluteSquare] using
        congrArg (fun k ↦ k ≫ pullback.fst (terminal.from U) (terminal.from U)) h
    · simpa [Scheme.relativeToAbsoluteSquare] using
        congrArg (fun k ↦ k ≫ pullback.snd (terminal.from U) (terminal.from U)) h⟩
  have : IsAffine (pullback (terminal.from U) (terminal.from U)) :=
    .of_isIso eP.hom
  refine ⟨⟨eP, hfst, hsnd⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  have : IsSeparated ((j ≫ Scheme.relativeToAbsoluteSquare f) ≫
      terminal.from (pullback (terminal.from U) (terminal.from U))) := inferInstance
  simpa only [terminal.comp_from] using this

end AlgebraicGeometry
