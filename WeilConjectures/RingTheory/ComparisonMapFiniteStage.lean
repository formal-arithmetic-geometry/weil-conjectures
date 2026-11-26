/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.RingTheory.TensorAlgebraStructureFiniteStage
import WeilConjectures.RingTheory.TensorRightFactorFiniteStage

/-! # Finite-stage descent of a compatible tensor comparison

A comparison map over the colimit of a directed system of rings, defined using finitely
presented data, descends to a compatible comparison map at a finite stage.

## Implementation details

The structure map `P → colim F ⊗ B₀` factors through a stage since `P` is finitely presented
over `ℤ`, and the `P`-algebra map `Q → colim F ⊗ C₀` factors through a later stage since `Q` is
finitely presented over `P`. The descended map is the tensor product universal map. No
finite-presentation hypothesis on `φ₀` is used.

## References

* [Stacks, Tag 02JO] (3), construction of `Ψ`
* [Stacks, Tag 00QO]
* [Stacks, Tag 00DD]
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- Let `P → Q` be finitely presented with `P` finitely presented over `ℤ`, and let
`g : (colim F ⊗ B₀) ⊗[P] Q → colim F ⊗ C₀` restrict to the base change of `φ₀`. Then at some
stage `i ≥ i₀` there is a `P`-structure on `F(i) ⊗ B₀` and a comparison map
`ψ : (F(i) ⊗ B₀) ⊗[P] Q → F(i) ⊗ C₀` restricting to the base change of `φ₀` and compatible with
`g`. -/
theorem exists_comparison_map_finite_stage
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (g : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q →+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (he : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      g.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom) :
    ∃ (i : I) (hi : i₀ ≤ i),
    letI := (colimit.ι F i₀).hom.toAlgebra
    letI := (F.map (homOfLE hi)).hom.toAlgebra
    let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
      { (colimit.ι F i).hom with
        commutes' := fun s ↦
          congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
      ∃ (aPi : Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀)),
        letI := aPi
        letI := aP
        ∃ (μB : (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P]
            (↥(colimit F) ⊗[F.obj i₀] B₀)),
          μB.toRingHom =
            (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀)).toRingHom ∧
          ∃ (ψ : ((↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q) →+*
              (↥(F.obj i) ⊗[F.obj i₀] C₀)),
            ψ.comp (Algebra.TensorProduct.includeLeftRingHom (R := P)
                (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
              (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom ∧
            (Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)).toRingHom.comp ψ =
              g.comp (Algebra.TensorProduct.map μB (AlgHom.id P Q)).toRingHom
    := by
  let := (colimit.ι F i₀).hom.toAlgebra
  let := aP
  let f := g.comp (Algebra.TensorProduct.includeRight (R := P)
    (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)).toRingHom
  have hf : f.comp (algebraMap P Q) =
      (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom.comp
        (algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀)) := by
    apply RingHom.ext
    intro r
    change g (1 ⊗ₜ[P] algebraMap P Q r) =
      (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀)
        (algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀) r)
    trans g (algebraMap P (↥(colimit F) ⊗[F.obj i₀] B₀) r ⊗ₜ[P] 1)
    · congr 1
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul r).symm
    · exact RingHom.congr_fun he _
  obtain ⟨j, hj, aPj, μBj, hμBj⟩ :=
    exists_tensor_algebra_structure_finite_stage F i₀ B₀ P aP
  obtain ⟨i, hi, aPi, μB, hμB, q, hq, hqf⟩ :=
    exists_tensor_right_factor_finite_stage F i₀ B₀ C₀ φ₀ P Q aP
      j hj aPj μBj hμBj f hf
  let := (F.map (homOfLE hi)).hom.toAlgebra
  let := aPi
  let αi : F.obj i →ₐ[F.obj i₀] ↥(colimit F) :=
    { (colimit.ι F i).hom with
      commutes' := fun s ↦
        congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE hi)) }
  let φi := Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀
  let μC := Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) C₀)
  let := (φi.toRingHom.comp (algebraMap P (↥(F.obj i) ⊗[F.obj i₀] B₀))).toAlgebra
  let φiP : (↥(F.obj i) ⊗[F.obj i₀] B₀) →ₐ[P]
      (↥(F.obj i) ⊗[F.obj i₀] C₀) :=
    { φi.toRingHom with commutes' := fun _ ↦ rfl }
  let qP : Q →ₐ[P] (↥(F.obj i) ⊗[F.obj i₀] C₀) :=
    { q with commutes' := fun r ↦ RingHom.congr_fun hq r }
  let ψ := (Algebra.TensorProduct.productMap φiP qP).toRingHom
  refine ⟨i, hi, aPi, μB, hμB, ψ, ?_, ?_⟩
  · apply RingHom.ext
    intro b
    exact Algebra.TensorProduct.productMap_left_apply φiP qP b
  · apply Algebra.TensorProduct.ringHom_ext
    · apply RingHom.ext
      intro b
      change μC (ψ (b ⊗ₜ[P] 1)) = g (μB b ⊗ₜ[P] 1)
      simp only [ψ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.productMap_left_apply]
      have hleft := RingHom.congr_fun he (μB b)
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply] at hleft
      rw [hleft]
      rw [show μB b = Algebra.TensorProduct.map αi (AlgHom.id (F.obj i₀) B₀) b from
        RingHom.congr_fun hμB b]
      clear hleft
      induction b using TensorProduct.inductionOn with
      | tmul a b => simp [μC, φiP, φi, Algebra.TensorProduct.map_tmul]
      | add b c hb hc => simpa only [map_add] using congrArg₂ (· + ·) hb hc
    · apply RingHom.ext
      intro r
      change μC (ψ (1 ⊗ₜ[P] r)) =
        g (Algebra.TensorProduct.map μB (AlgHom.id P Q) (1 ⊗ₜ[P] r))
      simp only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      change μC (Algebra.TensorProduct.productMap φiP qP (1 ⊗ₜ[P] r)) =
        g (1 ⊗ₜ[P] r)
      rw [Algebra.TensorProduct.productMap_right_apply]
      exact RingHom.congr_fun hqf r

end RingHom
