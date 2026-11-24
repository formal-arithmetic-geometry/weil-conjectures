/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.RingTheory.FinitePresentationComparisonSystem
import WeilConjectures.RingTheory.FilteredPushoutBijectiveStage

/-! # A finitely presented comparison model reaches a stage

A comparison isomorphism `(colim F ⊗ B₀) ⊗_P Q ≃ colim F ⊗ C₀` over a filtered colimit,
with `P → Q` finitely presented, descends to an isomorphism at some stage.

## Main results

- `RingHom.exists_finitePresentation_model_stage`

## Implementation details

The statement is obtained from the filtered system of finitely presented comparison maps of
`RingHom.exists_finitePresentation_comparison_system` together with
`CommRingCat.exists_bijective_stage_of_filtered_pushouts`. No flatness of `P → Q` is used.

## References

- Stacks Project, Algebra, Tag 02JO (3); Tags 00QO and 05N9 (2), (3).
-/

@[expose] public section

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- Given a finitely presented `F.obj i₀`-algebra map `φ₀ : B₀ → C₀`, finitely presented rings
`ℤ → P → Q`, and an isomorphism `e : (colim F ⊗ B₀) ⊗_P Q ≃ colim F ⊗ C₀` compatible with the
base change of `φ₀`, there are a stage `i ≥ i₀` and an isomorphism
`eᵢ : (F_i ⊗ B₀) ⊗_P Q ≃ F_i ⊗ C₀` compatible with the base change of `φ₀` to `F_i`. -/
theorem exists_finitePresentation_model_stage
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hfp : φ₀.toRingHom.FinitePresentation)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (e : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (he : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      e.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom) :
    ∃ (i : I) (hi : i₀ ≤ i), letI := (F.map (homOfLE hi)).hom.toAlgebra
      ∃ (aPi : Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀)), letI := aPi
        ∃ eᵢ : (↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q ≃+* (↥(F.obj i) ⊗[F.obj i₀] C₀),
          eᵢ.toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom (R := P)
              (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
            (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom := by
  classical
  obtain ⟨i, hi, aPs, D, E, α, d, c, cD, cE, f, hD, hE,
      hfilt, hcomm, hbij, hfpα, hpush, hcompat⟩ :=
    exists_finitePresentation_comparison_system F i₀ B₀ C₀ φ₀ hfp P Q aP e he
  let := hfilt
  obtain ⟨j, hj⟩ := CommRingCat.exists_bijective_stage_of_filtered_pushouts
    D E α cD cE hD hE f hcomm hbij hfpα hpush
  refine ⟨j.val, hi.trans j.property, aPs j, ?_⟩
  let eᵢ := (d j).symm.trans ((RingEquiv.ofBijective (α.app j).hom hj).trans (c j))
  exact ⟨eᵢ, hcompat j⟩

end RingHom
