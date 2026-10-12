module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
import Sheaf.Algebra.LimitFinitePresentation
import Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Sheaf.Paper.DirectedColimitBaseChangeElementwise
import Sheaf.RingTheory.ColimitCategoryFpAlgebras
import Sheaf.RingTheory.ColimitEventuallyFlat
import Sheaf.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import Sheaf.RingTheory.OpenFlatLocus

/-! # Flatness at a stage of a directed colimit -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w x

namespace RingHom

/-- Intermediate existence statement (blueprint: lem-weil-pbc-colimit-flat-ring-map-stage).
Proof: descend flatness to one stage. -/
theorem exists_flat_stage_of_colimit_flat
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hfp : φ₀.toRingHom.FinitePresentation)
    (hflat : letI := (colimit.ι F i₀).hom.toAlgebra
      (Algebra.TensorProduct.map
        (R := ((F.obj i₀ : CommRingCat) : Type v))
        (S := ((colimit F : CommRingCat) : Type v))
        (A := ((colimit F : CommRingCat) : Type v)) (B := B₀)
        (C := ((colimit F : CommRingCat) : Type v)) (D := C₀)
        (Algebra.ofId ((colimit F : CommRingCat) : Type v)
          ((colimit F : CommRingCat) : Type v)) φ₀).toRingHom.Flat) :
    ∃ i₁ : I, ∃ h₀ : i₀ ≤ i₁, letI :=
      (F.map (homOfLE h₀)).hom.toAlgebra
      (Algebra.TensorProduct.map
        (R := ((F.obj i₀ : CommRingCat) : Type v)) (S := ((F.obj i₁ : CommRingCat) : Type v))
        (A := ((F.obj i₁ : CommRingCat) : Type v)) (B := B₀)
        (C := ((F.obj i₁ : CommRingCat) : Type v)) (D := C₀)
        (Algebra.ofId (F.obj i₁) (F.obj i₁)) φ₀).toRingHom.Flat := by
  sorry

/-- Intermediate persistence statement
(blueprint: lem-weil-pbc-colimit-flat-ring-map-persistence).
Proof: base change preserves flatness. -/
theorem eventually_flat_of_flat_stage
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ i₁ : I) (h₀ : i₀ ≤ i₁) (B₀ : Type w) (C₀ : Type x)
    [CommRing B₀] [CommRing C₀] [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (hstage : letI := (F.map (homOfLE h₀)).hom.toAlgebra
      (Algebra.TensorProduct.map
        (R := ((F.obj i₀ : CommRingCat) : Type v)) (S := ((F.obj i₁ : CommRingCat) : Type v))
        (A := ((F.obj i₁ : CommRingCat) : Type v)) (B := B₀)
        (C := ((F.obj i₁ : CommRingCat) : Type v)) (D := C₀)
        (Algebra.ofId (F.obj i₁) (F.obj i₁)) φ₀).toRingHom.Flat) :
    ∀ i : I, ∀ hi : i₁ ≤ i, letI := (F.map (homOfLE (h₀.trans hi))).hom.toAlgebra
      (Algebra.TensorProduct.map
        (R := ((F.obj i₀ : CommRingCat) : Type v)) (S := ((F.obj i : CommRingCat) : Type v))
        (A := ((F.obj i : CommRingCat) : Type v)) (B := B₀)
        (C := ((F.obj i : CommRingCat) : Type v)) (D := C₀)
        (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom.Flat := by
  sorry

theorem exists_eventually_flat_of_colimit_flat
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I)
    (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀)
    (hfp : φ₀.toRingHom.FinitePresentation)
    (hflat : letI := (colimit.ι F i₀).hom.toAlgebra
      (Algebra.TensorProduct.map
        (R := ((F.obj i₀ : CommRingCat) : Type v)) (S := ((colimit F : CommRingCat) : Type v))
        (A := ((colimit F : CommRingCat) : Type v)) (B := B₀)
        (C := ((colimit F : CommRingCat) : Type v)) (D := C₀)
        (Algebra.ofId ((colimit F : CommRingCat) : Type v)
          ((colimit F : CommRingCat) : Type v)) φ₀).toRingHom.Flat) :
    ∃ i₁ : I, ∃ h₀ : i₀ ≤ i₁, ∀ i : I, ∀ hi : i₁ ≤ i,
      letI := (F.map (homOfLE (h₀.trans hi))).hom.toAlgebra
      (Algebra.TensorProduct.map
        (R := ((F.obj i₀ : CommRingCat) : Type v)) (S := ((F.obj i : CommRingCat) : Type v))
        (A := ((F.obj i : CommRingCat) : Type v)) (B := B₀)
        (C := ((F.obj i : CommRingCat) : Type v)) (D := C₀)
        (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom.Flat := by
  obtain ⟨i₁, h₀, hstage⟩ := exists_flat_stage_of_colimit_flat F i₀ B₀ C₀ φ₀ hfp hflat
  exact ⟨i₁, h₀, eventually_flat_of_flat_stage F i₀ i₁ h₀ B₀ C₀ φ₀ hstage⟩

end RingHom
