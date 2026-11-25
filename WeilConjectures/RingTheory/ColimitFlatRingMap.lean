/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.RingTheory.FlatFinitePresentationModel
import WeilConjectures.RingTheory.FinitePresentationModelStage

/-! # Flatness at a stage of a directed colimit

Let `F` be a directed system of rings with colimit `A`, and `φ₀ : B₀ → C₀` a finitely presented
map of `F(i₀)`-algebras. If `A ⊗ B₀ → A ⊗ C₀` is flat, then `F(i) ⊗ B₀ → F(i) ⊗ C₀` is flat for
all sufficiently large `i`.

## Implementation details

The stage is found by approximating the finitely presented map `A ⊗ B₀ → A ⊗ C₀` by a flat
finitely presented map `P → Q` of rings of finite presentation over `ℤ` (via openness of flat
loci over Noetherian rings, the local eventual-flatness criterion [Stacks, Tag 00R6] and
quasi-compactness of `Spec`), and then factoring `P → Q` through some stage. Persistence to
later stages follows from base change of flat maps and tensor cancellation.

## References

* [Stacks, Tag 02JO], part (3)
* [Stacks, Tag 00R6]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w x

namespace RingHom

private theorem finitePresentation_lTensor
    {R A B D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R D]
    (f : B →ₐ[R] D) (hf : f.toRingHom.FinitePresentation) :
    (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom.FinitePresentation := by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom]
  let : Algebra B (TensorProduct R A B) := Algebra.TensorProduct.rightAlgebra
  let e : TensorProduct R A D ≃ₐ[TensorProduct R A B] TensorProduct B (TensorProduct R A B) D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R B D A) x) }
  exact Algebra.FinitePresentation.equiv e.symm

/-- If `φ₀ : B₀ → C₀` is a finitely presented map of `F(i₀)`-algebras whose base change to the
colimit of the directed system `F` is flat, then its base change to some stage `F(i₁)` is
flat. -/
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
  let R := (F.obj i₀ : Type v)
  let A := ((colimit F : CommRingCat) : Type v)
  let : Algebra R A := (colimit.ι F i₀).hom.toAlgebra
  let ψ : (TensorProduct R A B₀) →ₐ[A] (TensorProduct R A C₀) :=
    Algebra.TensorProduct.map (Algebra.ofId A A) φ₀
  have hψfp : ψ.toRingHom.FinitePresentation := finitePresentation_lTensor φ₀ hfp
  obtain ⟨P, Q, cP, cQ, aPQ, aPB, hP, hQ, hPQ, e, he⟩ :=
    exists_flat_finitePresentation_model ψ.toRingHom hψfp hflat
  let : CommRing P := cP
  let : CommRing Q := cQ
  let : Algebra P Q := aPQ
  let : Algebra.FinitePresentation ℤ P := hP
  let : Algebra.FinitePresentation P Q := hQ
  obtain ⟨i, hi, aPi, ei, hei⟩ :=
    exists_finitePresentation_model_stage F i₀ B₀ C₀ φ₀ hfp P Q aPB e he
  refine ⟨i, hi, ?_⟩
  let : Algebra R (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
  let : Algebra P (TensorProduct R (F.obj i) B₀) := aPi
  have : Module.Flat P Q := (RingHom.flat_algebraMap_iff).mp hPQ
  have hbase : (algebraMap (TensorProduct R (F.obj i) B₀)
      (TensorProduct P (TensorProduct R (F.obj i) B₀) Q)).Flat :=
    (RingHom.flat_algebraMap_iff).mpr inferInstance
  rw [← hei]
  exact hbase.comp (Flat.of_bijective ei.bijective)

/-- If the base change of `φ₀ : B₀ → C₀` to `F(i₁)` is flat, then so is its base change to every
later stage `F(i)`. -/
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
  intro i hi
  let R := (F.obj i₀ : Type v)
  let S := (F.obj i₁ : Type v)
  let T := (F.obj i : Type v)
  let : Algebra R S := (F.map (homOfLE h₀)).hom.toAlgebra
  let : Algebra S T := (F.map (homOfLE hi)).hom.toAlgebra
  let : Algebra R T := (F.map (homOfLE (h₀.trans hi))).hom.toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by
    change (F.map (homOfLE (h₀.trans hi))).hom =
      (F.map (homOfLE hi)).hom.comp (F.map (homOfLE h₀)).hom
    rw [← CommRingCat.hom_comp, ← F.map_comp]
    rfl)
  let ψ : TensorProduct R S B₀ →ₐ[S] TensorProduct R S C₀ :=
    Algebra.TensorProduct.map (Algebra.ofId S S) φ₀
  let eB := Algebra.TensorProduct.cancelBaseChange R S T T B₀
  let eC := Algebra.TensorProduct.cancelBaseChange R S T T C₀
  have hf : ψ.toRingHom.Flat := hstage
  have hbase := hf.lTensor (S := T) T
  have heq : Algebra.TensorProduct.map (Algebra.ofId T T) φ₀ =
      eC.toAlgHom.comp
        ((Algebra.TensorProduct.lTensor (S := T) T ψ).comp eB.symm.toAlgHom) := by
    ext z
    change TensorProduct.tmul R (1 : T) (φ₀ z) = eC
      ((Algebra.TensorProduct.lTensor (S := T) T ψ) (eB.symm (TensorProduct.tmul R (1 : T) z)))
    simp [eB, eC, ψ]
  change (Algebra.TensorProduct.map (Algebra.ofId T T) φ₀).toRingHom.Flat
  rw [heq]
  exact Flat.comp (Flat.comp (Flat.of_bijective eB.symm.bijective) hbase)
    (Flat.of_bijective eC.bijective)

/-- If `φ₀ : B₀ → C₀` is a finitely presented map of `F(i₀)`-algebras whose base change to the
colimit of the directed system `F` is flat, then its base change to `F(i)` is flat for all
sufficiently large `i`. -/
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
