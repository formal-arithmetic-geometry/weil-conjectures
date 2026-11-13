/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.EtaleBaseChangePolynomialCertificate
import WeilConjectures.RingTheory.EtalePolynomialCertificateColimit

/-!
# Descent of etaleness along a directed colimit of rings

Source: Stacks Project, Algebra, Lemma 10.168.7 (Tag 07RI).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A finitely presented map of algebras over a stage of a directed system is etale
at some later stage if its base change to the colimit is etale.
Source: Stacks Project, Algebra, Lemma 10.168.7 (Tag 07RI). -/
theorem Etale.exists_stage_of_directedColimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ C₀ : Type v) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hfp : φ₀.FinitePresentation) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (colimit.ι F i₀).hom.toAlgebra
    Etale (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj i₀) (colimit F : CommRingCat.{u})) φ₀).toRingHom)) →
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
      Etale (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) (F.obj i)) φ₀).toRingHom)) := by
  obtain ⟨n, m, f, hf⟩ := exists_etale_baseChange_polynomialCertificate B₀ C₀ φ₀ hfp
  let : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
    (colimit.ι F i₀).hom.toAlgebra
  intro h
  have hc := (hf (colimit F : CommRingCat.{u})).mp h
  obtain ⟨i, hi, hcᵢ⟩ :=
    Algebra.exists_stage_etalePolynomialCertificate F i₀ B₀ n m f hc
  refine ⟨i, hi, ?_⟩
  let : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
  exact (hf (F.obj i)).mpr hcᵢ

end AlgebraicGeometry
