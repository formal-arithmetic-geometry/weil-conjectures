/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate

/-! # The external Alexander--Whitney differential calculation
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-differential).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The adjacent-degree chain equation for degree maps with the front/back coordinates.
Source: Stacks Project, Tag 07MB, and Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cech-cup-differential).
Proof: Precompose with each tensor-total inclusion. Tensor products are spanned by
pure tensors, so evaluate on a tensor a tensor b and on each product-cover tuple.
Use the prescribed coordinates to expand the target alternating Cech differential.
The omitted vertices before the shared vertex give the differential of a with b;
the vertices after it give a with the differential of b, with sign (-1)^p. The two
shared-vertex contributions are equal by restriction composition and cancel with
opposite signs. Pullback units commute with restriction by naturality, and tensor
sections commute with restriction. Consequently this is the signed Leibniz
identity. The tensor-total differential has exactly the same two terms, so the
inclusion composites agree. The coproduct universal property concludes the equation
in each adjacent degree. Empty covers give vacuous coordinate equations; the
identity is bilinear and remains valid for zero coefficients and in degree zero. -/
theorem picardExternalCechCupDegreeMaps_comm
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hl : ∀ p q, IsPicardExternalCechCupBidegree f g U V F G p q (l p q)) (n : ℕ) :
    picardExternalCechCupDegreeMaps f g U V F G l n ≫
        ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).d n (n + 1) =
      (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).d n (n + 1) ≫
        picardExternalCechCupDegreeMaps f g U V F G l (n + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  exact picardExternalCechCupDegreeMaps_comm_ι f g U V F G l hl n p q hpq

end
end AlgebraicGeometry.Scheme.Modules
