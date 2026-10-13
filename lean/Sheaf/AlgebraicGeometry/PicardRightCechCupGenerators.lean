/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.AlgebraicGeometry.PicardRightCechCupConstruction
public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.DirectSum.Module

/-! # Specified external Cech cup on factor homology generators

Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; Tags 01FD, 07MB, 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-generators).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme.Modules

/-- The specified external Cech cup takes each pure factor-homology tensor to
external cup, in compatible Cech comparison coordinates. This statement concerns
only generators of the direct sum, and does not compare with scalar-total cycles.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; Tags 01FD, 07MB, 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-generators).

Proof: The affine diagonal criterion makes each nonempty finite factor intersection
affine. Intersections of the product cover are products of these affine opens over
Spec k and are affine; the product cover covers the fibre product. Pullback and tensor
preserve quasi-coherence. Apply the canonical affine Cech comparisons to the two
factors and the product coefficient. Restriction of scalars is exact and commutes
with the finite products in each Cech term. Compose the product comparison with the
inverse fixed-resolution comparison and extension homology to obtain b. Tensor the
factor comparisons on each direct-sum summand, then apply tensor Kunneth to the
extended factor Cech complexes. The canonical comparison between extension of the
natural tensor total and the tensor total of extensions yields e.
For x and y, lift their images under the factor comparisons to Cech cycles. Tensor
Kunneth represents their summand tensor by the total tensor cycle. The given hθ
identifies its image tuple by tuple with the front X section and back Y section
pulled back by the projection adjunction units and tensored. Refinement/pullback
compatibility and Cech/sheaf-cup compatibility send this class under the canonical
product comparison to externalCup of the factor classes. The fixed resolution
comparisons identify those classes with the displayed scalar-model equivalences.
The cast implements the equality p+q=n. All choices of comparisons here are made
together with this formula; independent rescaling of b is not allowed. Empty covers
cover only empty schemes, whose coefficient cohomology vanishes. Zero coefficients
likewise give zero spaces. In degree zero the formula is the section tensor pairing. -/
theorem picardRightCechCup_generators
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F)
    (hθ : IsPicardRightCechCup f g U V F θ)
    (G : Y.Modules) [G.IsQuasicoherent] (n : ℕ) :
        ∃ (e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
              (picardScalarModel f F).homology (i.val.1 : ℤ) ⊗[k]
                (picardScalarModel g G).homology (i.val.2 : ℤ)) ≃ₗ[k]
              ((picardRightTensorCechFunctor f g U V F).obj G).homology (n : ℤ))
          (b : ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
            (picardScalarModel (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G)).homology (n : ℤ)),
          ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
            (x : (picardScalarModel f F).homology (i.val.1 : ℤ))
            (y : (picardScalarModel g G).homology (i.val.2 : ℤ)),
            picardScalarModelEquiv (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) n
              (b.hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
                (e (DirectSum.lof k _ _ i (x ⊗ₜ[k] y))))) =
              cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) d)) i.property)
                (externalCup f g F G i.val.1 i.val.2
                  (picardScalarModelEquiv f F i.val.1 x)
                  (picardScalarModelEquiv g G i.val.2 y)) := by sorry

end AlgebraicGeometry.Scheme.Modules
