/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.PicardRightCechCupConstruction
public import Sheaf.AlgebraicGeometry.PicardKunnethResolutionModel
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Geometric comparison on external Cech tensor cocycles

Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech; Tags 01FD, 07MB, 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-cycle-comparison).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- Factor and product affine comparisons identify the specified external Cech
cup on tensor cocycles. This asserts no tensor Kunneth equivalence.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech and the sentence
identifying its cohomology map; Cohomology Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-cycle-comparison).

Proof: Affine relative diagonals make every nonempty finite intersection of the
factor covers affine. The intersections of the product cover are fibre products
of these affine intersections over Spec k, hence affine. The product opens cover
the fibre product. The external coefficient is quasi-coherent by pullback and
tensor quasi-coherence. Apply the canonical affine Cech comparisons to both
factor coefficients and the product coefficient. Restriction of scalars is
exact and commutes with the products in each Cech term, so the comparisons are
k-linear. Compose the factor comparisons with the inverse fixed scalar-model
comparisons to get alpha and beta. For the product also use the zero-extension
homology isomorphism, giving b. Choose these comparisons together, in all degrees.
For factor cocycles a and v, the inclusion of z is the tensor of their inclusions
in the indicated total summand. The htheta coordinates compute its image on each
product-cover tuple as the front X section and back Y section pulled back by the
projection adjunction units and tensored. The projection refinements followed by
Cech cup have exactly these coordinates. Tag 01FD identifies the refinement maps
with pullback on cohomology, and Tag 0FKV identifies Cech cup with sheaf cup.
The fixed scalar-resolution comparison and its Ext identification give precisely
externalCup of the two displayed factor classes. Extension homology transports
this class to the integer complex without changing the natural-degree formula.
The degree cast implements p+q=n. Monicity of iCycles makes the assertion hold
for every z with the given inclusion. Empty covers force empty factors, and zero
coefficients give zero classes. In degree zero this is the section tensor pairing.
No invertibility of external cup, or tensor-total Kunneth, is used. -/
theorem picardRightCechCup_cycle_comparison
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
    (G : Y.Modules) [G.IsQuasicoherent] :
    let A := (picardCechFunctor f U).obj F
    let B := (picardCechFunctor g V).obj G
    let T := HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ)
    ∃ (alpha : ∀ p : ℕ, A.homology p ≃ₗ[k] (picardScalarModel f F).homology (p : ℤ))
      (beta : ∀ q : ℕ, B.homology q ≃ₗ[k] (picardScalarModel g G).homology (q : ℤ))
      (b : ∀ n : ℕ,
        ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
          (picardScalarModel (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G)).homology (n : ℤ)),
      ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
        (a : A.cycles i.val.1) (v : B.cycles i.val.2) (z : T.cycles n),
        T.iCycles n z =
          HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ) i.val.1 i.val.2 n i.property
              ((A.iCycles i.val.1 a) ⊗ₜ[k] (B.iCycles i.val.2 v)) →
        picardScalarModelEquiv (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) n
          ((b n).hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
            ((T.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv
              (T.homologyπ n z)))) =
          cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G) d)) i.property)
            (externalCup f g F G i.val.1 i.val.2
              (picardScalarModelEquiv f F i.val.1 (alpha i.val.1 (A.homologyπ _ a)))
              (picardScalarModelEquiv g G i.val.2 (beta i.val.2 (B.homologyπ _ v)))) :=
  by sorry

end AlgebraicGeometry.Scheme.Modules
