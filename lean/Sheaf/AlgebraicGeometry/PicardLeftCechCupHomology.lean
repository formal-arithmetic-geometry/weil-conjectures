/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.PicardLeftCechCupConstruction
public import Sheaf.AlgebraicGeometry.PicardExternalCupHomologyUnique

/-! # Comparison of the specified left Cech cup on cycles

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
Cohomology, Tags 01FD and 0FKV.
(blueprint: lem-sc-picard-left-cech-cup-homology).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Affine comparisons transport a cochain-specified cup to the scalar tensor cycles.
Source: Stacks, Tag 0BED, equation-kunneth-on-cech; Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-left-cech-cup-homology).

Proof: The finite affine covers cover X and Y. Affine relative diagonals over
Spec k make all their nonempty finite intersections affine. Intersections in the
product cover are the fibre products of these affine intersections over Spec k,
so are affine and cover the product. The external coefficient is quasi-coherent
since tensor pullback and tensor preserve quasi-coherence. Apply the canonical
affine Cech comparison on each factor and on the product. Exact restriction of
scalars makes these k-linear homology isomorphisms. Compose the product comparison
with the inverse fixed scalar-resolution comparison and extension homology
isomorphism to obtain b. Tensor Kunneth on the extended factor Cech complexes and
on the scalar models, composed with tensor products of the factor comparisons,
gives a. Choose these comparison isomorphisms in every natural degree.
To check normalization, represent the scalar factor classes by cycles and use
the factor comparisons to represent them by Cech cycles. The tensor Kunneth
cycle formula identifies the transported total class with the tensor of those
Cech cycles. The hypothesis specifies theta on each bidegree cochain summand:
its tuple values are pullback to the front/back intersection followed by section
tensor. Cech refinement compatibility identifies the corresponding class with
projection pullbacks followed by Cech cup. Compatibility of Cech comparison with
sheaf cup identifies its product comparison with externalCup. The canonical
scalar resolution comparisons identify the factor classes with exactly the
scalar classes occurring in the normalization predicate. Extension by zero adds
no negative classes and the equality p+q=n gives the displayed degree transport.
This checks every pair of cycles and every total cycle representing their tensor;
it does not assert invertibility of externalCup. Empty schemes and zero
coefficients have zero cohomology; degree zero gives the section tensor formula.
The cochain-coordinate hypothesis is essential: arbitrary theta need not satisfy
this conclusion. -/
theorem picardLeftCechCup_homology
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (G : Y.Modules) [G.IsQuasicoherent]
    (θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G)
    (hθ : IsPicardLeftCechCup f g G θ)
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (a : ∀ n : ℕ,
        ((picardLeftTensorCechFunctor f g G).obj F).homology (n : ℤ) ≅
          (picardExternalTotal f g F G).homology (n : ℤ))
      (b : ∀ n : ℕ,
        ((picardLeftProductCechFunctor f g G).obj F).homology (n : ℤ) ≅
          (picardScalarModel (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G)).homology (n : ℤ)),
      IsPicardExternalCupHomology f g F G (fun n ↦
        (a n).inv ≫ HomologicalComplex.homologyMap (θ.app F) (n : ℤ) ≫ (b n).hom) :=
  by sorry

end
end AlgebraicGeometry.Scheme.Modules
