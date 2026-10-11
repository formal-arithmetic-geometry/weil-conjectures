/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricProductSections
public import Sheaf.AlgebraicGeometry.SymmetricProductPolynomial
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# No common zero and permutation invariance

Source: Weil conjectures blueprint, symmetric-product-properties, parts (a)--(d);
Stacks Project, Etale Cohomology, proof of Tag 0A4F, and Constructions, Tags 01NE and 01NG
(blueprint: lem-weil-pbc-symmetric-product-properties).

The positive integer n is written m + 1. The product is described by its universal
cone in schemes over S; this applies in particular to the inductively formed fibre product.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Classical in
/-- The coefficient formula, multidegree, generation, coordinate morphism and its
invariance under permutations of the factors.

Source: blueprint symmetric-product-properties, parts (a)--(d); Stacks Tag 0A4F
(blueprint: lem-weil-pbc-symmetric-product-properties).

Proof:
1. Expand the product of linear forms using product-linear-forms-coefficients. Each
   monomial uses precisely one variable from each pair. Tensoring the corresponding
   pulled-back sections gives F_j in L_n; invertible-pullback-tensor gives invertibility.
2. The two coordinate sections have no common zero: the standard opens D_+(T_0),
   D_+(T_1) cover P^1 (01NG), and T_k is a basis on its own chart. Pullback preserves
   their fibrewise nonvanishing by invertible-pullback-tensor.
3. At a point choose bases of the factor fibres. The scalar polynomial is a product
   of nonzero linear polynomials over the residue field, hence nonzero. Some coefficient
   is nonzero. The invertible-generating-sections-fibre criterion gives the epimorphism.
4. Apply projective-space-functor-of-points (01NE) and the recorded morphism-by-sections
   construction to obtain sigma_n, its projections and its section-preserving isomorphism.
5. The product universal property constructs the permutation automorphism and its
   inverse. Pullback-composition and tensor symmetry give beta. Permuting the subsets
   in the tensor coefficient formula proves beta(tau^* F_j) = F_j.
6. Both composites to S agree. The integral composites agree because pullback of the
   generating pair is isomorphic via beta to the original pair, and 01NE gives uniqueness.
   The fibre-product universal property gives tau followed by sigma_n equals sigma_n. -/
theorem symmetricProduct_properties (S : Scheme.{v}) (m : ℕ)
    (X : Over S)
    (pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift.{v} (Fin 2); S) ↘ S)))
    (_hprod : IsLimit (Fan.mk X pr)) :
    (∀ j : Fin (m + 2),
      symmetricProductPolynomial (m + 1) (Nat.zero_lt_succ m) j =
        ∑ J ∈ (Finset.univ : Finset (Fin (m + 1))).powerset.filter
            (fun J ↦ J.card = j.val),
          (∏ i ∈ J, MvPolynomial.X (Sum.inl i)) *
            ∏ i ∈ (Finset.univ : Finset (Fin (m + 1))) \ J,
              MvPolynomial.X (Sum.inr i)) ∧
    (∀ j : Fin (m + 2),
      ∀ d ∈ (symmetricProductPolynomial (m + 1) (Nat.zero_lt_succ m) j).support,
        ∀ i : Fin (m + 1), d (Sum.inl i) + d (Sum.inr i) = 1) ∧
    (∀ z : X.left, ∃ j : ULift.{v} (Fin (m + 2)),
      z ∈ Scheme.Modules.nonvanishingLocus
        (symmetricProductLineBundle (fun i ↦ (pr i).left))
        ((symmetricProductCoordinateSection (fun i ↦ (pr i).left) j).val
          (Opposite.op ⊤))) ∧
    ∃ (hL : (symmetricProductLineBundle (fun i ↦ (pr i).left)).IsInvertible)
      (hs : Epi ((symmetricProductLineBundle (fun i ↦ (pr i).left)).freeHomEquiv.symm
        (symmetricProductCoordinateSection (fun i ↦ (pr i).left)))),
      ∃ σ : X.left ⟶ ℙ(ULift.{v} (Fin (m + 2)); S),
        σ = @ProjectiveSpace.homOfGeneratingSections.{v}
          (ULift.{v} (Fin (m + 2))) _ X.left S X.hom
          (symmetricProductLineBundle (fun i ↦ (pr i).left)) hL
          (symmetricProductCoordinateSection (fun i ↦ (pr i).left)) hs ∧
        σ ≫ ℙ(ULift.{v} (Fin (m + 2)); S) ↘ S = X.hom ∧
        ∃ ψ : X.left ⟶ ℙ(ULift.{v} (Fin (m + 2)); Spec (CommRingCat.of (ULift.{v} ℤ))),
          σ ≫ ProjectiveSpace.toProjInt _ S = ψ ≫ ProjectiveSpace.toProjInt _ _ ∧
          (∃ e : (Scheme.Modules.tensorPullback ψ).obj
              (ProjectiveSpace.twist (ULift.{v} (Fin (m + 2)))
                (Spec (CommRingCat.of (ULift.{v} ℤ))) 1) ≅
              symmetricProductLineBundle (fun i ↦ (pr i).left),
            ∀ j : ULift.{v} (Fin (m + 2)),
              e.hom.app ⊤ (((Classical.choose
                (Scheme.Modules.exists_tensorPullbackAdjunction ψ)).unit.app
                  (ProjectiveSpace.twist (ULift.{v} (Fin (m + 2)))
                    (Spec (CommRingCat.of (ULift.{v} ℤ))) 1)).val.app (Opposite.op ⊤)
                      (ProjectiveSpace.twistOneSection _ _ j)) =
                (symmetricProductCoordinateSection (fun i ↦ (pr i).left) j).val
                  (Opposite.op ⊤)) ∧
          ∀ π : Equiv.Perm (Fin (m + 1)), ∃ τ : X ≅ X,
            (∀ i, τ.hom ≫ pr i = pr (π i)) ∧
            (∀ i, τ.inv ≫ pr i = pr (π.symm i)) ∧
            (∃ β : (Scheme.Modules.tensorPullback τ.hom.left).obj
                (symmetricProductLineBundle (fun i ↦ (pr i).left)) ≅
                symmetricProductLineBundle (fun i ↦ (pr i).left),
              ∀ j : ULift.{v} (Fin (m + 2)),
                β.hom.app ⊤ (((Classical.choose
                  (Scheme.Modules.exists_tensorPullbackAdjunction τ.hom.left)).unit.app
                    (symmetricProductLineBundle (fun i ↦ (pr i).left))).val.app
                      (Opposite.op ⊤)
                        ((symmetricProductCoordinateSection (fun i ↦ (pr i).left) j).val
                          (Opposite.op ⊤))) =
                  (symmetricProductCoordinateSection (fun i ↦ (pr i).left) j).val
                    (Opposite.op ⊤)) ∧
            τ.hom.left ≫ σ = σ := by
  sorry

end AlgebraicGeometry
