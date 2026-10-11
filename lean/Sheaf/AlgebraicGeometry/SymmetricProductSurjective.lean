/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import Sheaf.AlgebraicGeometry.SymmetricProductProperties

/-!
# Surjectivity of the symmetric-product morphism

Source: Weil conjectures blueprint, `lem-weil-pbc-symmetric-product-surjective`, order 1202;
Stacks Project, Etale Cohomology, proof of Lemma 0A4F.
(blueprint: lem-weil-pbc-symmetric-product-surjective)

The positive integer `n` is represented as `m + 1`.  The product of the factors is
represented by an object `X : Over S` together with its limiting cone `hprod`; the
coordinate morphism is the morphism classified by the line bundle and its generating
coordinate sections in `symmetricProduct_properties`.
-/

universe v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The symmetric-product morphism is surjective.

Source: Weil conjectures blueprint, `lem-weil-pbc-symmetric-product-surjective`, order 1202;
Stacks Project, Etale Cohomology, proof of Lemma 0A4F.
(blueprint: lem-weil-pbc-symmetric-product-surjective)

Proof:
1. For a target point p, take an algebraic closure K of its residue field. The canonical
   residue-field point followed by Spec K gives a geometric point ξ over p
   (def-weil-residue-field, def-weil-algebraic-closure, def-weil-geometric-point).
   Its two components are g : Spec K → S and ψ into integral projective space
   (def-nagata-projective-space-base-change, def-pc-fibre-product).
2. The projective-space functor of points (lem-weil-pbc-projective-space-functor-of-points,
   Stacks 01NE) represents ψ by an invertible module and generating sections. Trivialize
   that module on the one-point scheme Spec K (def-sc-invertible-module), obtaining
   coordinates a_j in K, not all zero.
3. Factor the nonzero polynomial ∑ a_j t^j over K
   (lem-weil-alg-closed-linear-factorization). Absorb its nonzero leading coefficient
   into one factor and pad to m + 1 factors with (0,1), the factors at infinity.
   For a nonzero constant use (0,a_0) and then (0,1). Every pair is nonzero.
4. Each pair defines a morphism η_i : Spec K → P¹_S over g
   (def-weil-pbc-morphism-to-projective-space-by-sections). The product universal
   property (def-pc-fibre-product) gives η into X with these projections.
5. The composite of η and σ has first component g
   (lem-weil-pbc-symmetric-product-over-base). Pullback compatibility of the functor
   of points and of tensor products (lem-weil-pbc-invertible-pullback-tensor) identifies
   η*L_n with O and the pulled-back F_j with a_j by the coefficient formula
   (lem-weil-pbc-product-linear-forms-coefficients,
   lem-weil-pbc-symmetric-product-properties). Thus the second component is ψ.
   The fibre-product universal property gives η followed by σ equal to ξ.
6. The image under η of the unique point of Spec K therefore maps to p. Since p was
   arbitrary, σ is surjective (def-weil-surjective-morphism). -/
theorem symmetricProduct_surjective (S : Scheme.{v}) (m : ℕ)
    (X : Over S)
    (pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift.{v} (Fin 2); S) ↘ S)))
    (hprod : IsLimit (Fan.mk X pr)) :
    ∃ (hL : (symmetricProductLineBundle (fun i ↦ (pr i).left)).IsInvertible)
      (hs : Epi ((symmetricProductLineBundle (fun i ↦ (pr i).left)).freeHomEquiv.symm
        (symmetricProductCoordinateSection (fun i ↦ (pr i).left)))),
      Surjective (@ProjectiveSpace.homOfGeneratingSections.{v}
        (ULift.{v} (Fin (m + 2))) _ X.left S X.hom
        (symmetricProductLineBundle (fun i ↦ (pr i).left)) hL
        (symmetricProductCoordinateSection (fun i ↦ (pr i).left)) hs) := by
  sorry

end AlgebraicGeometry
