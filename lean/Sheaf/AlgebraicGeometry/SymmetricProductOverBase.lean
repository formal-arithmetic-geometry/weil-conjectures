/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricProductProperties
import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# The symmetric-product morphism is over the base

Source: Stacks Project, Etale Cohomology, proof of Tag 0A4F, last paragraph;
Constructions, paragraph following Definition 01NF
(blueprint: lem-weil-pbc-symmetric-product-over-base).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The morphism defined by the symmetric-product sections commutes with the structure
morphisms to S. The positive integer n is m + 1, and the product is expressed by its
universal cone in schemes over S, as in `symmetricProduct_properties`. The invertibility
and generation witnesses are selected from that theorem, so they are not extra hypotheses.

Source: Stacks Tag 0A4F, proof, last paragraph; paragraph following Definition 01NF
(blueprint: lem-weil-pbc-symmetric-product-over-base).

Proof:
1. `symmetricProduct_properties` constructs the line bundle and its generating coefficient
   sections. The morphism is `ProjectiveSpace.homOfGeneratingSections`, pairing the product
   projection with the integral morphism classified by these sections (01NE and 01NF).
2. The structure map of projective space is the first projection of its defining fibre
   product. The first projection of this pairing equals the original product projection
   by the fibre-product universal property, giving q_n composed with sigma_n equals p_n. -/
theorem symmetricProduct_over_base (S : Scheme.{v}) (m : ℕ)
    (X : Over S)
    (pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift.{v} (Fin 2); S) ↘ S)))
    (hprod : IsLimit (Fan.mk X pr)) :
    @ProjectiveSpace.homOfGeneratingSections.{v}
      (ULift.{v} (Fin (m + 2))) _ X.left S X.hom
      (symmetricProductLineBundle (fun i ↦ (pr i).left))
      (Classical.choose (symmetricProduct_properties S m X pr hprod).2.2.2)
      (symmetricProductCoordinateSection (fun i ↦ (pr i).left))
      (Classical.choose (Classical.choose_spec
        (symmetricProduct_properties S m X pr hprod).2.2.2)) ≫
      ℙ(ULift.{v} (Fin (m + 2)); S) ↘ S = X.hom := by
  sorry

end AlgebraicGeometry
