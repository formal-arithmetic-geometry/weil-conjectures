/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricProductProperties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Sheaf.AlgebraicGeometry.SymmetricProductFinite
import Sheaf.AlgebraicGeometry.SymmetricProductSurjective

/-!
# A finite symmetric-product cover over a Noetherian base

Source: Weil conjectures blueprint, sec-smooth-purity, sk-prop-sf-cbc, order 1597;
Stacks Project, Etale Cohomology, proof of Tag 0A4F, final paragraph
(blueprint: lem-fin-symmetric-product-finite).

The positive integer n is m + 1. The universal cone in schemes over S represents
its fibre power. The invertibility and generation proofs are supplied by
`symmetricProduct_properties`; they impose no additional hypotheses.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The coefficient morphism from n projective lines to projective n-space is finite
and surjective over a Noetherian base.

Source: blueprint lem-fin-symmetric-product-finite, order 1597; Stacks Tag 0A4F,
proof, final paragraph (blueprint: lem-fin-symmetric-product-finite).

Proof:
1. Apply `symmetricProduct_finite` (lem-weil-pbc-symmetric-product-finite) to S
   and n = m + 1, with the product cone and the invertibility and generation proofs
   from `symmetricProduct_properties`. Its first conclusion is finiteness of exactly
   the morphism classified by the coefficient sections of product_i (x_i t + y_i).
   The general lemma requires no Noetherian hypothesis.
2. Apply `symmetricProduct_surjective` (lem-weil-pbc-symmetric-product-surjective)
   to the same product. Its coordinate morphism uses the same line bundle and sections.
   The selected invertibility and generation witnesses are proofs of propositions,
   hence proof irrelevance identifies the morphisms. Its conclusion gives surjectivity
   on underlying topological spaces. Combine the two assertions. -/
theorem symmetricProduct_finite_surjective_of_isNoetherian
    (S : Scheme.{u}) [IsNoetherian S] (m : ℕ)
    (X : Over S)
    (pr : Fin (m + 1) → (X ⟶ Over.mk (ℙ(ULift.{u} (Fin 2); S) ↘ S)))
    (hprod : IsLimit (Fan.mk X pr)) :
    IsFinite (@ProjectiveSpace.homOfGeneratingSections.{u}
      (ULift.{u} (Fin (m + 2))) _ X.left S X.hom
      (symmetricProductLineBundle (fun i ↦ (pr i).left))
      (Classical.choose (symmetricProduct_properties S m X pr hprod).2.2.2)
      (symmetricProductCoordinateSection (fun i ↦ (pr i).left))
      (Classical.choose (Classical.choose_spec
        (symmetricProduct_properties S m X pr hprod).2.2.2))) ∧
    Surjective (@ProjectiveSpace.homOfGeneratingSections.{u}
      (ULift.{u} (Fin (m + 2))) _ X.left S X.hom
      (symmetricProductLineBundle (fun i ↦ (pr i).left))
      (Classical.choose (symmetricProduct_properties S m X pr hprod).2.2.2)
      (symmetricProductCoordinateSection (fun i ↦ (pr i).left))
      (Classical.choose (Classical.choose_spec
        (symmetricProduct_properties S m X pr hprod).2.2.2))) := by
  sorry

end AlgebraicGeometry
