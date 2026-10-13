/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.RestrictedOverSingleData

/-! # Triangle composition of restricted fixed-coefficient single complexes

Source: Stacks Project, Tags 09Z1 and 0EZM, restriction of fixed coefficients.
(blueprint: lem-sbc-restricted-over-single-composition).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Composition law for a triangle of fixed-coefficient restricted single complexes.
Source: Stacks Project, Tags 09Z1 and 0EZM, canonical fixed-coefficient comparisons.
(blueprint: lem-sbc-restricted-over-single-composition).

Proof: Substitute ha to replace the third arrow by g followed by f. Expand the
three explicit transition homs. The second pullback projections satisfy the
commuting triangles with f.left, g.left, and their composite. Apply the associativity
law of upperStarComp to these triangles and to the structure arrows to W. Naturality
moves each sheaf comparison across inverse image, and the inverse comparisons
cancel. Thus the composite of the two coefficient maps is the coefficient map
for the composite, preceded by upperStarComp for the restricted maps. Applying
the single functor and naturality of mapCochainComplexSingleFunctor gives the stated
complex identity. Its composition compatibility is checked in degree zero, where
it is the original functor composition identity; in other degrees the source is
zero. Transport along hq identifies the composite restricted map with that for a.
No cone, limiting property, or category structure on an indexing type is required;
zero sheaves, empty schemes and identity arrows satisfy the same calculation. -/
theorem restrictedOverSingle_composition {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A B C : Over W} (f : B ⟶ A) (g : C ⟶ B) (a : C ⟶ A)
    (ha : a = g ≫ f) (U : S.Etale)
    (hq : rawAffineRestrictedMap a.left (A.hom ≫ k) (C.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U =
      rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U ≫
      rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U) :
    (restrictedOverSingleIso k F a U).hom =
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1}
          (rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U)
          (rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U)
          (rawAffineRestrictedMap a.left (A.hom ≫ k) (C.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U) hq)
        (ComplexShape.up ℤ)).hom.app (restrictedOverSingle k F A U) ≫
      ((upperStar AddCommGrpCat.{u + 1}
        (rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (restrictedOverSingleIso k F f U).hom ≫
      (restrictedOverSingleIso k F g U).hom := by sorry

end AlgebraicGeometry.Etale
