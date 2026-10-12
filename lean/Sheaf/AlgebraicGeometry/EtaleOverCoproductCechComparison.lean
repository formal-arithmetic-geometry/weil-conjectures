/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Sheaf.AlgebraicGeometry.EtaleCoproductCechRestriction
import Sheaf.AlgebraicGeometry.EtaleFibreProductCoproduct
import Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison

/-! # Čech comparison for a finite coproduct over an étale object
Source: Stacks Project, Tag 03OZ, equation-sheaf-coprod.
(blueprint: new-etale-over-coproduct-cech-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- Replacing a finite family over an étale object by its coproduct preserves the Čech complex.
Source: Stacks Project, Tag 03OZ, equation-sheaf-coprod and its Čech-complex consequence.
(blueprint: new-etale-over-coproduct-cech-comparison)

Proof: restrict G to the slice over U and transport it through Etale.overSheafEquiv
to U.left.smallEtaleTopology. Etale.overEquiv preserves the chosen finite products
and their projections. Reindex the finite large type I by Fin n; this also reindexes
the tuples in each degree and commutes with deleting an index. Thus the terminal-base,
small-index disjoint-section comparison applies on U.left. The iterated fibre product of
W = coproduct V_i over U distributes as the coproduct over tuples of indices of the
corresponding fibre products of the V_i. This follows by induction on the number of
factors, since scheme base change preserves coproducts. The universal property identifies
these products with the chosen categorical products in Over U. The summands are disjoint
open subschemes and cover their coproduct. The sheaf axiom identifies sections on the
coproduct with the product of the sections on its summands: pairwise intersections of
distinct summands are empty, and sections on the empty scheme are zero. These restriction
isomorphisms commute with every omitted-factor projection, since the projection equations
characterize the distribution maps uniquely. They therefore commute with the alternating
sums defining the Čech differentials. Their inverses give an isomorphism of complexes.
For empty I, W is empty and all its nonempty powers over U are empty; the empty sheaf axiom
makes the singleton complex zero, as is the complex of the empty family. No affineness or
covering of U is required. A finite I in Type (u+1) can be reindexed by Fin n before applying
the small-index coproduct comparison of Tag 03OZ. -/
theorem nonempty_etale_over_coproduct_cech_iso
    (X : Scheme.{u}) (U : X.Etale) (I : Type (u + 1)) [Finite I]
    (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U)
    (W : X.Etale) (g : W ⟶ U) (c : ∀ i : I, V i ⟶ W)
    (hc : IsColimit (Cofan.mk W.left (fun i ↦ (c i).left)))
    (hw : ∀ i : I, c i ≫ g = f i)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty (((cechComplexFunctor fun i : I ↦ Over.mk (f i)).obj
      ((Over.forget U).op ⋙ G.obj)) ≅
      ((cechComplexFunctor fun _ : Fin 1 ↦ Over.mk g).obj
        ((Over.forget U).op ⋙ G.obj))) := by sorry

end AlgebraicGeometry.Scheme
