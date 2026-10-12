/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.CategoryTheory.CechResolutionDoubleComplex
public import Mathlib.Algebra.Homology.Functor

/-!
# Homology and the Čech complex of a complex of presheaves

Source: blueprint sk-thm-picard-cech, Step 2, product cohomology calculation.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

/-- Taking vertical homology of the Čech bicomplex commutes with the Čech construction.

Source: blueprint sk-thm-picard-cech, Step 2.
Proof: in Čech degree p, evaluate K on each product indexed by a tuple of p+1
covering indices. The resulting vertical complex is the product of those evaluation
complexes. The kernel of a product of homomorphisms is the product of the kernels.
The image is the product of the images: choose a preimage for each component.
The quotient of the product of kernels by the product of images is therefore the
product of the individual homology groups. These canonical identifications commute
with projections and with restriction maps, since the maps on homology are induced
by the same maps on cycles. In particular they commute with each Čech coface and
its alternating sum. Assemble them and their inverses into an isomorphism of
complexes. The empty indexing family gives zero products, and the same argument
applies in degree zero, where the incoming differential is zero.
(blueprint: lem-sc-cech-complex-homology) -/
theorem cechComplexFunctor_homology
    {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {ι : Type v} (U : ι → C) (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ)
    (q : ℕ) :
    Nonempty
      (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (HomologicalComplex₂.flip
            (((cechComplexFunctor U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≅
      (cechComplexFunctor U).obj
        (K.asFunctor ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) q)) := by
  sorry

end CategoryTheory
