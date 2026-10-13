/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # The union comparison as a morphism of distinguished triangles

Source: Stacks Project, Tags 0DJ9, 08BV and 08FE.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

/-- The relative Mayer--Vietoris diagram for a relatively flat module has invertible
middle and overlap components. This supplies only the triangle diagram; it does
not assert invertibility of the union comparison or a factorization at a chosen
flat complex.

Source: Stacks Project, Tag 0DJ9, induction diagram; Tags 08BV and 08FE.
(blueprint: new-pc-standard-single-flat-counit-union-triangles).

Proof:
1. Work on X = U union V and restrict N to the opens induced by U, V and
   U intersection V. Exact open restriction preserves quasi-coherence and
   relative flatness. The three presentation hypotheses give bounded-above flat
   representatives of the respective direct images. Their pinned pullback
   counits are invertible by bounded-flat K-flatness and uniqueness of the
   left-derived functor. The presentation equations therefore make the three
   canonical single-module comparisons invertible.
2. On X and on its base change choose K-injective resolutions with injective
   terms of N[0] and its ordinary pullback in degree zero. Apply
   schemeKInjective_mayerVietoris_presentation to the induced two-open covers.
   Its short exact complexes give distinguished triangles via triangleOfSES.
   Apply derived direct image, and also derived pullback on the source side,
   and transport the open terms using the canonical composition isomorphisms.
   These functors are triangulated and additive, so the middle terms are the
   biproducts of the direct images on U and V. No compactness of the opens or
   quasi-coherence of their direct images is required.
3. Transpose the ordinary single-module pullback map under the derived
   pullback/direct-image adjunction. Naturality of the sectionwise restriction
   units gives the first square, and the difference of the two restriction
   squares gives the second. For the connecting square use the degreewise
   identity schemeMVUnderivedOpenCounit_square and naturality of the boundary
   of the short exact cover complexes. Transposition back commutes with shift.
   Pasting the adjunction counits identifies the first component with
   standardSingleBaseChangeMap and the open components with the three maps
   in step 1. The biproduct of the U and V isomorphisms is invertible, as is
   the overlap component. Package the two distinguished triangles, their
   explicit differentials and this triangle morphism.
Empty opens, identical opens and the zero module obey the same construction:
the empty-open terms vanish, while the restriction-difference sequence remains
short exact. No witness here defines a new object of the library. -/
theorem standardSingleFlatCounitUnionTriangles
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver ((U ⊔ V).ι ≫ p))
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let a := Arrow.mk (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g)
    let aU := Arrow.mk (standardSingleBaseChangeMap (U.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_left) N) g)
    let aV := Arrow.mk (standardSingleBaseChangeMap (V.ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE le_sup_right) N) g)
    let aUV := Arrow.mk (standardSingleBaseChangeMap ((U ⊓ V).ι ≫ p)
      (Scheme.Modules.tensorPullbackObj (Y.homOfLE (inf_le_left.trans le_sup_left)) N) g)
    ∃ (d₁ : a.left ⟶ aU.left ⊞ aV.left)
      (d₂ : aU.left ⊞ aV.left ⟶ aUV.left)
      (d₃ : aUV.left ⟶ a.left⟦(1 : ℤ)⟧)
      (d₁' : a.right ⟶ aU.right ⊞ aV.right)
      (d₂' : aU.right ⊞ aV.right ⟶ aUV.right)
      (d₃' : aUV.right ⟶ a.right⟦(1 : ℤ)⟧),
      Triangle.mk d₁ d₂ d₃ ∈ distTriang (schemeDerivedCategory A) ∧
      Triangle.mk d₁' d₂' d₃' ∈ distTriang (schemeDerivedCategory A) ∧
      ∃ φ : Triangle.mk d₁ d₂ d₃ ⟶ Triangle.mk d₁' d₂' d₃',
        φ.hom₁ = a.hom ∧ φ.hom₂ = biprod.map aU.hom aV.hom ∧ φ.hom₃ = aUV.hom ∧
        IsIso aU.hom ∧ IsIso aV.hom ∧ IsIso aUV.hom := by sorry

end AlgebraicGeometry
