/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.CategoryTheory.Triangulated.Generators
import Sheaf.AlgebraicGeometry.SpacePerfectLocalizingGeneration
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactGeneratorAmbientThick

/-! # A perfect weak generator generates all perfect algebraic-space complexes

Source: Stacks Project, spaces-perfect.tex, Tag 0GFC, remark-classical-generator;
derived.tex, Tag 09SR (blueprint: lem-sfb-space-perfect-generator-thick).

The derived category is the recorded small affine model of the small etale ringed topos.
The conclusion uses the thick envelope in the ambient derived category. Quasi-separatedness
is absolute, expressed by quasi-compact fibre products of affine scheme charts.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A perfect weak generator of D_QCoh classically generates every perfect complex.
Source: Stacks Project, Tag 0GFC, remark-classical-generator, and Tag 09SR
(blueprint: lem-sfb-space-perfect-generator-thick).

Proof in words:
1. By lem-sfb-space-perfect-localizing-generation, D_QCoh is strictly full and closed
   under shifts, cones, retracts and ambient small coproducts. The empty coproduct
   supplies zero. Fullness restricts the ambient coproduct universal properties to it.
2. By lem-sfb-space-perfect-objects-compact, both G and P have quasi-coherent cohomology
   and are compact internally in D_QCoh. Ambient compactness is not needed.
3. The shift equivalences identify Hom(G,F[n]) with Hom(G[-n],F). Thus the hypothesis
   is the weak-generator condition of def-pc-generators. Apply
   lem-pc-compact-generators-build-objects to the singleton G and P in D_QCoh. It gives
   a tower Y_1 -> Y_2 -> ... with Y_1 and all attaching objects coproducts of shifts of G,
   and a distinguished telescope triangle with third object P. Its coproducts and
   triangles are the ambient ones by step 1.
4. Put X_0 = 0 and X_n = Y_n for positive n. The first triangle is the split triangle
   0 -> Y_1 -> Y_1 -> 0; rotate the attaching triangles to X_n -> X_(n+1) -> B_n.
   The B_n are again coproducts of shifts of G, since shifting is an autoequivalence.
   Adding the zero summand identifies the normalized telescope with the old one,
   including its shift operator, whose extra initial transition has zero source.
5. Apply lem-sc-compact-generator-ambient-thick to the ambient derived category,
   its full D_QCoh subcategory, the compact objects G and P, and this normalized tower.
   It puts P in the ambient thick envelope of G, exactly as asserted. -/
theorem perfect_mem_thick_of_weak_generator
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (G : X.DerivedQCoh)
    (hG : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, 0, w}
      X.smallStructureSheaf G.obj)
    (hgen : ∀ F : X.DerivedQCoh,
      (∀ n : ℤ, Subsingleton (G.obj⟦n⟧ ⟶ F.obj)) → IsZero F.obj)
    (P : X.DerivedModules)
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, 0, w}
      X.smallStructureSheaf P) :
    (ObjectProperty.singleton G.obj).triangEnvelope P := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
