/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck

/-! # The Grothendieck bottom edge on resolution comparisons

Source: Stacks Project, Tags 015M, 015N and 015J.
(blueprint: lem-sc-grothendieck-bottom-resolution-comparison)
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The bottom edge is computed by applying the second functor to a comparison
from a resolution of `F(X)` to `F(I)`.

Source: Stacks Project, Tags 015M, 015N and 015J, the degree-zero augmentation.
(blueprint: lem-sc-grothendieck-bottom-resolution-comparison)

Proof: Extend both complexes by zero to the bounded below homotopy category.
The augmentation of J identifies J with F(X) in the derived category. The supplied
comparison represents the canonical map F(X)[0] to RF(X): its degree-zero
augmentation identity identifies it with the derived unit. Indeed, after
precomposition with the quasi-isomorphism F(X)[0] to J, the maps agree as
complex maps; cancelling that isomorphism in the derived category proves
independence of the comparison. Under the truncation comparison for H^0(RF(X)), this is
exactly the map from the bottom interval into the full interval. Apply RG and
homology. The G unit on J is invertible since J has injective terms; the G unit
on F(I) is invertible by hFG. Naturality of that unit makes the resulting map
homology of G(phi). The canonical resolution computations identify its endpoints
with R^n G(F(X)) and R^n(GF)(X). Their order is the displayed hom/inv order.
This works also for n=0, with no incoming differential and no shift sign.
-/
theorem grothendieckBottomEdgeMap_eq_resolution
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) (I : InjectiveResolution X)
    (J : InjectiveResolution (F.obj X))
    (φ : J.cocomplex ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = F.map (I.ι.f 0)) (n : ℕ) :
    (F.grothendieckBottomEdgeMap G hFG n).app X =
      (J.isoRightDerivedObj G n).hom ≫
        HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
        (I.isoRightDerivedObj (F ⋙ G) n).inv := by sorry

end CategoryTheory
