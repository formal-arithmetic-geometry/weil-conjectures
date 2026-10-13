/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # The unit equation for the mate of pullback composition

Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-mate-unit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

set_option maxHeartbeats 800000 in
-- Matching the composition expands the sheaf and derived-functor instances.
/-- The conjugate of the fixed pullback comparison satisfies the pasted direct-image
unit equation, before identifying it with any direct-image composition isomorphism.
Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-mate-unit).

Proof: write ε for the counits selected by exists_derivedPullbackComposition and β
for the right-derived units. Its comparison p satisfies the left-derived lift
factorization equation: ε(fg) after p is the composite of ε(g), ε(f), and the
underived tensor-pullback composition comparison. Transpose this equation under
the pinned adjunctions schemeHomPullbackAdjunction. The Hom-equivalence equation
in exists_schemeDerivedAdjunction identifies each transposed ε with the localized
underived adjunct followed by β. For the composite adjunction apply that equation
first for f and then for g; naturality moves the first β through the second adjunct.
The underived tensor comparison was defined as the inverse conjugate of
pushforwardComp, so its transpose is the sectionwise identity identifying
(fg)_* with g_* f_*. Thus the two transposes are exactly β(fg) followed by the
mate of p and β(g) followed by Rg_*(β(f)). To test the equation, precompose with maps from
localized K-flat complexes: the left-derived counits are invertible on these complexes, and
successive pullback preserves K-flatness. For a map represented by a localization roof, replace
its intermediate complex by a K-flat resolution. Naturality and inversion of the localized quasi-
isomorphism extend the same calculation from localized homotopy maps to that roof. Thus the Hom-
equivalence calculation applies to every map from a K-flat representative. Every derived object
has such a representative, so Yoneda gives the claimed component equation for every homotopy
complex K. This argument requires no exactness of tensor pullback and no preservation of
K-injectives by direct image. Identity morphisms, zero complexes, and empty schemes satisfy the
same equations without additional hypotheses. -/
theorem derivedPullbackComposition_mate_unit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let p : ∀ {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C),
        derivedPullback t ⋙ derivedPullback s ≅ derivedPullback (s ≫ t) :=
      @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
        (conjugateEquiv (schemeHomPullbackAdjunction.{u, w} (f ≫ g))
          ((schemeHomPullbackAdjunction.{u, w} g).comp (schemeHomPullbackAdjunction.{u, w} f))
          (p f g).hom).app (DerivedCategory.Qh.obj K) =
      (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (schemeDerivedDirectImage g).map
          ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K)
    := by sorry

end AlgebraicGeometry
