/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.Paper.ComponentDerivedSquareData

/-! # Coefficient-normalized abelian component square

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

/-- The coordinate-normalized square of abelian inverse images and coefficients.
Source: HRS (4.1) (blueprint: lem-zl-component-ordinary-abelian-square). -/
structure NormalizedAbelianSquare (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (sX : Corner Λ X) (sY : Corner Λ Y) (sh : Slice Λ (affineComponentMap f)) where
  tests : CondensedRing.componentTests X ⋙ Scheme.proEtaleBaseChange f ≅
    Over.pullback (affineComponentMap f) ⋙ CondensedRing.componentTests Y
  tests_eq : ∀ E : Over (affineComponentSpace X),
    (tests.hom.app E).left = ((component_lift_base_change.choose f).hom.app E).left
  abelian : sX.inverse ⋙ upperStar Ab.{u + 1} f ≅ sh.inverse ⋙ sY.inverse
  [monoidal : NatTrans.IsMonoidal abelian.hom]
  abelian_mate : ∀ (G : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (E : Over (affineComponentSpace X)),
    (((conjugateIsoEquiv
      (sh.adjunction.comp sY.adjunction)
      (sX.adjunction.comp (upperStarLowerStarAdjunction Ab.{u + 1} f))
      abelian).hom.app G).hom.app (op E)) = G.obj.map (tests.hom.app E).op
  coefficient :
    (upperStar Ab.{u + 1} f).map sX.coefficient.hom.hom ≫ condensedPullbackHom Λ.X f =
      abelian.hom.app (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X)) ≫
        sY.inverse.map sh.coefficient.hom.hom ≫ sY.coefficient.hom.hom

attribute [instance] NormalizedAbelianSquare.monoidal

/-- The normalized abelian component square, prior to scalar transport.

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9 and the naturality
used in Corollary 4.4(2)
(blueprint: lem-zl-component-ordinary-abelian-square).

Proof: lift the relative-test base-change isomorphism through the fully faithful
pro-étale forgetful functor; this fixes tests and tests_eq. Restriction of sheaves
along tests gives the right-adjoint isomorphism whose sections are G applied to
tests.hom.op. Take its adjunction mate for abelian. The canonical tensor and unit
equations on the given edges identify their monoidal adjunction structures, so
monoidality of pointwise restriction implies monoidality of abelian by monoidality
of conjugate comparisons. On absolute tests P × S and Q × S the base-change map
preserves both coordinates. Thus its pasting with the two absolute-test
identifications and the slice product identification is the structural scheme
pullback comparison. Equality follows on both projections by the universal
property of the relative component lift. Restricting and taking mates preserves
this equality. Evaluation at Λ, followed by Corner.coefficient_eq and
Slice.coefficient_eq, is exactly the coefficient equation displayed above.
This is only one square of abelian sheaves and asserts neither module transport
nor identity/composition coherence of the resulting squares. -/
theorem component_ordinary_abelian_square
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (sX : Corner Λ X) (sY : Corner Λ Y) (sh : Slice Λ (affineComponentMap f)) :
    Nonempty (NormalizedAbelianSquare Λ f sX sY sh) := by sorry

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
