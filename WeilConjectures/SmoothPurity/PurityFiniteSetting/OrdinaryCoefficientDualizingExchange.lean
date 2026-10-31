/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.DualizingCartesianApexIsomorphism
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange

/-! # Cartesian dualizing exchange at the degree-zero coefficient unit

Source: orientation-charts proof Steps 2--4. Conjugate the monoidal-unit
exchange and apex comparison by the fixed coefficient-unit isomorphisms.
(blueprint: new-def-pur-ordinary-coefficient-dualizing-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The actual Cartesian exchange, expressed at the degree-zero coefficient unit.
Source: the dualizing base-change definition and the fixed unit change.
(blueprint: new-def-pur-ordinary-coefficient-dualizing-exchange). -/
def ordinaryCoefficientDualizingExchange (P : PurityFiniteSetting.{u})
    {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {i : T ⟶ Y} {j : Z ⟶ X} {r : Z ⟶ T}
    [HasCompactification f] [HasCompactification r] [QuasiCompact r]
    (q : IsPullback j r f i) :
    (Etale.ordinaryFinitePullback P.Coefficient j).obj
        (P.diagonalOrdinaryDualizing f) ⟶ P.diagonalOrdinaryDualizing r :=
  (Etale.ordinaryFinitePullback P.Coefficient j).map
      (OrientationCounit.unitChange P f).inv ≫
    Etale.dualizingComplexBaseChangeMap P.Coefficient q ≫
    (OrientationCounit.unitChange P r).hom

/-- The same coefficient-unit conjugation of the specified Cartesian-apex mate.
Source: Cartesian-apex isomorphism, unit clause.
(blueprint: new-def-pur-ordinary-coefficient-dualizing-exchange). -/
def ordinaryCoefficientApexComparison (P : PurityFiniteSetting.{u})
    {Z X T : Scheme.{u}} (e : Z ≅ X) (r : X ⟶ T)
    [HasCompactification r] [HasCompactification (e.hom ≫ r)]
    [QuasiCompact (e.hom ≫ r)] :
    (Etale.ordinaryFinitePullback P.Coefficient e.hom).obj
        (P.diagonalOrdinaryDualizing r) ⟶ P.diagonalOrdinaryDualizing (e.hom ≫ r) :=
  (Etale.ordinaryFinitePullback P.Coefficient e.hom).map
      (OrientationCounit.unitChange P r).inv ≫
    (Etale.cartesianApexExceptionalComparison P.Coefficient e r).app
      (𝟙_ (Etale.DerivedCategoryModule P.Coefficient T)) ≫
    (OrientationCounit.unitChange P (e.hom ≫ r)).hom

/-- Exchange over an open immersion is invertible, also in coefficient-unit coordinates.
Source: open exceptional base change.
Proof: open exceptional base change is invertible; its component and the unit
comparison are invertible. Conjugating by unit isomorphisms preserves this property.
(blueprint: new-def-pur-ordinary-coefficient-dualizing-exchange). -/
theorem ordinaryCoefficientDualizingExchange_isIso (P : PurityFiniteSetting.{u})
    {X Y Z T : Scheme.{u}} {f : X ⟶ Y} {i : T ⟶ Y} {j : Z ⟶ X} {r : Z ⟶ T}
    [HasCompactification f] [HasCompactification r] [QuasiCompact r]
    [QuasiCompact f] [IsOpenImmersion i] (q : IsPullback j r f i) :
    IsIso (P.ordinaryCoefficientDualizingExchange q) := by
  letI := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion
    (Λ := P.Coefficient) q
  unfold ordinaryCoefficientDualizingExchange Etale.dualizingComplexBaseChangeMap
  infer_instance

end WeilConjectures.PurityFiniteSetting
