/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-! Transport of a fixed-scalar mate through the intrinsic realization equivalences. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

noncomputable def sfIntrinsicTransportRight
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁]
    [Category D₀] [Category D₁]
    (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {R : C₁ ⥤ C₀} {R' : D₁ ⥤ D₀}
    (b : (f.inverse ⋙ R ⋙ e.functor) ≅ R') :
    R' ⋙ e.inverse ≅ f.inverse ⋙ R :=
  Functor.isoWhiskerRight b.symm e.inverse ≪≫
    Functor.isoWhiskerLeft (f.inverse ⋙ R) e.unitIso.symm

noncomputable def sfIntrinsicAmbientCoordinate
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective]
    (k : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).leftDerivedFunctor) :
    (proEtaleConstantDerivedDirectImage g A).obj
        ((proEtaleConstantDerivedDirectImage f A).obj
          ((sfIntrinsicDerivedEquivalence X A).functor.obj (DerivedCategory.Q.obj I))) ⟶
      ((sfIntrinsicDerivedEquivalence Z A).functor.obj
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj I))) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let eZ := sfIntrinsicDerivedEquivalence Z A
  let eY := sfIntrinsicDerivedEquivalence Y A
  let eX := sfIntrinsicDerivedEquivalence X A
  let ag0 := derivedUpperStarLowerStarAdjunction B g
  let af0 := derivedUpperStarLowerStarAdjunction B f
  let at0 := derivedUpperStarLowerStarAdjunction B (f ≫ g)
  let bg : (eY.inverse ⋙ (lowerStar B g).rightDerivedFunctor ⋙ eZ.functor) ≅
      proEtaleConstantDerivedDirectImage g A :=
    Functor.isoWhiskerLeft eY.inverse
      (sfIntrinsicDerivedDirectImageComparison g A).symm ≪≫
      Functor.isoWhiskerRight eY.counitIso _
  let bf : (eX.inverse ⋙ (lowerStar B f).rightDerivedFunctor ⋙ eY.functor) ≅
      proEtaleConstantDerivedDirectImage f A :=
    Functor.isoWhiskerLeft eX.inverse
      (sfIntrinsicDerivedDirectImageComparison f A).symm ≪≫
      Functor.isoWhiskerRight eX.counitIso _
  let N := eX.functor.obj (DerivedCategory.Q.obj I)
  let q := (sfIntrinsicTransportRight eZ eY bg).hom.app
      ((proEtaleConstantDerivedDirectImage f A).obj N) ≫
    (lowerStar B g).rightDerivedFunctor.map
      ((sfIntrinsicTransportRight eY eX bf).hom.app N) ≫
    ((conjugateEquiv (ag0.comp af0) at0 k.hom).app (eX.inverse.obj N)) ≫
    (lowerStar B (f ≫ g)).rightDerivedFunctor.map
      (eX.unitIso.inv.app (DerivedCategory.Q.obj I))
  simpa only [Functor.comp_obj, Functor.id_obj, eX, N] using
    (eZ.counitIso.inv.app
      ((proEtaleConstantDerivedDirectImage g A).obj
        ((proEtaleConstantDerivedDirectImage f A).obj N)) ≫ eZ.functor.map q)

/-
The direct-image comparison transport identity.  It is the comparison component of the
mate-pasting calculation, before the fixed-scalar conjugate is specialized.  The parameter
`k` makes this strictly more general than the paper's single compositor instance.

Source: Stacks Tags 03D1 and 0D6E; the proof is the naturality and unit-counit cancellation
in the transported comparison square.
(blueprint: lem-sf-intrinsic-direct-comparison-transport).
-/
theorem sfIntrinsicDirectComparisonTransport
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective]
    (k : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).leftDerivedFunctor ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).leftDerivedFunctor) :
    (proEtaleConstantDerivedDirectImage g A).map
        ((sfIntrinsicDerivedDirectImageComparison f A).hom.app (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedDirectImageComparison g A).hom.app
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj
          (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedEquivalence Z A).functor.map
        ((conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).comp
            (derivedUpperStarLowerStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f))
          (derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g)) k).hom.app
          (DerivedCategory.Q.obj I)) =
      sfIntrinsicAmbientCoordinate A f g I k := by
  sorry

end AlgebraicGeometry.Scheme
