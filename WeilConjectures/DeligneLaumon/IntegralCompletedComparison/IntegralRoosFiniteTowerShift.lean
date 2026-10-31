/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTower.FinitePullbackStrictTowerComparison
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Shift compatibility of a counit-normalized integral Roos comparison

Source: Stacks Project, sites-cohomology.tex, Tag 0941, and derived.tex, Tag 014E.
(blueprint: lem-a1-integral-roos-finite-tower-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
  WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
  WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.integralCompletedRingHasDerivedCategory
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

namespace WeilConjectures.IntegralCompletedComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- An already constructed natural comparison between integral pullback and the
finite derived tower followed by total limit respects shifts if its good-complex
values are normalized by the actual finite counit and the unit-normalized Roos map.
This statement supplies only shift compatibility, not the comparison or any of its
finite projection equations.

Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok,
shifted K-injective computation; derived.tex, Tag 014E, signed cone coordinates.
(blueprint: lem-a1-integral-roos-finite-tower-shift).

Proof: write the good-complex computation square for P and P[r]. By
finiteShift_descent the shifted finite counit is the localization of the retained
finite chain shift. Its normalization identifies each level with the standard
termwise shift. Thus its product comparison is productShift. The two equations in
hc identify the resulting Roos chain map: it is identity on the unshifted product
coordinate and multiplication by (-1)^r on the other coordinate. Compute the
unit-normalized Roos comparison on a K-injective replacement of the strict tower.
The ordinary limit inclusion has coordinates (0,z), so it commutes with this signed
shift. The canonical total right-derived-limit shift has the same unit square.
Cancel the invertible localized inclusion and resolution map to obtain the Roos
shift square for every strict tower. Substitute this square and finiteShift_descent
in the shifted good-complex computation square. The equation hd identifies the
remaining integral side with d. Cancel the finite computation isomorphism and its
shift, obtaining the CommShift square on Q(P) for every good P. The good resolving
localization is essentially surjective, so naturality transports that square to
every derived object. This proves NatTrans.CommShift, including all integer shifts;
the zero and addition coherence is already part of the given CommShift structures.
Zero complexes, r=0, negative shifts and arbitrary unbounded representatives require
no further hypothesis: the same two coordinate equalities and invertible counits
apply. -/
theorem integralRoosFiniteTower_commShift
    (C : FinitePullbackStrictTower.Comparison.{u, u} l E g)
    (e : roosF (A := integralTowerModules.{u, u} l E X) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙
        completedRlim X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X))
    (he : ∀ I : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules.{u, u} l E X) ℤ,
      DerivedCategory.Q.map (roosι I) ≫ e.hom.app I =
        DerivedCategory.Q.map
            ((limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩).hom) ≫
          (completedTowerLimit X
            (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)).rightDerivedFunctorUnitQ I)
    (b : integralDerivedPullback.{u, u} l E g ≅ C.B.functor ⋙
      completedRlim X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X))
    (hb : ∀ (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ)
      (hP : integralOperationsGoodComplex.{u, u} l E Y P),
      b.hom.app (DerivedCategory.Q.obj P) ≫
          (completedRlim X (completedIntegralCommRingSheafUnrestricted.{u, u} l E X)).map
            (C.B.counit.app P) =
        (integralDerivedPullbackComparison.{u, u} l E g).hom.app ⟨P, hP⟩ ≫
          e.hom.app ((FinitePullbackStrictTower.finiteComplex.{u, u} l E g).obj P))
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (hc : ShiftCoordinates l E g c)
    (d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ)
    (hd : ShiftDescent l E g c d) :
    letI := C.finiteShift
    letI := d
    NatTrans.CommShift b.hom ℤ := by sorry

end WeilConjectures.IntegralCompletedComparison
