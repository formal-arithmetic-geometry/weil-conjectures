/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClassicalDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteClassicalUnboundedComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.Compactification.CategoryBaseChange
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing

/-!
# Affine space and étale localization

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/
sec-the-exceptional-inverse-image-of-a-smooth-morphism-and-base-change/
sk-lem-geo-affine-local/_section.md, clauses (1)--(2), equation (7.10);
Stacks Tags 0F7J, 0F7K, 0F7L and 03S2
(blueprint: sk-lem-geo-affine-local).

All adjunctions below live in the finite-classical full subcategories.  The affine-space
right adjoint is the native pullback--Tate-twist--shift formula.  For a general separated
finite-type map the right adjoint is recorded only by the counit-normalized uniqueness
property supplied by `sk-prop-sf-existence`; no affine formula is imposed on it.  Pullback
and base-change functors are constrained by their native ambient formulas, and comparison
isos are constrained by the actual unit and counit equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory Limits
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- The accepted classical full subcategory. Source: unit opening setting
(blueprint: sk-lem-geo-affine-local). -/
abbrev ClassicalD (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  classicalDerivedCategory T A

/-- The ordinary finite-coefficient presentation of the ambient pro-étale derived category.
Source: unit opening setting (blueprint: sk-lem-geo-affine-local). -/
abbrev ProEtaleD (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The ordinary étale presentation used by the finite classical comparison.
Source: finite classical comparison, opening paragraph of the unit proof
(blueprint: sk-lem-geo-affine-local). -/
abbrev EtaleD (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The comparison equivalence has exactly the existing inverse-image functor after inclusion.
Source: finite classical comparison, opening paragraph of the unit proof
(blueprint: sk-lem-geo-affine-local). -/
structure ClassicalComparisonData (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] where
  equivalence : EtaleD T A ≌ ClassicalD T A
  native : equivalence.functor ⋙ (ObjectProperty.ι (IsClassicalComplexFor T A)) =
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- The comparison for a functor defined by conjugation through finite classical equivalences.
Its map is the unit isomorphism of the specified comparison equivalence, so no free comparison
map is chosen. Source: opening comparison paragraph (blueprint: sk-lem-geo-affine-local). -/
def classicalTransportModel
    {P S : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    (CP : ClassicalComparisonData P A) (CS : ClassicalComparisonData S A)
    (F : EtaleD P A ⥤ EtaleD S A) (L : ClassicalD P A ⥤ ClassicalD S A)
    (h : L = CP.equivalence.inverse ⋙ F ⋙ CS.equivalence.functor) :
    CP.equivalence.functor ⋙ L ≅ F ⋙ CS.equivalence.functor :=
  eqToIso (congrArg (fun J ↦ CP.equivalence.functor ⋙ J) h) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight CP.equivalence.unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- The ordinary presentation of the affine purity right functor.
Source: unit clause (1) (blueprint: sk-lem-geo-affine-local). -/
def etaleAffineRight (P S : Scheme.{u}) (f : P ⟶ S)
    (A : Type (u + 1)) [CommRing A] (ell r d : ℕ)
    (hEll : ((ell ^ r : ℕ) : A) = 0) : EtaleD S A ⥤ EtaleD P A :=
  (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ⋙
    Etale.derivedTensorRight (ModuleCat.{u + 1} A) P
      ((DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist P (ell ^ r) A hEll d)) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- The specified pullback--twist--shift comparison on the cartesian square.
It uses the existing upper-star compositor, normalized Tate pullback, tensor comparison and
shift comparison. Source: clause (1), base-change sentence
(blueprint: sk-lem-geo-affine-local). -/
def etaleAffineRightBaseChange
    (A : Type (u + 1)) [CommRing A] (ell r d : ℕ)
    (hpos : 0 < ell ^ r) (hEll : ((ell ^ r : ℕ) : A) = 0)
    {P P' S S' : Scheme.{u}} {f : P ⟶ S} {f' : P' ⟶ S'}
    {bP : P' ⟶ P} {bS : S' ⟶ S} (sq : IsPullback bP f' f bS)
    (hP : IsUnit (((ell ^ r : ℕ) : Γ(P, ⊤)))) :
    etaleAffineRight P S f A ell r d hEll ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) bP).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) bS).mapDerivedCategory ⋙
        etaleAffineRight P' S' f' A ell r d hEll :=
  let B := ModuleCat.{u + 1} A
  let E := fun (T : Scheme.{u}) (n : ℕ) ↦
    Scheme.finiteEtaleTateSheaf A (ell ^ r) T hEll (n : ℤ)
  let tp := Scheme.finiteEtaleTwistPullbackData A (ell ^ r) hpos hEll
  let tc := fun {T T' : Scheme.{u}} (g : T' ⟶ T)
      (hT : IsUnit (((ell ^ r : ℕ) : Γ(T, ⊤)))) (n : ℕ) ↦
    tp.c g hT (AlgebraicGeometry.affineTracePullbackInvertible (ell ^ r) g hT) n
  Functor.isoWhiskerLeft _ (Etale.leftDerivedUpperStarIsoMapDerivedCategory B bP).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Etale.tensorEPullback B (ell ^ r) E tc bP hP d (2 * (d : ℤ))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Etale.leftDerivedUpperStarComp B bP f (f' ≫ bS) sq.w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp B f' bS) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory B bS) _

/-- Tensor with the displayed finite Tate object on the right.
Source: clause (1) (blueprint: sk-lem-geo-affine-local). -/
noncomputable def derivedTensorRight
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M : ProEtaleD T A) : ProEtaleD T A ⥤ ProEtaleD T A :=
  (ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).flip.obj M

/-- The native pro-étale pullback, Tate twist and even shift.
Source: clause (1) (blueprint: sk-lem-geo-affine-local). -/
noncomputable def nativeAffineRight (P S : Scheme.{u}) (f : P ⟶ S)
    (A : Type (u + 1)) [CommRing A] (ell r d : ℕ)
    (hEll : ((ell ^ r : ℕ) : A) = 0) :
    ProEtaleD S A ⥤ ProEtaleD P A :=
  (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
    derivedTensorRight P A
      ((comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateTwist P (ell ^ r) A hEll d))) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- A classical upper-star functor together with its native ambient comparison.
(blueprint: sk-lem-geo-affine-local) -/
structure ClassicalUpperStarData (P S : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (g : P ⟶ S) where
  functor : ClassicalD S A ⥤ ClassicalD P A
  ambient : functor ⋙
      (CategoryTheory.ObjectProperty.ι (C := ProEtaleD P A)
        (IsClassicalComplexFor P A)) ≅
    (CategoryTheory.ObjectProperty.ι (C := ProEtaleD S A)
      (IsClassicalComplexFor S A)) ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory

/-- The affine-space adjunction.  Its right side is the explicit purity formula.
(blueprint: sk-lem-geo-affine-local) -/
structure ClassicalAffineAdjunctionData (P S : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] (f : P ⟶ S) (c : Compactification f) (ell r d : ℕ)
    (hEll : ((ell ^ r : ℕ) : A) = 0)
    (CP : ClassicalComparisonData P A) (CS : ClassicalComparisonData S A)
    (F : ProEtaleD P A ⥤ ProEtaleD S A) (G : ProEtaleD S A ⥤ ProEtaleD P A) where
  left : ClassicalD P A ⥤ ClassicalD S A
  right : ClassicalD S A ⥤ ClassicalD P A
  adjunction : left ⊣ right
  left_native : F = ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} A) c
  right_native : G = nativeAffineRight P S f A ell r d hEll
  left_eq : left = CP.equivalence.inverse ⋙
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
      CS.equivalence.functor
  left_etale : CP.equivalence.functor ⋙ left ≅
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
      CS.equivalence.functor
  left_etale_normalization : left_etale = classicalTransportModel CP CS _ left left_eq
  right_eq : right = CS.equivalence.inverse ⋙
    etaleAffineRight P S f A ell r d hEll ⋙ CP.equivalence.functor
  right_etale : CS.equivalence.functor ⋙ right ≅
    etaleAffineRight P S f A ell r d hEll ⋙ CP.equivalence.functor
  right_etale_normalization : right_etale = classicalTransportModel CS CP _ right right_eq
  left_formula : left ⋙
      (CategoryTheory.ObjectProperty.ι (C := ProEtaleD S A)
        (IsClassicalComplexFor S A)) ≅
    (CategoryTheory.ObjectProperty.ι (C := ProEtaleD P A)
      (IsClassicalComplexFor P A)) ⋙ F
  right_formula : right ⋙
      (CategoryTheory.ObjectProperty.ι (C := ProEtaleD P A)
        (IsClassicalComplexFor P A)) ≅
    (CategoryTheory.ObjectProperty.ι (C := ProEtaleD S A)
      (IsClassicalComplexFor S A)) ⋙ G

/-- The exceptional adjunction supplied by `sk-prop-sf-existence`.  The uniqueness field is
its counit-normalized right-adjoint characterization; in particular it imposes no affine
formula on the right adjoint. Source: clause (2), opening reference to existence
(blueprint: sk-lem-geo-affine-local). -/
structure ClassicalExceptionalAdjunctionData (P S : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] (f : P ⟶ S) (c : Compactification f)
    (CP : ClassicalComparisonData P A) (CS : ClassicalComparisonData S A)
    (F : ProEtaleD P A ⥤ ProEtaleD S A) where
  left : ClassicalD P A ⥤ ClassicalD S A
  right : ClassicalD S A ⥤ ClassicalD P A
  adjunction : left ⊣ right
  left_native : F = ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} A) c
  left_formula : left ⋙
      (CategoryTheory.ObjectProperty.ι (C := ProEtaleD S A)
        (IsClassicalComplexFor S A)) ≅
    (CategoryTheory.ObjectProperty.ι (C := ProEtaleD P A)
      (IsClassicalComplexFor P A)) ⋙ F
  left_eq : left = CP.equivalence.inverse ⋙
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
      CS.equivalence.functor
  left_etale : CP.equivalence.functor ⋙ left ≅
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
      CS.equivalence.functor
  left_etale_normalization : left_etale = classicalTransportModel CP CS _ left left_eq
  right_counit_normalized : ∀ (J : ClassicalD S A ⥤ ClassicalD P A)
    (adjJ : left ⊣ J), ∃! e : right ≅ J, ∀ N,
      left.map (e.hom.app N) ≫ adjJ.counit.app N = adjunction.counit.app N

/-- The étale sum extension with its compactification formula and native upper-star comparison.
Source: clause (2), the four-Hom calculation (blueprint: sk-lem-geo-affine-local). -/
structure ClassicalEtaleSumData (U X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (u : U ⟶ X) (c : Compactification u)
    (CU : ClassicalComparisonData U A) (CX : ClassicalComparisonData X A) where
  left : ClassicalD U A ⥤ ClassicalD X A
  right : ClassicalD X A ⥤ ClassicalD U A
  adjunction : left ⊣ right
  right_eq : right = CX.equivalence.inverse ⋙
    (Etale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ⋙ CU.equivalence.functor
  left_native : left ⋙
      (CategoryTheory.ObjectProperty.ι (C := ProEtaleD X A)
        (IsClassicalComplexFor X A)) ≅
    (CategoryTheory.ObjectProperty.ι (C := ProEtaleD U A)
      (IsClassicalComplexFor U A)) ⋙
      ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c
  right_native : right ⋙
      (CategoryTheory.ObjectProperty.ι (C := ProEtaleD U A)
        (IsClassicalComplexFor U A)) ≅
    (CategoryTheory.ObjectProperty.ι (C := ProEtaleD X A)
      (IsClassicalComplexFor X A)) ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory

/-- The exact derived pullback in the finite classical presentation. Source: clause (2)
(blueprint: sk-lem-geo-affine-local). -/
def ClassicalEtaleSumData.pullbackModel
    {U X : Scheme.{u}} {A : Type (u + 1)} [CommRing A] {u : U ⟶ X}
    {c : Compactification u} {CU : ClassicalComparisonData U A}
    {CX : ClassicalComparisonData X A}
    (sum : ClassicalEtaleSumData U X A u c CU CX)
    (h : sum.right = CX.equivalence.inverse ⋙
      (Etale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ⋙ CU.equivalence.functor) :=
  classicalTransportModel CX CU _ sum.right h

/-- Base-change comparison for two adjunctions.  The last two fields are the actual unit and
counit mate equations, rather than mere invertibility assertions.
(blueprint: sk-lem-geo-affine-local) -/
structure ClassicalAdjunctionComparison
    {C D C' D' : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Category.{u + 1} C'] [Category.{u + 1} D']
    (L : C ⥤ D) (R : D ⥤ C) (L' : C' ⥤ D') (R' : D' ⥤ C')
    (bC : C ⥤ C') (bD : D ⥤ D') (a : L ⊣ R) (a' : L' ⊣ R') where
  left_comparison : L ⋙ bD ≅ bC ⋙ L'
  right_comparison : R ⋙ bC ≅ bD ⋙ R'
  unit_base_change : ∀ X : C,
    bC.map (a.unit.app X) ≫ right_comparison.hom.app (L.obj X) ≫
        R'.map (left_comparison.hom.app X) = a'.unit.app (bC.obj X)
  counit_base_change : ∀ Y : D,
    bD.map (a.counit.app Y) = left_comparison.hom.app (R.obj Y) ≫
      L'.map (right_comparison.hom.app Y) ≫ a'.counit.app (bD.obj Y)

/-- The right comparison is the normalized mate of the supplied left compositor.
`ClassicalCanonicalComposite` below fixes that left compositor by an explicit construction.
Source: clause (2), the four-Hom calculation (blueprint: sk-lem-geo-affine-local). -/
structure ClassicalCompositeComparison
    {C E D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} E]
    [Category.{u + 1} D] (L : C ⥤ D) (R : D ⥤ C)
    (L' : E ⥤ D) (R' : D ⥤ E) (LP : E ⥤ C) (P : C ⥤ E)
    (a : L ⊣ R) (a' : L' ⊣ R') (ap : LP ⊣ P) where
  composite : LP ⋙ L ≅ L'
  comparison : R ⋙ P ≅ R'
  canonical : comparison = ((ap.comp a).ofNatIsoLeft composite).rightAdjointUniq a'
  unit_compatibility : ∀ K : E,
    ((ap.comp a).ofNatIsoLeft composite).unit.app K ≫
      comparison.hom.app (L'.obj K) = a'.unit.app K
  counit_compatibility : ∀ Y : D,
    L'.map (comparison.hom.app Y) ≫ a'.counit.app Y =
      ((ap.comp a).ofNatIsoLeft composite).counit.app Y

/-- Canonical base change on the classical categories.  The component equations fix both
maps by the actual compact-support exchange and the upper-star/Tate pullback identification.
Source: clause (1), base-change sentence (blueprint: sk-lem-geo-affine-local). -/
structure ClassicalAffineBaseChange
    (A : Type (u + 1)) [CommRing A] (ell r d : ℕ)
    (hpos : 0 < ell ^ r) (hEll : ((ell ^ r : ℕ) : A) = 0)
    {P P' S S' : Scheme.{u}} {f : P ⟶ S} {f' : P' ⟶ S'}
    {bP : P' ⟶ P} {bS : S' ⟶ S} (sq : IsPullback bP f' f bS)
    (c : Compactification f) (hP : IsUnit (((ell ^ r : ℕ) : Γ(P, ⊤))))
    (CP : ClassicalComparisonData P A) (CS : ClassicalComparisonData S A)
    (CP' : ClassicalComparisonData P' A) (CS' : ClassicalComparisonData S' A)
    (F : ProEtaleD P A ⥤ ProEtaleD S A) (G : ProEtaleD S A ⥤ ProEtaleD P A)
    (F' : ProEtaleD P' A ⥤ ProEtaleD S' A) (G' : ProEtaleD S' A ⥤ ProEtaleD P' A)
    (a : ClassicalAffineAdjunctionData P S A f c ell r d hEll CP CS F G)
    (a' : ClassicalAffineAdjunctionData P' S' A f' (c.ofIsPullback sq)
      ell r d hEll CP' CS' F' G')
    (bp : ClassicalUpperStarData P' P A bP) (bs : ClassicalUpperStarData S' S A bS) where
  pullP_eq : bp.functor = CP.equivalence.inverse ⋙
    (Etale.upperStar (ModuleCat.{u + 1} A) bP).mapDerivedCategory ⋙ CP'.equivalence.functor
  pullS_eq : bs.functor = CS.equivalence.inverse ⋙
    (Etale.upperStar (ModuleCat.{u + 1} A) bS).mapDerivedCategory ⋙ CS'.equivalence.functor
  pullP : CP.equivalence.functor ⋙ bp.functor ≅
    (Etale.upperStar (ModuleCat.{u + 1} A) bP).mapDerivedCategory ⋙ CP'.equivalence.functor
  pullS : CS.equivalence.functor ⋙ bs.functor ≅
    (Etale.upperStar (ModuleCat.{u + 1} A) bS).mapDerivedCategory ⋙ CS'.equivalence.functor
  pullP_normalization : pullP = classicalTransportModel CP CP' _ bp.functor pullP_eq
  pullS_normalization : pullS = classicalTransportModel CS CS' _ bs.functor pullS_eq
  comparison : ClassicalAdjunctionComparison a.left a.right a'.left a'.right
    bp.functor bs.functor a.adjunction a'.adjunction
  left_normalization : ∀ K : EtaleD P A,
    comparison.left_comparison.hom.app (CP.equivalence.functor.obj K) =
      bs.functor.map (a.left_etale.hom.app K) ≫
        pullS.hom.app
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ≫
        CS'.equivalence.functor.map
          ((Etale.unboundedEtaleCompactSupportExchange A sq c).app K) ≫
        a'.left_etale.inv.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) bP).mapDerivedCategory.obj K) ≫
        a'.left.map (pullP.inv.app K)
  right_normalization : ∀ K : EtaleD S A,
    comparison.right_comparison.hom.app (CS.equivalence.functor.obj K) =
      bp.functor.map (a.right_etale.hom.app K) ≫
        pullP.hom.app ((etaleAffineRight P S f A ell r d hEll).obj K) ≫
        CP'.equivalence.functor.map
          ((etaleAffineRightBaseChange A ell r d hpos hEll sq hP).hom.app K) ≫
        a'.right_etale.inv.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) bS).mapDerivedCategory.obj K) ≫
        a'.right.map (pullS.inv.app K)

/-- The canonical compact-support compositor for the three displayed compactifications.
Use the existing comparisons with chosen compactifications and the Tag 0F7J compositor.
Source: clause (2), the last Hom bijection (blueprint: sk-lem-geo-affine-local). -/
def classicalCompactSupportCompositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [QuasiCompact u] [QuasiCompact f]
    (cx : Compactification u) (c : Compactification f) (cu : Compactification (u ≫ f)) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cx ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cu :=
  letI := cx.hasCompactification
  letI := c.hasCompactification
  letI := cu.hasCompactification
  Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekIso A cx) _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.rightDerivedLowerShriekIso A c) ≪≫
    Etale.unboundedEtaleLowerShriekCompIso A u f ≪≫
    (Etale.rightDerivedLowerShriekIso A cu).symm

/-- A composite comparison normalized by the specified compact-support compositor,
the proper/open tower construction of Tag 0F7J with the coherent
compactification comparisons of `sk-prop-sf-comp-coherence`.
Source: clause (2), the four-Hom calculation (blueprint: sk-lem-geo-affine-local). -/
structure ClassicalCanonicalComposite
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [QuasiCompact u] [QuasiCompact f]
    (c : Compactification f) (cu : Compactification (u ≫ f))
    (cx : Compactification u)
    (CU : ClassicalComparisonData U A) (CX : ClassicalComparisonData X A)
    (CS : ClassicalComparisonData S A)
    (F : ProEtaleD X A ⥤ ProEtaleD S A) (FU : ProEtaleD U A ⥤ ProEtaleD S A)
    (a : ClassicalExceptionalAdjunctionData X S A f c CX CS F)
    (au : ClassicalExceptionalAdjunctionData U S A (u ≫ f) cu CU CS FU)
    (sum : ClassicalEtaleSumData U X A u cx CU CX) where
  sum_eq : sum.left = CU.equivalence.inverse ⋙
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cx ⋙
      CX.equivalence.functor
  sum_etale : CU.equivalence.functor ⋙ sum.left ≅
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cx ⋙
      CX.equivalence.functor
  sum_normalization : sum_etale = classicalTransportModel CU CX _ sum.left sum_eq
  sum_adjunction_normalization : sum.adjunction =
    let ordinaryAdj :=
      (Etale.derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u
        inferInstance).ofNatIsoLeft (Etale.canonicalEtaleCompactSupportComparison A u cx).symm
    ((((CU.equivalence.symm.toAdjunction.comp ordinaryAdj).comp
      CX.equivalence.toAdjunction).ofNatIsoLeft (eqToIso sum_eq.symm)).ofNatIsoRight
        (eqToIso sum.right_eq.symm))
  comparison : ClassicalCompositeComparison a.left a.right au.left au.right
    sum.left sum.right a.adjunction au.adjunction sum.adjunction
  compact_support_normalization : ∀ K : EtaleD U A,
    comparison.composite.hom.app (CU.equivalence.functor.obj K) =
      a.left.map (sum_etale.hom.app K) ≫
        a.left_etale.hom.app
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cx).obj K) ≫
        CS.equivalence.functor.map
          ((classicalCompactSupportCompositor A u f cx c cu).hom.app K) ≫
        au.left_etale.inv.app K

/-- Further localization compares the (7.10) isomorphisms, rather than asserting uniqueness
of an unconstrained pullback isomorphism. The pullback compositor is fixed on all comparison
inputs by the exact derived image of `upperStarComp`.
Source: clause (2), final sentence (blueprint: sk-lem-geo-affine-local). -/
structure ClassicalFurtherLocalization
    (A : Type (u + 1)) [CommRing A]
    {V U X S : Scheme.{u}} (v : V ⟶ U) (u : U ⟶ X)
    (R : ClassicalD S A ⥤ ClassicalD X A)
    (RU : ClassicalD S A ⥤ ClassicalD U A)
    (RV : ClassicalD S A ⥤ ClassicalD V A)
    (cU : Compactification u) (cV : Compactification v)
    (cVU : Compactification (v ≫ u))
    (CX : ClassicalComparisonData X A) (CU : ClassicalComparisonData U A)
    (CV : ClassicalComparisonData V A)
    (sumU : ClassicalEtaleSumData U X A u cU CU CX)
    (sumV : ClassicalEtaleSumData V U A v cV CV CU)
    (sumVU : ClassicalEtaleSumData V X A (v ≫ u) cVU CV CX)
    (thetaU : R ⋙ sumU.right ≅ RU)
    (thetaV : RU ⋙ sumV.right ≅ RV)
    (thetaVU : R ⋙ sumVU.right ≅ RV) where
  upper_star_compositor : sumU.right ⋙ sumV.right ≅ sumVU.right
  upper_star_normalization : ∀ K : EtaleD X A,
    upper_star_compositor.hom.app (CX.equivalence.functor.obj K) =
      sumV.right.map ((sumU.pullbackModel sumU.right_eq).hom.app K) ≫
        (sumV.pullbackModel sumV.right_eq).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj K) ≫
        CV.equivalence.functor.map
          ((Etale.unboundedEtaleUpperStarCompIso A v u).inv.app K) ≫
        (sumVU.pullbackModel sumVU.right_eq).inv.app K
  localization_equation :
    Functor.isoWhiskerRight thetaU sumV.right ≪≫ thetaV =
      Functor.associator R sumU.right sumV.right ≪≫
        Functor.isoWhiskerLeft R upper_star_compositor ≪≫ thetaVU

/-- Classical affine-space purity and exceptional localization.
(blueprint: sk-lem-geo-affine-local)

The second clause uses the existence-theorem exceptional adjoint and its counit normalization;
`right` is deliberately not specialized to the affine-space formula.  Pullback data carry the
native upper-star comparison, and all displayed comparison maps are fixed by adjunction
unit/counit equations or by the canonical upper-star compositor.

Proof source: the six steps of the current node and the two unit proof paragraphs.
1. Finite classical comparison identifies the full classical category with the ordinary
unbounded étale category and the finite localizing closure; transfer the existence adjoint.
2. Compactify the affine line in the projective line. Compose projective trace adjunction
with open-extension/restriction adjunction; its right side is pullback with twist (1)[2].
3. Start at d = 0 with the identity. Iterate the affine-line construction and use the
compact-support compositor, upper-star compositor, Tate multiplication and addition of shifts.
4. Trace base change and open-extension evaluation give the counit square. Composition
and mate pasting give all dimensions and the unit square. The two normalizations in
ClassicalAffineBaseChange specify exactly these exchange and pullback maps.
5. For étale u, termwise sum extension is left adjoint to restriction. The canonical support
compositor identifies the four Hom groups, giving (7.10) by normalized right-adjoint uniqueness.
6. Expand the pasted counits for f,u,v. The canonical support associator makes them equal.
Uniqueness gives the displayed localization equation modulo upperStarComp, including identity
localizations. Transport every construction and equation through the specified comparisons.
-/
theorem geoAffineLocal
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k ≠ ell)]
    (hbase : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))]
    [IsSeparated (S ↘ Spec (CommRingCat.of k))]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ ((ell ^ r : ℕ) : A) = 0) :
    ∃ (CS : ClassicalComparisonData S A) (r : ℕ),
      1 ≤ r ∧ ∃ (hAr : ((ell ^ r : ℕ) : A) = 0) (hpos : 0 < ell ^ r),
    ((∀ d : ℕ,
      let P := AffineSpace (ULift.{u} (Fin d)) S
      let f : P ⟶ S := P ↘ S
      ∃ (CP : ClassicalComparisonData P A) (c : Compactification f)
        (F : ProEtaleD P A ⥤ ProEtaleD S A) (G : ProEtaleD S A ⥤ ProEtaleD P A)
        (data : ClassicalAffineAdjunctionData P S A f c ell r d hAr CP CS F G),
      ∀ (S' : Scheme.{u}) (b : S' ⟶ S)
        [S'.Over (Spec (CommRingCat.of k))]
        [LocallyOfFiniteType (S' ↘ Spec (CommRingCat.of k))]
        [QuasiCompact (S' ↘ Spec (CommRingCat.of k))]
        [IsSeparated (S' ↘ Spec (CommRingCat.of k))]
        [b.IsOver (Spec (CommRingCat.of k))],
        let sq := IsPullback.of_hasPullback f b
        ∃ (CP' : ClassicalComparisonData (pullback f b) A)
          (CS' : ClassicalComparisonData S' A)
          (F' : ProEtaleD (pullback f b) A ⥤ ProEtaleD S' A)
          (G' : ProEtaleD S' A ⥤ ProEtaleD (pullback f b) A)
          (data' : ClassicalAffineAdjunctionData (pullback f b) S' A
            (pullback.snd f b) (c.ofIsPullback sq) ell r d hAr CP' CS' F' G')
          (bP : ClassicalUpperStarData (pullback f b) P A (pullback.fst f b))
          (bS : ClassicalUpperStarData S' S A b)
          (hP : IsUnit (((ell ^ r : ℕ) : Γ(P, ⊤)))),
          Nonempty (ClassicalAffineBaseChange A ell r d hpos hAr sq c hP
            CP CS CP' CS' F G F' G' data data' bP bS)) ∧
    (∀ (X U : Scheme.{u}) (f : X ⟶ S) (u : U ⟶ X)
        [X.Over (Spec (CommRingCat.of k))] [U.Over (Spec (CommRingCat.of k))]
        [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
        [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
        [IsSeparated (X ↘ Spec (CommRingCat.of k))]
        [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k))]
        [QuasiCompact (U ↘ Spec (CommRingCat.of k))]
        [IsSeparated (U ↘ Spec (CommRingCat.of k))]
        [f.IsOver (Spec (CommRingCat.of k))] [u.IsOver (Spec (CommRingCat.of k))]
        [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
        (c : Compactification f) (cu : Compactification (u ≫ f)),
      ∃ (CX : ClassicalComparisonData X A) (CU : ClassicalComparisonData U A)
        (F : ProEtaleD X A ⥤ ProEtaleD S A) (FU : ProEtaleD U A ⥤ ProEtaleD S A)
        (data : ClassicalExceptionalAdjunctionData X S A f c CX CS F)
        (dataU : ClassicalExceptionalAdjunctionData U S A (u ≫ f) cu CU CS FU)
        (cx : Compactification u) (sumU : ClassicalEtaleSumData U X A u cx CU CX)
        (thetaU : ClassicalCanonicalComposite A u f c cu cx CU CX CS F FU data dataU sumU),
      ∀ (V : Scheme.{u}) (v : V ⟶ U)
        [V.Over (Spec (CommRingCat.of k))]
        [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k))]
        [QuasiCompact (V ↘ Spec (CommRingCat.of k))]
        [IsSeparated (V ↘ Spec (CommRingCat.of k))]
        [v.IsOver (Spec (CommRingCat.of k))]
        [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
        (cv : Compactification (v ≫ u ≫ f)),
        let cv' := cv.copy (Category.assoc v u f)
        ∃ (CV : ClassicalComparisonData V A)
          (FV : ProEtaleD V A ⥤ ProEtaleD S A)
          (dataV : ClassicalExceptionalAdjunctionData V S A (v ≫ u ≫ f) cv CV CS FV)
          (dataVU : ClassicalExceptionalAdjunctionData V S A ((v ≫ u) ≫ f) cv' CV CS FV)
          (cV : Compactification v) (cVU : Compactification (v ≫ u))
          (sumV : ClassicalEtaleSumData V U A v cV CV CU)
          (sumVU : ClassicalEtaleSumData V X A (v ≫ u) cVU CV CX)
          (thetaV : ClassicalCanonicalComposite A v (u ≫ f) cu cv cV
            CV CU CS FU FV dataU dataV sumV)
          (thetaVU : ClassicalCanonicalComposite A (v ≫ u) f c cv' cVU
            CV CX CS F FV data dataVU sumVU)
          (assocLeft : dataV.left = dataVU.left)
          (assocRight : dataV.right ≅ dataVU.right),
          assocRight = (dataV.adjunction.ofNatIsoLeft (eqToIso assocLeft)).rightAdjointUniq
            dataVU.adjunction ∧
          Nonempty (ClassicalFurtherLocalization A v u data.right dataU.right dataVU.right
            cx cV cVU CX CU CV sumU sumV sumVU thetaU.comparison.comparison
            (thetaV.comparison.comparison ≪≫ assocRight) thetaVU.comparison.comparison))) := by
  sorry

end AlgebraicGeometry.ProEtale
