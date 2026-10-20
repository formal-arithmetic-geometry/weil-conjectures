/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.QbarCurveOrdinaryImage
public import Sheaf.Paper.QbarPerverseSubcategories
public import Sheaf.Paper.CommonStageLisse
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.ZlImmersionWeilLocalBehavior
public import Sheaf.Paper.IntegralPullbackComposition
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenFiniteComplement
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.DeligneLaumon.AffineLine.Perverse
import Sheaf.Paper.A1QbarOpenClosedCohomology
import Sheaf.Paper.BoundaryHomVanishing
import Sheaf.Paper.CommonStageCurveWeilMiddleExtension
import Sheaf.Paper.SfWeilSheafComplex

/-! # Ordinary and perverse intermediate extension on a smooth curve

Source: main-20261015, sec-deligne-laumon-a1/sk-d-dl-a1-setup,
rem-dl-a1-conventions, second paragraph
(blueprint: lem-dl-a1-curve-intermediate-extension).

All perverse subobjects and quotients below are geometric. Weil structures are fixed
pairs, and the last equation asserts equivariance of the geometric comparison. No
triangulated structure on a category of fixed pairs is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Endofunctor
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (c : AlgebraicGeometry.Scheme.MiddleExtensionCurve D)

/-- Separatedness of the geometric curve is inherited by base change.
Source: blueprint geometric-fibre hypotheses
(blueprint: lem-dl-a1-curve-intermediate-extension). -/
instance qbarCurveGeometricSeparated :
    IsSeparated ((D.geometricFiber c.C).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (IsSeparated (pullback.snd c.C.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The geometric perverse heart predicate is the intersection of support and cosupport.
Source: blueprint curve convention (blueprint: lem-dl-a1-curve-intermediate-extension). -/
abbrev qbarCurvePerverse :=
  QbarPerverseHeart l (D.geometricFiber c.C).left Ω D.k
    (finiteFieldDatumPrimeUnit D l hl)

/-- The shifted geometric sheaf on the open, in cohomological degree minus one.
Source: blueprint F[1] convention (blueprint: lem-dl-a1-curve-intermediate-extension). -/
def qbarCurveShiftedSource :=
  (sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω).ι ⋙ shiftFunctor _ (1 : ℤ)

/-- Forget only the Weil structure of the sheaf, retaining its actual common-stage carrier.
Source: blueprint Weil-pair convention (blueprint: lem-dl-a1-curve-intermediate-extension). -/
def qbarCurveWeilCarrier (F₀ : sfCommonStageWeilSheaf D l hl c.U Ω) :
    sfCommonStageHeart l (D.geometricFiber c.U).left Ω :=
  ⟨F₀.obj.carrier, F₀.property⟩

/-- Boundary minimality tests all geometric perverse monomorphisms and epimorphisms.
A boundary object is exactly one whose restriction to the open is zero.
Source: blueprint minimality sentence (blueprint: lem-dl-a1-curve-intermediate-extension). -/
def QbarCurveBoundaryMinimal
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber c.C).left)
    (hK : qbarCurvePerverse D l hl Ω c K) : Prop :=
  (∀ (Q : (qbarCurvePerverse D l hl Ω c).FullSubcategory)
    (f : Q ⟶ ⟨K, hK⟩), Mono f →
      IsZero ((qbarCurveDerivedRestriction D l hl Ω c).obj Q.obj) → IsZero Q.obj) ∧
  (∀ (Q : (qbarCurvePerverse D l hl Ω c).FullSubcategory)
    (f : (⟨K, hK⟩ : (qbarCurvePerverse D l hl Ω c).FullSubcategory) ⟶ Q), Epi f →
      IsZero ((qbarCurveDerivedRestriction D l hl Ω c).obj Q.obj) → IsZero Q.obj)

/-- The canonical finite-stage comparison across the geometric Frobenius square.
Its three factors are inverse composition, equality of the two composite maps, and
composition. This is the universe-general form of zlRationalFrobeniusComparison.
Source: blueprint Weil compatibility (blueprint: lem-dl-a1-curve-intermediate-extension). -/
def qbarCurveRationalFrobeniusComparison
    (w : (D.geometricFrobenius c.U).hom ≫ qbarCurveGeometricOpen D c =
      qbarCurveGeometricOpen D c ≫ (D.geometricFrobenius c.C).hom)
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber c.C).left E) :
    (sfWeilFrobeniusPullback D l hl c.U
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj
        ((@rationalDerivedPullback l _
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) _ _ _ _ _
          (qbarCurveGeometricOpen D c) (sfWeilPrimeInvertible D l hl c.U)
          (sfWeilPrimeInvertible D l hl c.C)).obj K) ≅
    (@rationalDerivedPullback l _
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) _ _ _ _ _
      (qbarCurveGeometricOpen D c) (sfWeilPrimeInvertible D l hl c.U)
      (sfWeilPrimeInvertible D l hl c.C)).obj
        ((sfWeilFrobeniusPullback D l hl c.C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).obj K) :=
  (@localPullbackComposition l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
    _ _ _ _ _ _ (D.geometricFrobenius c.U).hom (qbarCurveGeometricOpen D c)
    (sfWeilPrimeInvertible D l hl c.U) (sfWeilPrimeInvertible D l hl c.U)
    (sfWeilPrimeInvertible D l hl c.C) K).symm ≪≫
  eqToIso (congrArg (fun f ↦ (@rationalDerivedPullback l _
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) _ _ _ _ _ f
    (sfWeilPrimeInvertible D l hl c.U) (sfWeilPrimeInvertible D l hl c.C)).obj K) w) ≪≫
  @localPullbackComposition l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
    _ _ _ _ _ _ (qbarCurveGeometricOpen D c) (D.geometricFrobenius c.C).hom
    (sfWeilPrimeInvertible D l hl c.U) (sfWeilPrimeInvertible D l hl c.C)
    (sfWeilPrimeInvertible D l hl c.C) K

/-- The full characterization for one lisse Weil sheaf. The unique comparison is an
isomorphism of geometric complexes with prescribed restriction. Naturality quantifies
also over geometric sheaf maps; the final clause says that comparisons between Weil
extensions intertwine their structure isomorphisms.
Source: blueprint characterization, naturality and Weil sentences
(blueprint: lem-dl-a1-curve-intermediate-extension). -/
def QbarCurveIntermediateExtensionAssertions
    (β : qbarCurveShiftedOrdinaryImage D l hl Ω c ⋙
        qbarCurveDerivedRestriction D l hl Ω c ≅ qbarCurveShiftedSource D l Ω c)
    (rΦ : qbarCurveDerivedRestriction D l hl Ω c ⋙
        sfCommonStageWeilFrobeniusPullback D l hl c.U Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl c.C Ω ⋙
        qbarCurveDerivedRestriction D l hl Ω c)
    (sΦ : (shiftFunctor
        (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber c.U).left)
        (1 : ℤ)) ⋙ sfCommonStageWeilFrobeniusPullback D l hl c.U Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl c.U Ω ⋙ shiftFunctor _ (1 : ℤ))
    (F₀ : sfCommonStageWeilSheaf D l hl c.U Ω) : Prop :=
  ∃ hA : qbarCurvePerverse D l hl Ω c
      ((qbarCurveShiftedOrdinaryImage D l hl Ω c).obj
        (qbarCurveWeilCarrier D l hl Ω c F₀)),
    QbarCurveBoundaryMinimal D l hl Ω c _ hA ∧
    (∀ (P : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber c.C).left)
      (hP : qbarCurvePerverse D l hl Ω c P)
      (α : (qbarCurveDerivedRestriction D l hl Ω c).obj P ≅ F₀.obj.carrier⟦(1 : ℤ)⟧),
      QbarCurveBoundaryMinimal D l hl Ω c P hP ↔
        ∃! e : P ≅ (qbarCurveShiftedOrdinaryImage D l hl Ω c).obj
            (qbarCurveWeilCarrier D l hl Ω c F₀),
          (qbarCurveDerivedRestriction D l hl Ω c).mapIso e ≪≫
            β.app (qbarCurveWeilCarrier D l hl Ω c F₀) = α) ∧
    (∀ (F₀' : sfCommonStageWeilSheaf D l hl c.U Ω)
      (_hF' : HasCommonStageLisseLattice l Ω (D.geometricFiber c.U).left F₀'.obj.carrier)
      (P P' : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber c.C).left)
      (hP : qbarCurvePerverse D l hl Ω c P) (hP' : qbarCurvePerverse D l hl Ω c P')
      (α : (qbarCurveDerivedRestriction D l hl Ω c).obj P ≅ F₀.obj.carrier⟦(1 : ℤ)⟧)
      (α' : (qbarCurveDerivedRestriction D l hl Ω c).obj P' ≅ F₀'.obj.carrier⟦(1 : ℤ)⟧)
      (_hmin : QbarCurveBoundaryMinimal D l hl Ω c P hP)
      (_hmin' : QbarCurveBoundaryMinimal D l hl Ω c P' hP')
      (f : qbarCurveWeilCarrier D l hl Ω c F₀ ⟶ qbarCurveWeilCarrier D l hl Ω c F₀')
      (e : P ≅ (qbarCurveShiftedOrdinaryImage D l hl Ω c).obj
        (qbarCurveWeilCarrier D l hl Ω c F₀))
      (e' : P' ≅ (qbarCurveShiftedOrdinaryImage D l hl Ω c).obj
        (qbarCurveWeilCarrier D l hl Ω c F₀'))
      (_he : (qbarCurveDerivedRestriction D l hl Ω c).mapIso e ≪≫
        β.app (qbarCurveWeilCarrier D l hl Ω c F₀) = α)
      (_he' : (qbarCurveDerivedRestriction D l hl Ω c).mapIso e' ≪≫
        β.app (qbarCurveWeilCarrier D l hl Ω c F₀') = α'),
      ∃! g : P ⟶ P',
        (qbarCurveDerivedRestriction D l hl Ω c).map g ≫ α'.hom =
          α.hom ≫ (shiftFunctor _ (1 : ℤ)).map f.hom ∧
        g ≫ e'.hom = e.hom ≫ (qbarCurveShiftedOrdinaryImage D l hl Ω c).map f) ∧
    (∃ θA : (sfCommonStageWeilFrobeniusPullback D l hl c.C Ω).obj
          ((qbarCurveShiftedOrdinaryImage D l hl Ω c).obj
            (qbarCurveWeilCarrier D l hl Ω c F₀)) ≅
        (qbarCurveShiftedOrdinaryImage D l hl Ω c).obj
          (qbarCurveWeilCarrier D l hl Ω c F₀),
      rΦ.hom.app _ ≫ (qbarCurveDerivedRestriction D l hl Ω c).map θA.hom ≫
          (β.app (qbarCurveWeilCarrier D l hl Ω c F₀)).hom =
        (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).map
            (β.app (qbarCurveWeilCarrier D l hl Ω c F₀)).hom ≫
          sΦ.hom.app F₀.obj.carrier ≫ (shiftFunctor _ (1 : ℤ)).map F₀.obj.str.hom ∧
      ∀ (P : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber c.C).left)
        (hP : qbarCurvePerverse D l hl Ω c P)
        (_hmin : QbarCurveBoundaryMinimal D l hl Ω c P hP)
        (θP : (sfCommonStageWeilFrobeniusPullback D l hl c.C Ω).obj P ≅ P)
        (α : (qbarCurveDerivedRestriction D l hl Ω c).obj P ≅ F₀.obj.carrier⟦(1 : ℤ)⟧)
        (e : P ≅ (qbarCurveShiftedOrdinaryImage D l hl Ω c).obj
          (qbarCurveWeilCarrier D l hl Ω c F₀))
        (_he : (qbarCurveDerivedRestriction D l hl Ω c).mapIso e ≪≫
          β.app (qbarCurveWeilCarrier D l hl Ω c F₀) = α),
        rΦ.hom.app P ≫ (qbarCurveDerivedRestriction D l hl Ω c).map θP.hom ≫ α.hom =
          (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).map α.hom ≫
            sΦ.hom.app F₀.obj.carrier ≫ (shiftFunctor _ (1 : ℤ)).map F₀.obj.str.hom →
        θP.hom ≫ e.hom =
          (sfCommonStageWeilFrobeniusPullback D l hl c.C Ω).map e.hom ≫ θA.hom)

/-- The ordinary middle extension shifted by one is the uniquely characterized
perverse intermediate extension, naturally and with its Weil structure.

Source: main-20261015, rem-dl-a1-conventions, second paragraph
(blueprint: lem-dl-a1-curve-intermediate-extension).

Proof, following the seven steps of the DAG:
1. The geometric curve is smooth of pure dimension one, and the complement of the
   dense open is a finite set of closed points (lem-sc-dense-open-finite-complement).
   Clause (4) of thm-a1-curve-perverse-heart makes A=(j_*F)[1] perverse.
   Ordinary restriction and its counit identify j*A with F[1], as in
   lem-a1-qbar-open-closed-cohomology. These are the components of β below.
2. A perverse boundary object has punctual H^{-1}, hence zero H^{-1} by clause (3)
   of the curve-heart theorem. It is i_*E in degree zero by the closed essential
   image assertion. The two vanishings of lem-dl-a1-boundary-hom-vanishing therefore
   kill every boundary perverse subobject and quotient of A.
3. For a characterized extension P, clause (5) gives the perverse quotient H^0P.
   It is on the boundary, so vanishes. Thus P=G[1], with G having no punctual
   subsheaf and j*G=F.
4. The sheaf adjunction gives u:G→j_*F. Its kernel and cokernel are on the finite
   boundary. The kernel is punctual, so zero. Write the cokernel as T.
5. Apply lem-weil-heart-short-exact-triangles(4) first in the standard heart to
   G→j_*F→T, rotate its triangle, and apply the same lemma in the perverse heart.
   This gives 0→T→P→A→0. Boundary minimality kills T, giving the comparison.
6. Shifting identifies its Hom set with Hom(G,j_*F), and sheaf adjunction with
   Hom(j*G,F). Thus restriction determines it uniquely. The same argument for
   arbitrary sheaf maps gives the naturality equation displayed above.
7. The normalized pullback-composition comparison across the Frobenius square
   and the sheaf unit commute with Frobenius, by the last paragraph of
   lem-a1-qbar-open-closed-cohomology. Both composites restrict to the same map;
   uniqueness from Step 6 makes them equal. Inverting an equivariant isomorphism
   preserves equivariance. All triangles in Step 5 are geometric, not triangles
   in a category of Frobenius pairs. -/
theorem qbarCurveIntermediateExtension [GeometricallyConnected c.C.hom] :
    ∃ (sR : (qbarCurveDerivedRestriction D l hl Ω c).CommShift ℤ)
      (sΦ : (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).CommShift ℤ)
      (w : (D.geometricFrobenius c.U).hom ≫ qbarCurveGeometricOpen D c =
        qbarCurveGeometricOpen D c ≫ (D.geometricFrobenius c.C).hom)
      (rΦ : qbarCurveDerivedRestriction D l hl Ω c ⋙
          sfCommonStageWeilFrobeniusPullback D l hl c.U Ω ≅
        sfCommonStageWeilFrobeniusPullback D l hl c.C Ω ⋙
          qbarCurveDerivedRestriction D l hl Ω c)
      (β : qbarCurveShiftedOrdinaryImage D l hl Ω c ⋙
          qbarCurveDerivedRestriction D l hl Ω c ≅ qbarCurveShiftedSource D l Ω c),
      (∀ K : generalAlgebraicallyClosedConstructibleCategory
          l Ω (D.geometricFiber c.C).left,
        HEq (rΦ.hom.app K)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := Ω) (Y := (D.geometricFiber c.U).left) K.stage).map
              (qbarCurveRationalFrobeniusComparison D l hl Ω c w K.stage K.obj).hom)) ∧
      (∀ F : sfCommonStageHeart l (D.geometricFiber c.U).left Ω,
        (β.app F).hom =
          (fun [cs : (qbarCurveDerivedRestriction D l hl Ω c).CommShift ℤ] ↦
            ((qbarCurveDerivedRestriction D l hl Ω c).commShiftIso (1 : ℤ)).hom.app
                ((qbarCurveOrdinaryPushforward D l hl Ω c).obj F).obj ≫
              (shiftFunctor _ (1 : ℤ)).map
                ((qbarCurveOrdinaryAdjunction D l hl Ω c).counit.app F).hom)
            (cs := sR)) ∧
      (∀ (F₀ : sfCommonStageWeilSheaf D l hl c.U Ω),
        HasCommonStageLisseLattice l Ω (D.geometricFiber c.U).left F₀.obj.carrier →
        QbarCurveIntermediateExtensionAssertions D l hl Ω c β rΦ
          ((fun [cs : (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).CommShift ℤ] ↦
            (sfCommonStageWeilFrobeniusPullback D l hl c.U Ω).commShiftIso (1 : ℤ))
              (cs := sΦ)) F₀) := by
  sorry

end WeilConjectures
