module

public import Sheaf.Paper.IntegralLisseClosedBaseChange
public import Sheaf.Paper.RootTowerCoordinateFace
public import Sheaf.CategoryTheory.RightDerivedSingleH0
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit
import Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-!
# Normalized specialization to a surjective closed fibre section

Source: main-20261015, direct-image stability proof paragraph (3), returned proof
steps 3 and 5, agent-extracted full integral-source specialization.
(blueprint: lem-sfb-integral-fibre-section-specialization).

The maps use actual profinite test schemes and the actual derived counit. The
coefficient comparison always uses restriction in its forward direction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralFibreSection

open IntegralLisseClosedBaseChange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual test projection, with its scheme endpoints made explicit.
Source: def-sfb-profinite-test-objects, the map X[P] → X
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def testBase (X : Scheme.{u}) (P : Profinite.{u}) :
    ((profiniteToProEtOf X).obj P).left ⟶ X :=
  ((profiniteToProEtOf X).obj P).hom

/-- The full-source projection q_P from the recorded actual test object.
Source: the node's notation q_P (blueprint: lem-sfb-integral-fibre-section-specialization). -/
def testProjection {X U : Scheme.{u}} (q : X ⟶ U) (P : Profinite.{u}) :
    ((profiniteToProEtOf X).obj P).left ⟶ U :=
  (testBase X P) ≫ q

/-- The induced section square commutes on the actual test schemes.
Source: the node's displayed section diagram
(blueprint: lem-sfb-integral-fibre-section-specialization).
Proof: the pullback lift defining testMap commutes with its second projection.
Compose this identity with q, reassociate, and substitute i ≫ q = s. -/
theorem testSection_square {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) (P : Profinite.{u}) :
    RootCoordinateFace.testMap i P ≫ testProjection q P =
      (testBase Z P) ≫ s := by
  sorry

/-- The actual map a_P into the cartesian closed fibre.
Source: the node's definition of a_P
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def fibreSection {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) (P : Profinite.{u}) :
    ((profiniteToProEtOf Z).obj P).left ⟶ pullback (testProjection q P) s :=
  pullback.lift (RootCoordinateFace.testMap i P)
    (testBase Z P) (testSection_square q s i w P)

/-- L_P placed in degree zero, using the existing ordinary module pullback.
Source: the node's notation L_P[0]
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def testComplex {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Profinite.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology ((profiniteToProEtOf X).obj P).left)
      Ab.{u + 1}) (condensedRingObj Λ ((profiniteToProEtOf X).obj P).left)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((CondensedRing.upperStar Λ (testBase X P)).obj M)

/-- Projection compatibility for the recorded map on actual test schemes.
Source: the node's definition of i_P and rho_P
(blueprint: lem-sfb-integral-fibre-section-specialization).
Proof: testMap is the pullback lift with second component testBase Z P followed by i.
The second projection identity for this lift is the asserted equation. -/
theorem testMap_projection {X Z : Scheme.{u}} (i : Z ⟶ X) (P : Profinite.{u}) :
    RootCoordinateFace.testMap i P ≫ testBase X P = testBase Z P ≫ i := by
  sorry

/-- The canonical identification i_P^* L_P[0] = rho_P^* i^* L[0].
Source: the node's defining adjunct, final identification
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def boundaryIdentification {X Z : Scheme.{u}} (i : Z ⟶ X) (P : Profinite.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (pull Λ (RootCoordinateFace.testMap i P)).obj (testComplex Λ M P) ≅
      (pull Λ (testBase Z P)).obj
        ((pull Λ i).obj ((DerivedCategory.singleFunctor _ 0).obj M)) :=
  (pull Λ (RootCoordinateFace.testMap i P)).mapIso
      (((CondensedRing.upperStar Λ (testBase X P))
        |>.mapDerivedCategorySingleFunctor 0).symm.app M) ≪≫
    (square Λ (CommSq.mk (testMap_projection i P))).symm.app
      ((DerivedCategory.singleFunctor _ 0).obj M)

/-- Theta for every degree-zero module, without any lisseness or invertibility assumption.
The exchange is defined as the rho_P-adjunct of i_P^* of the actual q_P-counit;
the last arrow is precisely the canonical boundary identification.
Source: the node's defining adjunct formula and its last paragraph
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def specialization {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) (P : Profinite.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (pull Λ s).obj
        ((CondensedRing.moduleObjectDerivedPushforward Λ (testProjection q P)).obj
          (testComplex Λ M P)) ⟶
      (CondensedRing.moduleObjectDerivedPushforward Λ
        (testBase Z P)).obj
        ((pull Λ (testBase Z P)).obj
          ((pull Λ i).obj ((DerivedCategory.singleFunctor _ 0).obj M))) :=
  (exchange Λ (CommSq.mk (testSection_square q s i w P))).app (testComplex Λ M P) ≫
    (CondensedRing.moduleObjectDerivedPushforward Λ
      (testBase Z P)).map (boundaryIdentification Λ i P M).hom

/-- The actual fibre-section map has the specified first projection i_P.
Source: the node's definition of a_P
(blueprint: lem-sfb-integral-fibre-section-specialization).
Proof: apply the first projection identity of the defining pullback lift. -/
theorem fibreSection_fst {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) (P : Profinite.{u}) :
    fibreSection q s i w P ≫ pullback.fst (testProjection q P) s =
      RootCoordinateFace.testMap i P := by
  sorry

/-- The actual fibre-section map has the specified second projection rho_P.
Source: the node's definition of a_P
(blueprint: lem-sfb-integral-fibre-section-specialization).
Proof: apply the second projection identity of the defining pullback lift. -/
theorem fibreSection_snd {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) (P : Profinite.{u}) :
    fibreSection q s i w P ≫ pullback.snd (testProjection q P) s = testBase Z P := by
  sorry

/-- The canonical derived composition comparison for a_P followed by q_(Z,P),
normalized by conjugating the actual pullback identification and actual adjunctions.
Source: the node's cartesian factorization clause
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def fibreComposition {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) (P : Profinite.{u}) :
    CondensedRing.moduleObjectDerivedPushforward Λ (fibreSection q s i w P) ⋙
        CondensedRing.moduleObjectDerivedPushforward Λ (pullback.snd (testProjection q P) s) ≅
      CondensedRing.moduleObjectDerivedPushforward Λ
        (testBase Z P) :=
  (conjugateIsoEquiv (adj Λ (testBase Z P))
    ((adj Λ (pullback.snd (testProjection q P) s)).comp
      (adj Λ (fibreSection q s i w P)))
    ((pullComp Λ (fibreSection q s i w P) (pullback.snd (testProjection q P) s)).symm ≪≫
      eqToIso (congrArg (pull Λ) (fibreSection_snd q s i w P)))).symm

/-- The canonical pullback identification a_P^* h_P^* = i_P^*.
Source: the node's factorization, fibre pullback identification
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def fibrePullIdentification {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) (P : Profinite.{u}) :
    pull Λ (pullback.fst (testProjection q P) s) ⋙ pull Λ (fibreSection q s i w P) ≅
      pull Λ (RootCoordinateFace.testMap i P) :=
  (pullComp Λ (fibreSection q s i w P) (pullback.fst (testProjection q P) s)).symm ≪≫
    eqToIso (congrArg (pull Λ) (fibreSection_fst q s i w P))

/-- The exchange followed by the actual a_P-unit, the normalized composition comparison,
and the two canonical pullback identifications. No inverse of the unit is used here.
Source: the node's cartesian-exchange factorization
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def factoredSpecialization {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) (P : Profinite.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (pull Λ s).obj
        ((CondensedRing.moduleObjectDerivedPushforward Λ (testProjection q P)).obj
          (testComplex Λ M P)) ⟶
      (CondensedRing.moduleObjectDerivedPushforward Λ
        (testBase Z P)).obj
        ((pull Λ (testBase Z P)).obj
          ((pull Λ i).obj ((DerivedCategory.singleFunctor _ 0).obj M))) :=
  (exchange Λ (CommSq.mk (pullback.condition (f := testProjection q P) (g := s)))).app
      (testComplex Λ M P) ≫
    (CondensedRing.moduleObjectDerivedPushforward Λ
      (pullback.snd (testProjection q P) s)).map
      ((adj Λ (fibreSection q s i w P)).unit.app
        ((pull Λ (pullback.fst (testProjection q P) s)).obj (testComplex Λ M P))) ≫
    (fibreComposition Λ q s i w P).hom.app _ ≫
    (CondensedRing.moduleObjectDerivedPushforward Λ
      (testBase Z P)).map
      ((fibrePullIdentification Λ q s i w P).hom.app (testComplex Λ M P) ≫
        (boundaryIdentification Λ i P M).hom)

/-- The ordinary pullback comparison for the section square, before taking its mate.
Source: the node's degree-zero restriction square and canonical composition comparisons
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def ordinarySquare {A U B Z : Scheme.{u}} {q : A ⟶ U} {s : Z ⟶ U}
    {j : B ⟶ A} {r : B ⟶ Z} (w : CommSq j r q s) :
    CondensedRing.upperStar Λ s ⋙ CondensedRing.upperStar Λ r ≅
      CondensedRing.upperStar Λ q ⋙ CondensedRing.upperStar Λ j :=
  (CondensedRing.upperStarComp Λ r s).symm ≪≫
    CondensedRing.upperStarCongr Λ w.w.symm ≪≫ CondensedRing.upperStarComp Λ j q

/-- The ordinary counit mate as a natural transformation, with its endpoints cached.
Source: the node's degree-zero restriction along a section square
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def ordinaryExchange {A U B Z : Scheme.{u}} {q : A ⟶ U} {s : Z ⟶ U}
    {j : B ⟶ A} {r : B ⟶ Z} (w : CommSq j r q s) :
    CondensedRing.lowerStar Λ q ⋙ CondensedRing.upperStar Λ s ⟶
      CondensedRing.upperStar Λ j ⋙ CondensedRing.lowerStar Λ r :=
  Adjunction.squareExchange (CondensedRing.upperStarLowerStarAdjunction Λ q)
    (CondensedRing.upperStarLowerStarAdjunction Λ r)
    (CondensedRing.upperStar Λ s) (CondensedRing.upperStar Λ j) (ordinarySquare Λ w)

/-- The ordinary restriction of full-source sections, expressed by the ordinary adjunction.
Source: the node's degree-zero restriction clause
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def ordinaryRestriction {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) (P : Profinite.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology ((profiniteToProEtOf X).obj P).left)
      Ab.{u + 1}) (condensedRingObj Λ ((profiniteToProEtOf X).obj P).left)) :
    (CondensedRing.upperStar Λ s).obj
        ((CondensedRing.lowerStar Λ (testProjection q P)).obj M) ⟶
      (CondensedRing.lowerStar Λ (testBase Z P)).obj
        ((CondensedRing.upperStar Λ (RootCoordinateFace.testMap i P)).obj M) :=
  (ordinaryExchange Λ (CommSq.mk (testSection_square q s i w P))).app M

/-- All geometric hypotheses about the actual tests, including empty P.
Source: the node's integral and surjective-closed-fibre hypotheses
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def TestHypotheses {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) : Prop :=
  ∀ P : Profinite.{u}, IsIntegralHom (testProjection q P) ∧
    IsClosedImmersion (fibreSection q s i w P) ∧ Surjective (fibreSection q s i w P)

/-- Invertibility and the equality with the normalized cartesian factorization, for
all supplied finite-rank lisse modules and every actual profinite parameter.
Source: the node's main isomorphism and factorization clauses
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def GeometricAssertions {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) : Prop :=
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
    IsLisseCoefficientModule Λ M → ∀ P : Profinite.{u},
      IsIso (specialization Λ q s i w P M) ∧
        specialization Λ q s i w P M = factoredSpecialization Λ q s i w P M


/-- The degree-zero comparison is the ordinary restriction arrow, under the canonical
H^0 identifications for left exact direct image and exact inverse image.
Source: the node's degree-zero clause
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def DegreeZeroRestriction {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Profinite.{u}),
    (DerivedCategory.homologyFunctor _ 0).map
        (specialization Λ q s i w P M ≫
          (CondensedRing.moduleObjectDerivedPushforward Λ
            (testBase Z P)).map
            ((boundaryIdentification Λ i P M).inv ≫
              ((CondensedRing.upperStar Λ (RootCoordinateFace.testMap i P))
                |>.mapDerivedCategorySingleFunctor 0).hom.app
                ((CondensedRing.upperStar Λ (testBase X P)).obj M))) ≫
        ((CondensedRing.lowerStar Λ (testBase Z P))
          |>.singleRightDerivedH0Iso
          ((CondensedRing.upperStar Λ (RootCoordinateFace.testMap i P)).obj
            ((CondensedRing.upperStar Λ (testBase X P)).obj M))).hom =
      ((CondensedRing.lowerStar Λ (testProjection q P)).mapSingleRightDerivedH0Iso
        (CondensedRing.upperStar Λ s)
        ((CondensedRing.upperStar Λ (testBase X P)).obj M)).hom ≫
      ordinaryRestriction Λ q s i w P
        ((CondensedRing.upperStar Λ (testBase X P)).obj M)

/-- The explicit adjunct normalization for the actual parameter tests. For the terminal
parameter, the canonical identifications X[*]=X and Z[*]=Z reduce this formula to
boundary restriction s^*Rq_* L[0] → i^*L[0]. No choice of an abstract isomorphism occurs.
Source: the defining adjunct and P=* clauses
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def AdjunctNormalization {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Profinite.{u}),
    (adj Λ (testBase Z P)).homEquiv _ _
      ((square Λ (CommSq.mk (testSection_square q s i w P))).hom.app
          ((CondensedRing.moduleObjectDerivedPushforward Λ (testProjection q P)).obj
            (testComplex Λ M P)) ≫
        (pull Λ (RootCoordinateFace.testMap i P)).map
          ((adj Λ (testProjection q P)).counit.app (testComplex Λ M P)) ≫
        (boundaryIdentification Λ i P M).hom) = specialization Λ q s i w P M

/-- Actual boundary restriction before introducing a profinite parameter.
Source: the node's P=* clause, i^* of the q-counit
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def originalBoundary {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (pull Λ s).obj ((CondensedRing.moduleObjectDerivedPushforward Λ q).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) ⟶
      (pull Λ i).obj ((DerivedCategory.singleFunctor _ 0).obj M) :=
  eqToHom (congrArg (fun f ↦ (pull Λ f).obj
      ((CondensedRing.moduleObjectDerivedPushforward Λ q).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) w.symm) ≫
    (pullComp Λ i q).hom.app _ ≫
    (pull Λ i).map ((adj Λ q).counit.app ((DerivedCategory.singleFunctor _ 0).obj M))

/-- The canonical arrow from the unparametrized full source to its test source,
using the test-projection unit and the existing canonical derived composition comparison.
Source: the canonical identifications in the node's terminal-parameter clause
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def originalToTest {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Profinite.{u}) :
    (pull Λ s).obj ((CondensedRing.moduleObjectDerivedPushforward Λ q).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) ⟶
      (pull Λ s).obj
        ((CondensedRing.moduleObjectDerivedPushforward Λ (testProjection q P)).obj
          (testComplex Λ M P)) :=
  (pull Λ s).map
    ((CondensedRing.moduleObjectDerivedPushforward Λ q).map
        ((adj Λ (testBase X P)).unit.app ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
      (RootCoordinateFace.lowerComp Λ (testBase X P) q).inv.app _ ≫
      (CondensedRing.moduleObjectDerivedPushforward Λ (testProjection q P)).map
        (((CondensedRing.upperStar Λ (testBase X P)).mapDerivedCategorySingleFunctor 0).hom.app M))

/-- For a singleton parameter the actual source comparison and actual rho-unit are
isomorphisms, and they transport theta to actual unparametrized boundary restriction.
This specifies P=* using the actual test schemes, rather than replacing them by arbitrary
isomorphic objects. Empty parameters are still included in every other assertion.
Source: the node's terminal-parameter clause
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def PointNormalization {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Profinite.{u}), Subsingleton P → Nonempty P →
    IsIso (originalToTest Λ q s M P) ∧
      IsIso ((adj Λ (testBase Z P)).unit.app
        ((pull Λ i).obj ((DerivedCategory.singleFunctor _ 0).obj M))) ∧
      originalToTest Λ q s M P ≫ specialization Λ q s i w P M =
        originalBoundary Λ q s i w M ≫ (adj Λ (testBase Z P)).unit.app
          ((pull Λ i).obj ((DerivedCategory.singleFunctor _ 0).obj M))

/-- The naturality equation on the entire commuting cube, with a compatible arrow of
full-source modules. The new full source, section and base are arbitrary; continuous
parameter maps, pro-etale base change, identities and Q-parametrized maps are included
by substitution. In particular one may take the source schemes to be X[Q×P] and
X[Q×P'], with the scheme map induced by (q,p') ↦ (q,phi(q,p')).
Source: the node's full-source, base-change and whole-family naturality clauses
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def CubeNaturality {A U B Z : Scheme.{u}} {q : A ⟶ U} {s : Z ⟶ U}
    {j : B ⟶ A} {r : B ⟶ Z} (w : CommSq j r q s)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1})
      (condensedRingObj Λ A))) : Prop :=
  ∀ (A' U' B' Z' : Scheme.{u}) (q' : A' ⟶ U') (s' : Z' ⟶ U')
    (j' : B' ⟶ A') (r' : B' ⟶ Z') (a : A' ⟶ A) (v : U' ⟶ U)
    (_hv : WeaklyEtale v) (b : B' ⟶ B) (z : Z' ⟶ Z) (w' : CommSq j' r' q' s')
    (wq : CommSq a q' q v) (wr : CommSq b r' r z)
    (wj : CommSq b j' j a) (ws : CommSq z s' s v)
    (M' : Mod (Sheaf (Scheme.ProEt.topology A') Ab.{u + 1}) (condensedRingObj Λ A'))
    (f : (pull Λ a).obj K ⟶ (DerivedCategory.singleFunctor _ 0).obj M'),
    (pull Λ z).map ((exchange Λ w).app K) ≫
        (exchange Λ wr).app ((pull Λ j).obj K) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ r').map
          ((square Λ wj).inv.app K ≫ (pull Λ j').map f) =
      (square Λ ws).inv.app
          ((CondensedRing.moduleObjectDerivedPushforward Λ q).obj K) ≫
        (pull Λ s').map ((exchange Λ wq).app K ≫
          (CondensedRing.moduleObjectDerivedPushforward Λ q').map f) ≫
        (exchange Λ w').app ((DerivedCategory.singleFunctor _ 0).obj M')

/-- Naturality is asserted for each actual section square. The boundary identifications
in specialization are the canonical composition constraints, so this equation includes
transport to rho^*i^* L[0]. Module arrows include the identity geometric cube; parameter
and family arrows act on whole schemes, never on a chosen point of the parameter.
Source: all naturality clauses of the node
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def Naturality {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Profinite.{u}),
    CubeNaturality Λ (CommSq.mk (testSection_square q s i w P)) (testComplex Λ M P)

section Coefficients

variable {Λ} {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (c : Λ ⟶ Λ') [IsMonHom c]

/-- The actual ordinary tensor extension on X, embedded in degree zero, then pulled
to X[P] and transported through the canonical pullback/restriction comparison.
Source: x ↦ 1 tensor x in the node's coefficient clause
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def testScalarUnit {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Profinite.{u}) :
    testComplex Λ M P ⟶ (restrict c ((profiniteToProEtOf X).obj P).left).obj
      (testComplex Λ' ((Mod.extendScalars (coefficientMap c X)).obj M) P) :=
  ((CondensedRing.upperStar Λ (testBase X P))
    |>.mapDerivedCategorySingleFunctor 0).inv.app M ≫
    (pull Λ (testBase X P)).map (scalarUnit c X M) ≫
    (restrictPull c (testBase X P)).inv.app _ ≫
    (restrict c ((profiniteToProEtOf X).obj P).left).map
      (((CondensedRing.upperStar Λ' (testBase X P))
        |>.mapDerivedCategorySingleFunctor 0).hom.app
        ((Mod.extendScalars (coefficientMap c X)).obj M))

/-- Canonical transport to the common boundary target rho^*i^*Res L_Omega[0].
Only exact pullback/restriction and pullback-composition isomorphisms occur.
Source: the common boundary target of the node's coefficient cospan
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
@[no_expose, irreducible]
def restrictedBoundaryIdentification {X Z : Scheme.{u}} (i : Z ⟶ X) (P : Profinite.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    (pull Λ (RootCoordinateFace.testMap i P)).obj
        ((restrict c ((profiniteToProEtOf X).obj P).left).obj (testComplex Λ' N P)) ⟶
      (pull Λ (testBase Z P)).obj
        ((pull Λ i).obj ((restrict c X).obj ((DerivedCategory.singleFunctor _ 0).obj N))) :=
  (pull Λ (RootCoordinateFace.testMap i P)).map
      ((restrict c ((profiniteToProEtOf X).obj P).left).map
        (((CondensedRing.upperStar Λ' (testBase X P))
          |>.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
        (restrictPull c (testBase X P)).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj N)) ≫
    (square Λ (CommSq.mk (testMap_projection i P))).inv.app
      ((restrict c X).obj ((DerivedCategory.singleFunctor _ 0).obj N))

/-- The commuting cospan has the restricted Omega full-source object as its common
source. The first equality is module naturality for the actual tensor unit, pasted
with the common boundary transport. The second is the directional restriction square
for the Omega exchange, with that same transport. No restriction/direct-image map
is inverted, and theta_E on a restricted module has no invertibility hypothesis.
Source: the final paragraph of the node
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def ScalarCompatibility {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) : Prop :=
  ∀ (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (_hM : IsLisseCoefficientModule Λ M) (P : Profinite.{u}),
    (pull Λ s).map
        ((CondensedRing.moduleObjectDerivedPushforward Λ (testProjection q P)).map
          (testScalarUnit c M P)) ≫
        (exchange Λ (CommSq.mk (testSection_square q s i w P))).app
          ((restrict c ((profiniteToProEtOf X).obj P).left).obj
            (testComplex Λ' ((Mod.extendScalars (coefficientMap c X)).obj M) P)) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ
          (testBase Z P)).map
          (restrictedBoundaryIdentification c i P
            ((Mod.extendScalars (coefficientMap c X)).obj M)) =
      (exchange Λ (CommSq.mk (testSection_square q s i w P))).app (testComplex Λ M P) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ
          (testBase Z P)).map
          ((pull Λ (RootCoordinateFace.testMap i P)).map (testScalarUnit c M P) ≫
            restrictedBoundaryIdentification c i P
              ((Mod.extendScalars (coefficientMap c X)).obj M)) ∧
    (restrictPull c s).inv.app
        ((CondensedRing.moduleObjectDerivedPushforward Λ' (testProjection q P)).obj
          (testComplex Λ' ((Mod.extendScalars (coefficientMap c X)).obj M) P)) ≫
        (restrict c Z).map
          ((exchange Λ' (CommSq.mk (testSection_square q s i w P))).app
            (testComplex Λ' ((Mod.extendScalars (coefficientMap c X)).obj M) P)) ≫
        (restrictPush c (testBase Z P)).app _ ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ
          (testBase Z P)).map
          ((restrictPull c (RootCoordinateFace.testMap i P)).hom.app _ ≫
            restrictedBoundaryIdentification c i P
              ((Mod.extendScalars (coefficientMap c X)).obj M)) =
      (pull Λ s).map ((restrictPush c (testProjection q P)).app _) ≫
        (exchange Λ (CommSq.mk (testSection_square q s i w P))).app
          ((restrict c ((profiniteToProEtOf X).obj P).left).obj
            (testComplex Λ' ((Mod.extendScalars (coefficientMap c X)).obj M) P)) ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ
          (testBase Z P)).map
          (restrictedBoundaryIdentification c i P
            ((Mod.extendScalars (coefficientMap c X)).obj M))

end Coefficients

/-- All assertions for one of the two specified all-continuous coefficient rings.
Source: the isomorphism, normalization, H^0 and naturality clauses of the node
(blueprint: lem-sfb-integral-fibre-section-specialization). -/
def Assertions {X U Z : Scheme.{u}} (q : X ⟶ U) (s : Z ⟶ U)
    (i : Z ⟶ X) (w : i ≫ q = s) : Prop :=
  GeometricAssertions Λ q s i w ∧ DegreeZeroRestriction Λ q s i w ∧
    AdjunctNormalization Λ q s i w ∧ PointNormalization Λ q s i w ∧
      Naturality Λ q s i w

/-- Normalized specialization to a surjective closed fibre section, for both E and its
normed algebraic closure, including the forward scalar-restriction cospan.
Source: main-20261015, direct-image proof (3), returned steps 3 and 5,
agent-extracted assertion (blueprint: lem-sfb-integral-fibre-section-specialization).

Proof: (1) Internal-module transport and alpha-isomorphisms identify all pullbacks
with exact abelian inverse images with relabelled coefficients. Finite free bases
pull back, so L_P is lisse; actual affine tests remain affine.
(2) Integral lisse closed base change gives the cartesian exchange isomorphism beta
for (q_P,s), with transpose h_P^* of the q_P-counit, separately for E and Omega.
(3) The localization sequence for the surjective closed immersion a_P has empty
quasi-compact complement. The module category on that empty site is zero, so the
actual unit is invertible; the closed counit is invertible and closed pushforward
is exact. Internal-module transport preserves the actual adjunction.
(4) Exact open/closed unbounded calculus and right derivation of exact functors
make the derived a_P-unit invertible. Derived composition adjunction normalization
identifies R(q_Z)_* Ra_* with Rrho_* and its adjunction with the composite.
(5) Transpose beta followed by the pushed unit. Naturality of the q_Z-counit moves
it past that unit; the a-unit/counit triangle cancels them. What remains is i_P^*
of the q_P-counit. Thus the factored arrow equals theta, and theta is invertible.
(6) A nonnegative injective resolution identifies H^0 Rf_* M[0] with f_* M.
The derived counit induces ordinary restriction on sections. At P=* the test
projections are the canonical identity identifications and this is i^*epsilon^q.
(7) Transposing the cube paths leaves the same pulled counit and compatible module
arrow. Triangle identities give identity/composition coherence. Pro-etale base
change preserves these equations, including for whole Q-parametrized schemes.
(8) Finite-limit preservation identifies X[Q×P] with X[P] over U[Q]. A simultaneous
map Q×P'→P yields (q,p')↦(q,phi(q,p')), so the equality holds before evaluating q.
Empty parameters and empty Z use the zero categories; zero modules use zero maps.
(9) Apply the coefficient-change adjunction mate equality to q_P and rho_P.
Both transposes are the restricted counit, giving the forward restriction square.
Paste module naturality for the actual ordinary tensor unit x↦1 tensor x. This is
the common-source, common-boundary cospan; no directional comparison is inverted. -/
theorem integral_fibre_section_specialization
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E Ω : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] [NormedField Ω] [NormedAlgebra E Ω]
    [IsAlgClosure E Ω]
    {X U Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsAffine X] [IsAffine U]
    (q : X ⟶ U) [q.IsOver (Spec (.of k))]
    (s : Z ⟶ U) [s.IsOver (Spec (.of k))] [IsClosedImmersion s]
    (i : Z ⟶ X) (w : i ≫ q = s) (_h : TestHypotheses q s i w) :
    Assertions (Profinite.continuousCoefficientRingObj E) q s i w ∧
      Assertions (Profinite.continuousCoefficientRingObj Ω) q s i w ∧
      ScalarCompatibility (coefficientInclusion E Ω) q s i w := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralFibreSection
