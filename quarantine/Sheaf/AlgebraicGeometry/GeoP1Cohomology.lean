/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.GeoCartierCycleClass
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
import Sheaf.CategoryTheory.Sites.TorsorWithSection
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.PurEtaleScalarMateProjection
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.CategoryTheory.Adjunction.CoefficientExchange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek

/-!
# The ordinary pro-etale projective-line decomposition and trace

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-p1-cohomology,
(G2), (G3) and proof steps 1--9; Stacks Project, Tag 0GL5
(blueprint: sk-lem-geo-p1-cohomology).

The coefficient object and signed twists are comparison pullbacks of the existing
ordinary etale objects. This is the ordinary small pro-etale derived category.
The comparison map is the counit mate, and the two decomposition maps use the
same Kummer-normalized Chern class. All helpers spell out these canonical arrows.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Exact comparison on the entire ordinary derived category; its bounded-below
restriction is `siteComparisonDerivedPullbackPlus`.
Source: blueprint (G2), proof step 6 (blueprint: sk-lem-geo-p1-cohomology). -/
abbrev geoP1Comparison (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory

/-- The existing exact inverse image, expressed as its left derived functor.
Source: blueprint (G2), base-change clause (blueprint: sk-lem-geo-p1-cohomology). -/
@[implicit_reducible]
def geoP1Pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor

/-- The existing K-injective derived direct image on ordinary module sheaves.
Source: blueprint (G2) (blueprint: sk-lem-geo-p1-cohomology). -/
@[implicit_reducible]
def geoP1Pushforward (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor

/-- Pullback commutes with comparison by the actual site-comparison square.
Source: blueprint proof step 7 (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1PullComparison (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    geoP1Comparison A Y ⋙ geoP1Pullback A f ≅
      Etale.ordinaryFinitePullback A f ⋙ geoP1Comparison A X :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _

/-- The canonical unbounded comparison mate. Only its bounded-below instances
are asserted invertible below. Its adjunct is the pull comparison followed by the
image of the etale counit; no arbitrary pushforward comparison is selected.
Source: blueprint proof steps 6--7 (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1PushComparison (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A X) :
    (geoP1Comparison A Y).obj ((Etale.ordinaryFinitePushforward A f).obj K) ⟶
      (geoP1Pushforward A f).obj ((geoP1Comparison A X).obj K) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
    ((geoP1PullComparison A f).hom.app _ ≫
      (geoP1Comparison A X).map
        ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K))

/-- Comparison preserves the specified ordered sum by its two injections.
Source: blueprint proof step 6 (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1SumComparison (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (K L : Etale.DerivedCategoryModule A S) :
    ((geoP1Comparison A S).obj K ⊞ (geoP1Comparison A S).obj L) ⟶
      (geoP1Comparison A S).obj (K ⊞ L) :=
  biprod.desc ((geoP1Comparison A S).map biprod.inl)
    ((geoP1Comparison A S).map biprod.inr)

/-- The constant coefficient object, canonically the constant pro-etale sheaf
in degree zero by the exact comparison constant-sheaf identification.
Source: blueprint (G2) (blueprint: sk-lem-geo-p1-cohomology). -/
abbrev geoP1Unit (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :=
  (geoP1Comparison A S).obj (Etale.ordinaryFiniteUnit A S)

/-- The signed finite Tate object, pulled through comparison and shifted.
Exact comparison commutes with shifts, so this is Λ_S(a)[b].
Source: blueprint definition of the twists (blueprint: sk-lem-geo-p1-cohomology). -/
abbrev geoP1Twist (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (a b : ℤ) :=
  (geoP1Comparison A S).obj (Etale.p1DecompositionTwist A N hA S a b)

/-- The same normalized Kummer Chern arrow used by the ordinary trace. Its
specification is the scalar Kummer boundary of the existing projective-space O(1),
not an arbitrary degree-two class. Its comparison image is the pro-etale class.
Source: blueprint proof steps 1, 2, 6 (blueprint: sk-lem-geo-p1-cohomology). -/
abbrev geoP1EtaleChern (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :=
  (Etale.projectiveLineTraceDatum N hN A hA S hS).chern

/-- The specified map (G2), obtained from the unit and the adjoint of the
Kummer Chern class, then the canonical direct-image comparison mate.
Source: blueprint (G2), proof steps 5--6 (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1DecompositionMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Unit A S ⊞ geoP1Twist A N hA S (-1) (-2)) ⟶
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj (geoP1Unit A (ProjectiveLine S)) :=
  geoP1SumComparison A S _ _ ≫
    (geoP1Comparison A S).map
      (Etale.p1DecompositionMap A N hN hA S hS (geoP1EtaleChern A N hN hA S hS)) ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S) _

/-- The twist of (G2) by (1)[2], expressed in the order Λ(1)[2] plus Λ.
Its two components are the shifted twisted unit and the very same Chern adjunct.
The projection formula and evaluation identify this with twisting (G2).
Source: blueprint proof step 8 (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1TwistedMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ⟶
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
        (geoP1Twist A N hA (ProjectiveLine S) 1 2) :=
  geoP1SumComparison A S _ _ ≫
    (geoP1Comparison A S).map
      (Etale.projectiveLineTraceDatum N hN A hA S hS).decomposition.hom ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S) _

/-- The normalized constant-object pullback through the comparison square.
Source: blueprint base-change clause (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1UnitPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (geoP1Pullback A f).obj (geoP1Unit A Y) ≅ geoP1Unit A X :=
  (geoP1PullComparison A f).app _ ≪≫
    (geoP1Comparison A X).mapIso (Etale.ordinaryFiniteUnitPullback A f)

/-- The roots-normalized signed-twist pullback, with the exact comparison square.
Source: blueprint base-change clause (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1TwistPullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (a b : ℤ) :
    (geoP1Pullback A f).obj (geoP1Twist A N hA Y a b) ≅ geoP1Twist A N hA X a b :=
  (geoP1PullComparison A f).app _ ≪≫
    (geoP1Comparison A X).mapIso (Etale.p1DecompositionTwistPullback A N hN hA f hY a b)

/-- Canonical comparison on the ordered summands of (G2).
Source: blueprint proof step 7 (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1SourceMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Pullback A g).obj (geoP1Unit A S ⊞ geoP1Twist A N hA S (-1) (-2)) ⟶
      (geoP1Unit A S' ⊞ geoP1Twist A N hA S' (-1) (-2)) :=
  biprod.lift
    ((geoP1Pullback A g).map biprod.fst ≫ (geoP1UnitPullback A g).hom)
    ((geoP1Pullback A g).map biprod.snd ≫
      (geoP1TwistPullback A N hN hA g hS (-1) (-2)).hom)

/-- The actual derived exchange map of the Cartesian projective-line square.
This is the mate specified by the recorded derived adjunction, for every base map.
Source: blueprint proof step 7 (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1Exchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine S))
      (ModuleCat.{u + 1} A))) :
    (geoP1Pullback A g).obj ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj K) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj
        ((geoP1Pullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).obj K) :=
  (derivedBaseChangeMap (ModuleCat.{u + 1} A)
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq).app K

/-- Exchange on the coefficient object with its canonical constant identification.
Source: blueprint (G2), base-change clause (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1UnitExchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S) :
    (geoP1Pullback A g).obj
        ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj (geoP1Unit A (ProjectiveLine S))) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj (geoP1Unit A (ProjectiveLine S')) :=
  geoP1Exchange A g _ ≫ (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
    (geoP1UnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom

/-- Exchange on the shifted positive twist, using the normalized finite-line pullback.
Source: blueprint proof steps 8--9 (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1TwistExchange (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Pullback A g).obj ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
      (geoP1Twist A N hA (ProjectiveLine S) 1 2)) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj
        (geoP1Twist A N hA (ProjectiveLine S') 1 2) :=
  geoP1Exchange A g _ ≫ (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
    (geoP1TwistPullback A N hN hA (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) 1 2).hom

/-- The normalized trace is projection onto the constant second summand after the
inverse of the twisted (G2). The isomorphism's hom is fixed in the theorem below.
Source: blueprint (G3) (blueprint: sk-lem-geo-p1-cohomology). -/
def geoP1Trace (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u})
    (b : (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ≅
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
        (geoP1Twist A N hA (ProjectiveLine S) 1 2)) :
    (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
      (geoP1Twist A N hA (ProjectiveLine S) 1 2) ⟶ geoP1Unit A S :=
  b.inv ≫ biprod.snd

/-- The canonical decomposition (G2) and the trace (G3), with every Noetherian
base change. The existential isomorphisms have their homs fixed to `geoP1TwistedMap`;
their inverses, hence the traces, are uniquely determined. The untwisted map is
fixed separately to the unit and the same Kummer Chern class.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-p1-cohomology,
(G2), (G3), proof steps 1--9; Stacks Project, Tag 0GL5
(blueprint: sk-lem-geo-p1-cohomology).

Proof:
1. Projective space is proper (lemma-nagata-projective-space-base-change-proper),
   hence separated and finite type, so its source over a Noetherian base is
   Noetherian. On the charts R[t], R[s], st=1, the infinity divisor has ideals
   (1) and (s). Polynomial coefficient comparison makes s regular over every base.
   Its dual ideal has transition e_0=(x_0/x_1)e_1, exactly the existing O(1).
2. On ordinary etale sites form b from the shifted twisted unit and the scalar
   Kummer class (def-asd-ordinary-finite-p1-kummer-class). Unit/counit triangles
   compare units with exchange. Kummer naturality and relative torsor cohomology
   compare the O(1) class after every base change, including nonflat ones.
3. For Z/N coefficients, proper geometric-fibre comparison reduces invertibility
   to the algebraically closed projective line. Its genus is zero; proper curve
   cohomology gives degrees 0 and 2 only. The Kummer degree coordinate sends O(1)
   to one by lem-sc-constant-proper-degree-coordinates and lem-pc-degree-agrees-sc.
   Derived stalk conservativity proves b invertible.
4. Extend scalars to A. The canonical scalar mate is the proper projection map
   after restriction (lem-pur-etale-scalar-mate-projection). Restriction reflects
   isomorphisms. Flatness of the Tate line identifies the shifted input after
   extension, without flatness of A over Z/N. The adjunct formula identifies the
   two components, giving exactly the same b for A.
5. Tensor with the negative line shifted by -2 and evaluate. Proper projection
   gives the untwisted decomposition with its unit and Chern-adjoint components,
   precisely p1DecompositionMap. Normalized twist pullback, evaluation and
   lem-weil-pbc-ringed-exchange-tensor-coherence give its base-change square.
6. Apply exact comparison. Every object involved is bounded below. The qcqs
   direct-image theorem sk-thm-pe-direct-image-comparison makes the canonical
   counit mate invertible here, so geoP1DecompositionMap is invertible. Comparison
   preserves the unit and the scalar Kummer class; sk-lem-geo-cartier identifies
   the latter with the Cartier composite for the infinity divisor of step 1.
7. Apply lem-weil-pbc-coefficient-exchange-mates to the four derived adjunctions,
   the exact comparison functors and their pullback squares. Their counit-mate
   normalization identifies the image of the etale exchange square with exactly
   geoP1Exchange, giving the asserted untwisted base-change equation.
8. Do the same for the positive shifted line. Exchange/tensor coherence and
   canonical comparison monoidality identify its decomposition with twisting
   (G2) by (1)[2], and give the corresponding ordered-sum base-change square.
9. Invert that square and project to the constant second summand. The ordered
   sum comparison preserves this projection and its constant comparison is
   geoP1UnitPullback. This is exactly the trace equation displayed below. -/
theorem geoP1Cohomology (ℓ : ℕ) (hℓ : ℓ.Prime) (r : ℕ) (_hr : 0 < r)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((ℓ ^ r : ℕ) : A) = 0) :
    ∃ b : ∀ (S : Scheme.{u}) [IsNoetherian S]
      (_hS : IsUnit ((ℓ ^ r : ℕ) : Γ(S, ⊤))),
        (geoP1Twist A (ℓ ^ r) hA S 1 2 ⊞ geoP1Unit A S) ≅
          (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
            (geoP1Twist A (ℓ ^ r) hA (ProjectiveLine S) 1 2),
      (∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit ((ℓ ^ r : ℕ) : Γ(S, ⊤))),
        IsIso (geoP1DecompositionMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA S hS) ∧
        (b S hS).hom = geoP1TwistedMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA S hS) ∧
      ∀ (S' S : Scheme.{u}) [IsNoetherian S'] [IsNoetherian S] (g : S' ⟶ S)
        (hS : IsUnit ((ℓ ^ r : ℕ) : Γ(S, ⊤)))
        (hS' : IsUnit ((ℓ ^ r : ℕ) : Γ(S', ⊤))),
        ((geoP1Pullback A g).map
            (geoP1DecompositionMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA S hS) ≫
          geoP1UnitExchange A g =
          geoP1SourceMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA g hS ≫
            geoP1DecompositionMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA S' hS') ∧
        ((geoP1Pullback A g).map (geoP1Trace A (ℓ ^ r) hA S (b S hS)) ≫
            (geoP1UnitPullback A g).hom =
          geoP1TwistExchange A (ℓ ^ r) (pow_pos hℓ.pos r) hA g hS ≫
            geoP1Trace A (ℓ ^ r) hA S' (b S' hS')) := by
  sorry

end AlgebraicGeometry.ProEtale
