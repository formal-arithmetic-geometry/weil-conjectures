/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.SixFunctors.GeoCartierCoeffExtension
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.Paper.EtaleKFlatCriteria
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import Sheaf.Paper.DivisibleExtensionDerivedReduction
import Sheaf.Paper.GeoCartierExponentIndependence

/-!
# The cycle class of an effective Cartier divisor

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier,
statement and proof paragraphs 1--6; Stacks Project, Tag 03PL
(blueprint: sk-lem-geo-cartier).

We use the fixed-scalar sheaf presentation of ordinary pro-etale modules, canonically
realized by `finiteCoefficientRealization` over the coefficient ring sheaf of
`def-weil-pbc-proetale-modules`. `Ext.homEquiv` identifies every degree-two Ext class
below with the displayed morphism from the degree-zero supported constant object to
its finite Tate line shifted by two. No condensed or completed coefficient category occurs.
The auxiliary definitions only spell out this class and its normalization diagrams.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The ordinary pro-etale constant module used in the Cartier class.
Source: blueprint sk-lem-geo-cartier, statement (blueprint: sk-lem-geo-cartier). -/
abbrev geoCartierConstant (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- The finite Tate line is exactly comparison inverse image of the etale roots tensor.
Source: blueprint sk-lem-geo-cartier, displayed definition of Λ(1)
(blueprint: sk-lem-geo-cartier). -/
abbrev geoCartierLine (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (Z : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
    (Scheme.finiteEtaleTateLine Z N A hA)

/-- The supported cycle class, represented through the canonical degree-two Ext/Hom
bijection. Its source uses ordinary closed direct image, not an arbitrary support object.
Source: blueprint sk-lem-geo-cartier, displayed c_D (blueprint: sk-lem-geo-cartier). -/
abbrev GeoCartierClass (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) :=
  Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D))
    (geoCartierLine A N hA Z) 2

/-- A simultaneous family allows coefficient, exponent and geometric compatibility
between its actual members. Invertibility of ℓ^r equals invertibility of ℓ for r > 0.
Source: blueprint sk-lem-geo-cartier, statement (blueprint: sk-lem-geo-cartier). -/
def GeoCartierClassFamily (ℓ : ℕ) : Type (u + 2) :=
  ∀ (r : ℕ) (_hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))),
    GeoCartierClass A (ℓ ^ r) hA i

/-- The comparison on the ordinary supported constant, with its canonical mate and
constant-sheaf identification. Invertibility is asserted in the main statement.
Source: blueprint sk-lem-geo-cartier, proof paragraph 1 (blueprint: sk-lem-geo-cartier). -/
def geoCartierSourceComparison (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D) :=
  (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app
      (Etale.ordinaryFiniteConstant A D) ≫
    (lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom

/-- Canonical pro-etale closed exchange, as the adjoint of inverse-image commutation
followed by the counit and the pullback of constants. This formula works for arbitrary
base morphisms; no weakly-etale or flatness restriction is imposed.
Source: blueprint sk-lem-geo-cartier, proof paragraph 6 (blueprint: sk-lem-geo-cartier). -/
def geoCartierExchange (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    (upperStar (ModuleCat.{u + 1} A) g).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i').obj (geoCartierConstant A D') :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i').homEquiv _ _
    (((upperStarComp (ModuleCat.{u + 1} A) i' g).symm ≪≫
      eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) sq.w.symm) ≪≫
      upperStarComp (ModuleCat.{u + 1} A) gD i).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) gD).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app
            (geoCartierConstant A D)) ≫
        Scheme.proEtaleConstantInverseImageMap gD (ModuleCat.{u + 1} A) (ModuleCat.of A A))

/-- Pull back the finite Tate line through the canonical comparison square and the
existing roots-normalized etale transport.
Source: blueprint sk-lem-geo-cartier, base-change clause (blueprint: sk-lem-geo-cartier). -/
def geoCartierLinePullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    {Z Z' : Scheme.{u}} (g : Z' ⟶ Z) (hZ : IsUnit (N : Γ(Z, ⊤))) :
    (upperStar (ModuleCat.{u + 1} A) g).obj (geoCartierLine A N hA Z) ≅
      geoCartierLine A N hA Z' :=
  (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).app
      (Scheme.finiteEtaleTateLine Z N A hA) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z').mapIso (t.line g hZ)

/-- The Chern equation is the actual Kummer boundary of the dual ideal line, expressed
in module Ext and then pulled back by ν. The integral generator fixes the usual
cohomological normalization; it does not supply an arbitrary Chern class.
Source: blueprint sk-lem-geo-cartier, statement and proof paragraph 5
(blueprint: sk-lem-geo-cartier). -/
def GeoCartierChernEquation (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z)
    (hI : i.ker.IsInvertible) (hZ : IsUnit (N : Γ(Z, ⊤)))
    (c : GeoCartierClass A N hA i) : Prop :=
  ∃ c₁ : Ext (Etale.ordinaryFiniteConstant A Z) (Scheme.finiteEtaleTateLine Z N A hA) 2,
    (Ext.mk₀ (Etale.ordinaryFiniteIntegralGenerator A Z)).comp
        (c₁.mapExactFunctor (Etale.RawModuleScalarComparison.forget A Z)) (zero_add 2) =
      Etale.supportedKummerChern A N hA i hI hZ ∧
    (Ext.mk₀ (((comparisonUpperStarConstantSheafIso A Z).app (ModuleCat.of A A)).hom ≫
      Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A) (ModuleCat.of A A))).comp
        c (zero_add 2) = c₁.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z)

/-- Derived extension at a specified sheaf map is characterized by its Hom universal
property against every unbounded complex. This is a property of the given coefficient
unit, not a choice of a replacement scalar-extension functor.
Source: Stacks 07A6; blueprint sk-lem-geo-cartier, coefficient clause
(blueprint: sk-lem-geo-cartier). -/
def GeoCartierScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (Z : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))
    (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj G) : Prop :=
  ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S)),
    Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj G ⟶ K ↦
      (DerivedCategory.singleFunctor _ 0).map η ≫
        ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).mapDerivedCategorySingleFunctor
          0).inv.app G ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).mapDerivedCategory.map f)

/-- Coefficient compatibility with the canonical supported-constant and Tate-line
units. Normalization is on constants and on pure root tensors through the comparison
adjunction unit. These generate after sheafification, so the comparisons are fixed.
Source: blueprint sk-lem-geo-cartier, coefficient clause (blueprint: sk-lem-geo-cartier). -/
def GeoCartierScalarCompatibility {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z)
    (cR : GeoCartierClass R N hR i) (cS : GeoCartierClass S N hS i) : Prop :=
  ∃ (η : geoCartierConstant R D ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj (geoCartierConstant S D))
    (θ : geoCartierLine R N hR Z ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj (geoCartierLine S N hS Z)),
    (∀ (W : D.ProEtᵒᵖ) (a : R),
      η.hom.app W ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of R R))).app W a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of S S))).app W (φ a)) ∧
    (∀ (W : Z.Etaleᵒᵖ) (a : R) (z : (Z.rootsOfUnitySheaf N).obj.obj W),
      θ.hom.app ((Scheme.toProEt Z).op.obj W)
        (((comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app
          (Scheme.finiteEtaleTateLine Z N R hR)).hom.app W
            (Scheme.finiteEtaleTateOneGenerator R N Z hR W a z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} S) Z).unit.app
        (Scheme.finiteEtaleTateLine Z N S hS)).hom.app W
          (Scheme.finiteEtaleTateOneGenerator S N Z hS W (φ a) z)) ∧
    GeoCartierScalarUnit φ Z
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (geoCartierConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    GeoCartierScalarUnit φ Z (geoCartierLine R N hR Z) (geoCartierLine S N hS Z) θ ∧
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (cS.mapExactFunctor (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ))
        (zero_add 2) = cR.comp (Ext.mk₀ θ) (add_zero 2)

/-- Cartier-preserving pullback of a simultaneous class family, using the counit mate
for the source and the roots-normalized finite Tate-line comparison for the target.
Source: blueprint sk-lem-geo-cartier, final clause (blueprint: sk-lem-geo-cartier). -/
def GeoCartierBaseChange (ℓ : ℕ) (c : GeoCartierClassFamily.{u} ℓ) : Prop :=
  ∀ (r : ℕ) (hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0),
    ∃ t : Etale.OrdinaryFiniteTwistTransport A (ℓ ^ r) hA,
      ∀ {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
        [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (gD : D' ⟶ D)
        (sq : IsPullback gD i' i g) (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
        (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ r : ℕ) : Γ(Z', ⊤))),
        IsIso (geoCartierExchange A i i' g gD sq.toCommSq) ∧
        (Ext.mk₀ (geoCartierExchange A i i' g gD sq.toCommSq)).comp
            (c r hr A hA i' hI' hZ') (zero_add 2) =
          ((c r hr A hA i hI hZ).mapExactFunctor (upperStar (ModuleCat.{u + 1} A) g)).comp
            (Ext.mk₀ (geoCartierLinePullback A (ℓ ^ r) hA t g hZ).hom) (add_zero 2)

/-- Independence of the killing exponent under the actual roots projection. The map
on roots is pinned by its inclusion into G_m, and the line map by its pure tensors.
Source: blueprint sk-lem-geo-cartier, exponent sentence (blueprint: sk-lem-geo-cartier). -/
def GeoCartierExponentIndependence (ℓ : ℕ) (c : GeoCartierClassFamily.{u} ℓ) : Prop :=
  ∀ (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (_hrs : r ≤ s)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) (hA' : ((ℓ ^ s : ℕ) : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ s : ℕ) : Γ(Z, ⊤))),
    ∃ (q : Z.rootsOfUnitySheaf (ℓ ^ s) ⟶ Z.rootsOfUnitySheaf (ℓ ^ r))
      (e : Scheme.finiteEtaleTateLine Z (ℓ ^ s) A hA' ≅
        Scheme.finiteEtaleTateLine Z (ℓ ^ r) A hA),
      q ≫ kernel.ι ((ℓ ^ r) • 𝟙 Z.gmSheaf) =
        (ℓ ^ s / ℓ ^ r) • kernel.ι ((ℓ ^ s) • 𝟙 Z.gmSheaf) ∧
      (∀ (W : Z.Etaleᵒᵖ) (a : A) (z : (Z.rootsOfUnitySheaf (ℓ ^ s)).obj.obj W),
        e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A (ℓ ^ s) Z hA' W a z) =
          Scheme.finiteEtaleTateOneGenerator A (ℓ ^ r) Z hA W a (q.hom.app W z)) ∧
      (c s hs A hA' i hI hZ').comp
          (Ext.mk₀ ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).map e.hom)) (add_zero 2) =
        c r hr A hA i hI hZ

/-- The canonical Cartier classes in the ordinary pro-etale module derived category,
with the Kummer Chern equation, arbitrary finite-coefficient extension, exponent
independence, and every Cartier-preserving base change. The auxiliary etale class fixes
the canonical construction by its relative torsor boundary; `geoCartierSourceComparison`
is the specified comparison mate, so no arbitrary source isomorphism occurs.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier, statement
and proof paragraphs 1--6; Stacks Project, Tag 03PL (blueprint: sk-lem-geo-cartier).

Proof:
1. Work etale locally, choosing regular equations t_a for D. Inside the direct image
   of G_m from the complement, glue the groups generated by units and all integral
   powers of t_a inverse. Changing t_a to v_ab t_b changes the inverse generator by
   the inverse unit. Etale flatness preserves regularity, hence restriction of units
   to the complement is injective. This constructs M_D without bounding pole order.
2. Send u t_a^(-b) to b on D and to zero off D. Regularity makes b unique at a
   geometric point on D, and every integer lifts locally. The finite-stalk formula
   and exact conservative geometric stalks give 0 -> G_m -> M_D -> i_* Z_D -> 0.
   They also show multiplication by ℓ^r on the quotient is injective, with quotient
   i_* (Z/ℓ^r)_D.
3. Apply lem-sfb-divisible-extension-derived-reduction and the exact Kummer sequence
   lem-amb-kummer-any-base. The resulting R-linear derived boundary has degree two:
   one shift comes from the extension and one from the Kummer kernel. Its relative
   torsor normalization is the existing SupportedKummerBoundary.
4. The lifts of the section one are generated by t_a inverse, hence are the frames
   of the dual Cartier ideal O(D), with the correct sign. By lem-sc-line-bundle-torsor
   and lem-sc-torsor-h1 its extension boundary is that torsor's H1 class. The Kummer
   boundary therefore gives the Chern equation, independent of equations.
5. Extend R to A by lem-geo-cartier-coeff-extension and lem-pur-derived-change-of-rings.
   The supported constant has stalk R or zero; the finite Tate line is flat by
   lem-asd-finite-etale-twist-line. The canonical extension units give precisely the
   unbounded Hom universal properties in GeoCartierScalarCompatibility. Naturality
   and the transitivity normalization give the coefficient equation for every A -> B,
   including nonflat maps. Lem-geo-cartier-exponent-independence computes the modulus
   comparison as roots raised to ℓ^s/ℓ^r. This gives the displayed exponent equation.
6. For Cartier-preserving g, pull back the equations and the extension of step 2.
   The equations remain regular by the Cartier hypothesis. The finite-stalk formula
   identifies the canonical closed exchange with identity on the supported constant
   stalk and zero off the divisor. Naturality of the reduced extension boundary and
   the roots comparison of lem-asd-etale-finite-twist-pullback gives base change.
7. Apply exact ν^*. Closed direct image is etale exact, and the qcqs comparison
   sk-thm-pe-direct-image-comparison identifies its derived image with the pro-etale
   derived image. Its H0 is ordinary closed direct image by left exactness and the
   nonnegative injective resolution theorem. This is geoCartierSourceComparison;
   the comparison respects the units, giving GeoCartierChernEquation.
8. The comparison inverse-image square respects counits. The adjoint of exchange is
   inverse-image commutation followed by the pulled-back counit, which is exactly
   geoCartierExchange. Comparison thus carries the etale equality in step 6 to the
   displayed pro-etale equality. Monoidality and the scalar units commute comparison
   with coefficient extension, preserving the normalized supported and root maps in
   step 5. These are equalities of derived morphisms by functoriality; no geometric
   stalk argument is used to test equality of derived morphisms. -/
theorem exists_geoCartierCycleClass (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ c : GeoCartierClassFamily.{u} ℓ,
      (∀ (r : ℕ) (hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
        (hA : ((ℓ ^ r : ℕ) : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
        (hI : i.ker.IsInvertible) (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))),
        IsIso (geoCartierSourceComparison A i) ∧
        GeoCartierChernEquation A (ℓ ^ r) hA i hI hZ (c r hr A hA i hI hZ) ∧
        ∃ κ : Ext
          ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D))
          (Scheme.finiteEtaleTateLine Z (ℓ ^ r) A hA) 2,
          Etale.SupportedKummerBoundary A (ℓ ^ r) hA i hI hZ κ ∧
          (Ext.mk₀ (geoCartierSourceComparison A i)).comp (c r hr A hA i hI hZ)
              (zero_add 2) = κ.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z)) ∧
      (∀ (r : ℕ) (hr : 0 < r) (A B : Type (u + 1))
        [CommRing A] [CommRing B] [Finite A] [Finite B]
        (hA : ((ℓ ^ r : ℕ) : A) = 0) (hB : ((ℓ ^ r : ℕ) : B) = 0) (φ : A →+* B)
        {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
        (hI : i.ker.IsInvertible) (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))),
        GeoCartierScalarCompatibility φ (ℓ ^ r) hA hB i
          (c r hr A hA i hI hZ) (c r hr B hB i hI hZ)) ∧
      GeoCartierBaseChange ℓ c ∧ GeoCartierExponentIndependence ℓ c := by
  sorry

end AlgebraicGeometry.ProEtale
