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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange


/-!
# The cycle class of an effective Cartier divisor

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-cartier,
statement and proof paragraphs 1--6; Stacks Project, Tag 03PL
(blueprint: def-sfb-geo-cartier-interface).

We use the fixed-scalar sheaf presentation of ordinary pro-etale modules, canonically
realized by `finiteCoefficientRealization` over the coefficient ring sheaf of
`def-weil-pbc-proetale-modules`. `Ext.homEquiv` identifies every degree-two Ext class
below with the displayed morphism from the degree-zero supported constant object to
its finite Tate line shifted by two. No condensed or completed coefficient category occurs.
The auxiliary definitions only spell out this class and its normalization diagrams.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Cache the existing smallness proof used by integral pro-etale Ext classes.
Source: the existing Grothendieck-abelian sheaf category and its Ext instance
(blueprint: def-sfb-geo-cartier-interface).
Proof: apply the library instance for Ext in this sheaf category. This names only
its smallness proof, so it does not alter the Ext objects or their operations. -/
instance (priority := 10000) geoCartierIntegralExt (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) := by
  infer_instance

/-- Cache finite-coefficient pro-etale Ext smallness, without changing any Ext data.
Source: the existing Grothendieck-abelian sheaf Ext instance
(blueprint: def-sfb-geo-cartier-interface). The proof only specializes that instance. -/
instance (priority := 10000) geoCartierModuleExt
    (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) := by
  infer_instance

/-- The ordinary pro-etale constant module used in the Cartier class.
Source: blueprint sk-lem-geo-cartier, statement (blueprint: def-sfb-geo-cartier-interface). -/
def geoCartierConstant (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) :=
  (constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- The finite Tate line is exactly comparison inverse image of the etale roots tensor.
Source: blueprint sk-lem-geo-cartier, displayed definition of Λ(1)
(blueprint: def-sfb-geo-cartier-interface). -/
def geoCartierLine (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (Z : Scheme.{u}) : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
    (Scheme.finiteEtaleTateLine Z N A hA)

/-- The supported cycle class, represented through the canonical degree-two Ext/Hom
bijection. Its source uses ordinary closed direct image, not an arbitrary support object.
Source: blueprint sk-lem-geo-cartier, displayed c_D (blueprint: def-sfb-geo-cartier-interface). -/
abbrev GeoCartierClass (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) :=
  Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D))
    (geoCartierLine A N hA Z) 2

/-- A simultaneous family allows coefficient, exponent and geometric compatibility
between its actual members. Invertibility of ℓ^r equals invertibility of ℓ for r > 0.
Source: blueprint sk-lem-geo-cartier, statement (blueprint: def-sfb-geo-cartier-interface). -/
def GeoCartierClassFamily (ℓ : ℕ) : Type (u + 2) :=
  ∀ (r : ℕ) (_hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))),
    GeoCartierClass A (ℓ ^ r) hA i

/-- The comparison on the ordinary supported constant, with its canonical mate and
constant-sheaf identification. Invertibility is asserted in the main statement.
Source: blueprint sk-lem-geo-cartier, proof paragraph 1
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierSourceComparison (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D) :=
  (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app
      (Etale.ordinaryFiniteConstant A D) ≫
    (lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom

/-- The direct image of the constant-sheaf comparison, typed with the Cartier constant as
target, is invertible; instance search cannot see through geoCartierConstant itself.
Source: blueprint sk-lem-geo-cartier, proof paragraph 1
(blueprint: def-sfb-geo-cartier-interface).
Proof: after unfolding the constant, it is the image of an isomorphism under a functor. -/
instance geoCartierSourceConstant_isIso (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    IsIso ((lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom :
        _ ⟶ (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) := by
  unfold geoCartierConstant
  infer_instance

/-- The inverse-image commutation isomorphism for the specified square.
Source: blueprint sk-lem-geo-cartier, opening comparison and paragraph 6
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierPullbackSquare (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    upperStar (ModuleCat.{u + 1} A) g ⋙ upperStar (ModuleCat.{u + 1} A) i' ≅
      upperStar (ModuleCat.{u + 1} A) i ⋙ upperStar (ModuleCat.{u + 1} A) gD :=
  (upperStarComp (ModuleCat.{u + 1} A) i' g).symm ≪≫
    eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) sq.w.symm) ≪≫
    upperStarComp (ModuleCat.{u + 1} A) gD i

/-- Canonical pro-etale closed exchange, as the adjoint of inverse-image commutation
followed by the counit and the pullback of constants. This formula works for arbitrary
base morphisms; no weakly-etale or flatness restriction is imposed.
Source: blueprint sk-lem-geo-cartier, proof paragraph 6
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierExchange (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    (upperStar (ModuleCat.{u + 1} A) g).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i').obj (geoCartierConstant A D') :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i').homEquiv _ _
    ((geoCartierPullbackSquare A i i' g gD sq).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) gD).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app
            (geoCartierConstant A D)) ≫
        Scheme.proEtaleConstantInverseImageMap gD (ModuleCat.{u + 1} A) (ModuleCat.of A A))

/-- Pull back the finite Tate line through the canonical comparison square and the
existing roots-normalized etale transport.
Source: blueprint sk-lem-geo-cartier, base-change clause
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
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
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
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
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (Z : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))
    (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj G) : Prop :=
  Sheaf.IsDerivedBaseChange
    ((DerivedCategory.singleFunctor _ 0).map η ≫
      ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).mapDerivedCategorySingleFunctor
        0).inv.app G)


/-- Coefficient compatibility with the canonical supported-constant and Tate-line
units. Normalization is on constants and on pure root tensors through the comparison
adjunction unit. These generate after sheafification, so the comparisons are fixed.
Source: blueprint sk-lem-geo-cartier, coefficient clause
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
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
Source: blueprint sk-lem-geo-cartier, final clause (blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
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
Source: blueprint sk-lem-geo-cartier, exponent sentence
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
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

end AlgebraicGeometry.ProEtale
