/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.ProperBaseChangeFourCorners
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.Paper.EtaleOriginWitness
public import Sheaf.Paper.FiniteLevelRingedProEtaleBaseChange

/-!
# The four finite-level proper base-change arrows

Source: blueprint definition 1343; Stacks Project, Tags 07A7, 0B56, 0944 and 09C9
(blueprint: def-weil-pbc-four-arrows).
The positive exponent is n+1. All arrows retain the finite quotient coefficient action.
The horizontal arrows and right exchange are isomorphisms. No invertibility of the
left exchange and no commutativity of the resulting square are asserted here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

variable {A : Type (t + 1)} [CommRing A]

/-- The finite quotient, with no universe change of the recorded adic datum.
Source: definition 1343 (blueprint: def-weil-pbc-four-arrows). -/
abbrev fourArrowQuotient (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :=
  A ⧸ d.ideal ^ (n + 1)

/-- Finiteness at each positive level; no common bound on origin complexes is imposed.
Source: definition 1343 (blueprint: def-weil-pbc-four-arrows). -/
instance fourArrowQuotient_finite (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    Finite (fourArrowQuotient d n) := d.quotientFinite n

/-- Each finite quotient is discrete.
Source: definition 1343 (blueprint: def-weil-pbc-four-arrows). -/
instance fourArrowQuotient_topology (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    TopologicalSpace (fourArrowQuotient d n) := ⊥

/-- Discreteness of the specified finite coefficient topology.
Source: definition 1343 (blueprint: def-weil-pbc-four-arrows). -/
instance fourArrowQuotient_discrete (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    DiscreteTopology (fourArrowQuotient d n) := ⟨rfl⟩

/-- Canonical finite-origin coefficient transport from the repaired finite-level theorem.
Source: definition 1343 (blueprint: def-weil-pbc-four-arrows). -/
abbrev fourArrowOriginTransport (T : Scheme.{t}) (d : ProEtaleAdicCoefficientDatum A)
    (n : ℕ) :=
  finiteOriginTransport (fourArrowQuotient d n) T

/-- The canonical comparison chi, oriented from finite pullback of reduction to reduction
of ambient pullback. Its inverse is the four-corner comparison delta.
Source: definition 1343, comparison paragraph (blueprint: def-weil-pbc-four-arrows). -/
def fourArrowReductionPullback {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :=
  (fourCornerReductionPullback f d n).symm

/-- Finite-coefficient projection is exactly the specified counit adjunct.
Source: definition 1343, formula for p; Stacks 0B56
(blueprint: def-weil-pbc-four-arrows). -/
def fourArrowProjection {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A)
    (H : fourCornerDerived U (adicDatumRing U d)) (n : ℕ) :
    (adicDatumReduction V d n).obj ((fourCornerPushforward f d).obj H) ⟶
      (fourCornerFinitePushforward f d n).obj ((adicDatumReduction U d n).obj H) :=
  (fourCornerFiniteDerivedAdjunction f d n).homEquiv _ _
      ((fourArrowReductionPullback f d n).hom.app ((fourCornerPushforward f d).obj H) ≫
        (adicDatumReduction U d n).map
          ((fourCornerDerivedAdjunction f d).counit.app H))

/-- Perfect quotient coefficients make this specified projection adjunct invertible.
Source: definition 1343, projection paragraph; Stacks 0944
(blueprint: def-weil-pbc-four-arrows).
Proof: the change-of-ring adjunction comparison identifies the restricted adjunct with
the ambient projection map proEtaleProjectionFormulaMate. The finite perfect
A-resolution of P_n gives a finite-projective coefficient resolution over A_T.
Apply lemma-weil-pbc-perfect-projection-formula to this perfect coefficient object.
Restriction reflects isomorphisms by lem-weil-pbc-ring-sheaf-change-adjunction, so the
finite-coefficient adjunct is invertible too. Neither properness nor completeness of H
is used in this argument. -/
theorem fourArrowProjection_isIso {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A)
    (H : fourCornerDerived U (adicDatumRing U d)) (n : ℕ) :
    IsIso (fourArrowProjection f d H n) := by
  sorry

/-- The isomorphism whose forward map is precisely p, not a separately chosen map.
Source: definition 1343 (blueprint: def-weil-pbc-four-arrows). -/
def fourArrowProjectionIso {U V : Scheme.{t}} (f : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A)
    (H : fourCornerDerived U (adicDatumRing U d)) (n : ℕ) :=
  @asIso _ _ _ _ (fourArrowProjection f d H n) (fourArrowProjection_isIso f d H n)

variable {X' X Y' Y : Scheme.{t}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The specified completed coefficients agree around the cartesian square.
Source: definition 1343, compatible coefficient identifications; Stacks 07A7
(blueprint: def-weil-pbc-four-arrows).
Proof: apply fourCornerCoefficientCoherence to both composites; transport across the
commutativity of the scheme square. The two canonical inverse-image identifications
are the same, so the resulting dependent isomorphisms agree. -/
theorem fourArrowIntegralCoefficients_comm (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) :
    HEq (proEtaleRingCompositeCoefficients g' f (adicDatumRing Y d)
      (adicDatumRing X d) (adicDatumRing X' d)
      (fourCornerCoefficientIso f d) (fourCornerCoefficientIso g' d))
      (proEtaleRingCompositeCoefficients f' g (adicDatumRing Y d)
        (adicDatumRing Y' d) (adicDatumRing X' d)
        (fourCornerCoefficientIso g d) (fourCornerCoefficientIso f' d)) := by
  have hcomp {U V W : Scheme.{t}} (h : U ⟶ V) (k : V ⟶ W) :
      proEtaleRingCompositeCoefficients h k (adicDatumRing W d)
        (adicDatumRing V d) (adicDatumRing U d)
        (fourCornerCoefficientIso k d) (fourCornerCoefficientIso h d) =
      fourCornerCoefficientIso (h ≫ k) d := by
    apply Iso.ext
    simpa only [proEtaleRingCompositeCoefficients, Iso.trans_hom,
      NatTrans.comp_app, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      ((fourCornerCoefficientCoherence d).2.2.1 U V W h k).symm
  have he : HEq (fourCornerCoefficientIso (g' ≫ f) d)
      (fourCornerCoefficientIso (f' ≫ g) d) := by
    generalize hleft : g' ≫ f = left
    generalize hright : f' ≫ g = right
    have hh : left = right := hleft.symm.trans (sq.toCommSq.w.trans hright)
    cases hh
    rfl
  exact (heq_of_eq (hcomp g' f)).trans (he.trans (heq_of_eq (hcomp f' g)).symm)

/-- The same coefficient coherence at every finite quotient level.
Source: definition 1343; Stacks 07A7 (blueprint: def-weil-pbc-four-arrows).
Proof: the finite composition clause of fourCornerCoefficientCoherence gives the
canonical identification for either composite. Transport through sq.toCommSq.w
identifies them, exactly as for the completed coefficient ring. -/
theorem fourArrowFiniteCoefficients_comm (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    HEq (proEtaleRingCompositeCoefficients g' f
      ((adicLisseRingSystem Y d.ideal).obj (op n))
      ((adicLisseRingSystem X d.ideal).obj (op n))
      ((adicLisseRingSystem X' d.ideal).obj (op n))
      (fourCornerFiniteIso f d n) (fourCornerFiniteIso g' d n))
      (proEtaleRingCompositeCoefficients f' g
        ((adicLisseRingSystem Y d.ideal).obj (op n))
        ((adicLisseRingSystem Y' d.ideal).obj (op n))
        ((adicLisseRingSystem X' d.ideal).obj (op n))
        (fourCornerFiniteIso g d n) (fourCornerFiniteIso f' d n)) := by
  have hcomp {U V W : Scheme.{t}} (h : U ⟶ V) (k : V ⟶ W) :
      proEtaleRingCompositeCoefficients h k
        ((adicLisseRingSystem W d.ideal).obj (op n))
        ((adicLisseRingSystem V d.ideal).obj (op n))
        ((adicLisseRingSystem U d.ideal).obj (op n))
        (fourCornerFiniteIso k d n) (fourCornerFiniteIso h d n) =
      fourCornerFiniteIso (h ≫ k) d n := by
    apply Iso.ext
    simpa only [proEtaleRingCompositeCoefficients, Iso.trans_hom,
      NatTrans.comp_app, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      ((fourCornerCoefficientCoherence d).2.2.2 U V W h k n).symm
  have he : HEq (fourCornerFiniteIso (g' ≫ f) d n)
      (fourCornerFiniteIso (f' ≫ g) d n) := by
    generalize hleft : g' ≫ f = left
    generalize hright : f' ≫ g = right
    have hh : left = right := hleft.symm.trans (sq.toCommSq.w.trans hright)
    cases hh
    rfl
  exact (heq_of_eq (hcomp g' f)).trans (he.trans (heq_of_eq (hcomp f' g)).symm)

/-- The specified geometric comparison with the fixed four-corner functor interface.
Its value is the existing ambient comparison; only its category instances are explicit.
Source: Stacks 0D6D and 07A7 (blueprint: def-weil-pbc-four-arrows). -/
def fourArrowIntegralPullbackComparison (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) :
    fourCornerPullback g d ⋙ fourCornerPullback f' d ≅
      fourCornerPullback f d ⋙ fourCornerPullback g' d :=
  proEtaleAmbientRingedPullbackComparison sq
    (adicDatumRing X d)
    (adicDatumRing Y d)
    (adicDatumRing X' d)
    (adicDatumRing Y' d)
    (fourCornerCoefficientIso f d) (fourCornerCoefficientIso g d)
    (fourCornerCoefficientIso g' d) (fourCornerCoefficientIso f' d)
    (fourArrowIntegralCoefficients_comm sq d)

/-- The specified geometric comparison with the fixed four-corner functor interface.
Its value is the existing ambient comparison; only its category instances are explicit.
Source: Stacks 0D6D and 07A7 (blueprint: def-weil-pbc-four-arrows). -/
def fourArrowIntegralExchangeNat (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) :
    fourCornerPushforward f d ⋙ fourCornerPullback g d ⟶
      fourCornerPullback g' d ⋙ fourCornerPushforward f' d :=
  proEtaleAmbientRingedExchange sq
    (adicDatumRing X d)
    (adicDatumRing Y d)
    (adicDatumRing X' d)
    (adicDatumRing Y' d)
    (fourCornerCoefficientIso f d) (fourCornerCoefficientIso g d)
    (fourCornerCoefficientIso g' d) (fourCornerCoefficientIso f' d)
    (fourArrowIntegralCoefficients_comm sq d)

/-- The specified geometric comparison with the fixed four-corner functor interface.
Its value is the existing ambient comparison; only its category instances are explicit.
Source: Stacks 0D6D and 07A7 (blueprint: def-weil-pbc-four-arrows). -/
def fourArrowFinitePullbackComparison (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    fourCornerFinitePullback g d n ⋙ fourCornerFinitePullback f' d n ≅
      fourCornerFinitePullback f d n ⋙ fourCornerFinitePullback g' d n :=
  proEtaleAmbientRingedPullbackComparison sq
    ((adicLisseRingSystem X d.ideal).obj (op n))
    ((adicLisseRingSystem Y d.ideal).obj (op n))
    ((adicLisseRingSystem X' d.ideal).obj (op n))
    ((adicLisseRingSystem Y' d.ideal).obj (op n))
    (fourCornerFiniteIso f d n) (fourCornerFiniteIso g d n)
    (fourCornerFiniteIso g' d n) (fourCornerFiniteIso f' d n)
    (fourArrowFiniteCoefficients_comm sq d n)

/-- The specified geometric comparison with the fixed four-corner functor interface.
Its value is the existing ambient comparison; only its category instances are explicit.
Source: Stacks 0D6D and 07A7 (blueprint: def-weil-pbc-four-arrows). -/
def fourArrowFiniteExchangeNat (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    fourCornerFinitePushforward f d n ⋙ fourCornerFinitePullback g d n ⟶
      fourCornerFinitePullback g' d n ⋙ fourCornerFinitePushforward f' d n :=
  proEtaleAmbientRingedExchange sq
    ((adicLisseRingSystem X d.ideal).obj (op n))
    ((adicLisseRingSystem Y d.ideal).obj (op n))
    ((adicLisseRingSystem X' d.ideal).obj (op n))
    ((adicLisseRingSystem Y' d.ideal).obj (op n))
    (fourCornerFiniteIso f d n) (fourCornerFiniteIso g d n)
    (fourCornerFiniteIso g' d n) (fourCornerFiniteIso f' d n)
    (fourArrowFiniteCoefficients_comm sq d n)

/-- The actual finite ringed exchange, defined independently of any origin witness.
Source: definition 1343, final displayed adjunct; Stacks 07A7
(blueprint: def-weil-pbc-four-arrows). -/
def fourArrowFiniteExchange (sq : ChosenCartesianSquare g' f' f g)
    (d : ProEtaleAdicCoefficientDatum A)
    (K : fourCornerDerived X (adicDatumRing X d)) (n : ℕ) :
    (fourCornerFinitePullback g d n).obj
        ((fourCornerFinitePushforward f d n).obj
            ((adicDatumReduction X d n).obj K)) ⟶
      (fourCornerFinitePushforward f' d n).obj
          ((fourCornerFinitePullback g' d n).obj
              ((adicDatumReduction X d n).obj K)) :=
  (fourArrowFiniteExchangeNat sq d n).app ((adicDatumReduction X d n).obj K)

/-- Proper base change certifies this canonical finite exchange is invertible.
The supplied bounded-below origin is transported along the normalized coefficient
isomorphism. No compatibility with other levels is required.
Source: definition 1343, finite exchange paragraph; Stacks 09C9
(blueprint: def-weil-pbc-four-arrows).
Proof: exact identified-coefficient inverse image agrees with the fixed-ring inverse
image under the constants-to-functions coefficient equivalence. Its normalized unit
and counit identify the ringed exchange mate with the fixed-ring exchange mate.
The witness w supplies the etale object L and its alpha isomorphism; transport via e
identifies its pro-etale image with K_n. Apply thm-weil-pbc-finite-level-proetale
(finiteConstantRingedExchange_isIso) to the finite ring P_n and proper f.
The comparison equivalence reflects isomorphisms, giving the claimed IsIso.
The forward map has no witness argument, so replacing a witness leaves it unchanged. -/
theorem fourArrowFiniteExchange_isIso [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g) (d : ProEtaleAdicCoefficientDatum A)
    (K : fourCornerDerived X (adicDatumRing X d)) (n : ℕ)
    (W : ProEtale.FiniteCoefficientDerivedCategoryPlus X (fourArrowQuotient d n))
    (w : ProEtale.EtaleOriginWitness X (fourArrowQuotient d n) W)
    (e : (fourArrowOriginTransport X d n).obj W.obj ≅ (adicDatumReduction X d n).obj K) :
    IsIso (fourArrowFiniteExchange sq d K n) := by
  sorry

/-- The four arrows on exactly the objects of properBaseChangeFourCorners.
The family W presents each reduction in D+; w retains the actual etale-origin data,
and e only transports between the two canonically identified coefficient presentations.
No uniform lower bound or compatibility between different w n is required.
Source: definition 1343, four displayed formulas; Stacks 0B56, 07A7, 0944, 09C9
(blueprint: def-weil-pbc-four-arrows). -/
def properBaseChangeFourArrows
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (d : ProEtaleAdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : fourCornerDerived X (adicDatumRing X d))
    (C : CochainComplex (proEtaleRingModules X (adicDatumRing X d)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (hK : IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC)
    (W : ∀ n : ℕ, ProEtale.FiniteCoefficientDerivedCategoryPlus X (fourArrowQuotient d n))
    (w : ∀ n : ℕ, ProEtale.EtaleOriginWitness X (fourArrowQuotient d n) (W n))
    (e : ∀ n : ℕ, (fourArrowOriginTransport X d n).obj (W n).obj ≅
      (adicDatumReduction X d n).obj K) (n : ℕ) :
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).1 ≅
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.1) ×
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.1 ≅
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.2) ×
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).1 ⟶
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.1) ×
    ((properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.1 ≅
      (properBaseChangeFourCorners g' f' f g sq d r a ha K C eC hK n).2.2.2) :=
  ((fourCornerFinitePullback g d n).mapIso (fourArrowProjectionIso f d K n),
    fourArrowProjectionIso f' d ((fourCornerPullback g' d).obj K) n ≪≫
      (fourCornerFinitePushforward f' d n).mapIso (fourCornerEReductionIso g' d K n),
    (fourArrowReductionPullback g d n).hom.app ((fourCornerPushforward f d).obj K) ≫
      (adicDatumReduction Y' d n).map
        ((fourArrowIntegralExchangeNat sq d).app K),
    @asIso _ _ _ _ (fourArrowFiniteExchange sq d K n)
      (fourArrowFiniteExchange_isIso sq d K n (W n) (w n) (e n)))

end AlgebraicGeometry.Scheme
