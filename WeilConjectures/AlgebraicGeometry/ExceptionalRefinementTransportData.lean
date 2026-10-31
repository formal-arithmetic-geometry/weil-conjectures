/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.AlgebraicGeometry.CompactSupportNormalizedScalarIsomorphisms

/-! # Prescribed transports with their actual common-field scalar action -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalRefinement
open WeilConjectures.ConstructibleExceptionalCoefficients

/-- The inherited shift on finite and integral full inclusions, with the independent
coefficient-closure universe retained. Source: blueprint full finite-Tor categories
(blueprint: lem-sf-exceptional-refinement-mates). -/
instance ringInclusionShift (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
    (RingStage.inclusion.{u, v} l Ω T s).CommShift ℤ :=
  match s with
  | .finite E n =>
    inferInstanceAs (((finiteTorConstructible l E.carrier n n.pos T).ι).CommShift ℤ)
  | .integral E =>
    inferInstanceAs (((finiteTorConstructibleIntegral l E.carrier T).ι).CommShift ℤ)

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The fixed transported adjunctions, with their given realizations at every stage.
The localization and common-field comparisons refer to these same adjunctions.
Source: Zheng Section 5; blueprint retained steps 17--20
(blueprint: lem-sf-exceptional-refinement-mates). -/
structure Transport (c : Compactification f) where
  operation (s : Stage.{max u v} l) : Operation.{u, v} l Ω X Y s
  left (s : RingStage.{max u v} l) :
    LeftRealization.{u, v} l Ω c s (operation (s.stage l))
  leftShift (s : RingStage.{max u v} l) : (left s).hom.CommShift ℤ
  integral (E : FieldStage.{max u v} l) :
    (operation (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier
  integralNormalized (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    (sfIntegralConstructible l E.carrier Y).ι.map ((integral E).hom.app K) =
      (left (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
            ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  rational (E : FieldStage.{max u v} l) :
    (operation (.rational E)).F ≅ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier
  localization (E : FieldStage.{max u v} l) :
    FieldComparison.{u, v} l Ω (operation (.integral E)) (operation (.rational E))
      (rationalization.{u, v} l Ω E X) (rationalization.{u, v} l Ω E Y)
  localizationNormalized (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) :
    (localization E).q.hom.app K ≫
      (rational E).hom.app ((rationalization.{u, v} l Ω E X).obj K) =
        (sfRationalConstructibleLocalization l E.carrier Y).map ((integral E).hom.app K)
  localizationShiftX (E : FieldStage.{max u v} l)
      (K : C.{u, v} l Ω X (.integral E)) (m : ℤ) :
    HEq ((Functor.commShiftIso (rationalization.{u, v} l Ω E X)
        (self := (localization E).shiftX) m).hom.app K)
      (((sfRationalConstructibleLocalization l E.carrier X).commShiftIso m).hom.app
        ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K))
  localizationShiftY (E : FieldStage.{max u v} l)
      (L : C.{u, v} l Ω Y (.integral E)) (m : ℤ) :
    HEq ((Functor.commShiftIso (rationalization.{u, v} l Ω E Y)
        (self := (localization E).shiftY) m).hom.app L)
      (((sfRationalConstructibleLocalization l E.carrier Y).commShiftIso m).hom.app
        ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y).obj L))
  common (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    FieldComparison.{u, v} l Ω (operation (.rational (commonField.{u, v} l Ω E)))
      (operation .closed) (commonInclusion.{u, v} l Ω X E) (commonInclusion.{u, v} l Ω Y E)
  commonNormalized (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω E))) :
    HEq ((common E).q.hom.app K)
      (𝟙 ((commonInclusion.{u, v} l Ω Y E).obj
        ((operation (.rational (commonField.{u, v} l Ω E))).F.obj K)))

  commonShiftX (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    (common E).shiftX =
      GeneralAlgebraicallyClosedCoefficients.inclusionCommShift (l := l) (Ω := Ω) (Y := X) E
  commonShiftY (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    (common E).shiftY =
      GeneralAlgebraicallyClosedCoefficients.inclusionCommShift (l := l) (Ω := Ω) (Y := Y) E

  /-- The actual integral compact-support scalar comparison at common finite fields. -/
  scalarIntegral (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j) :
    sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c (commonField.{u, v} l Ω i).carrier ⋙
        sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
          (commonField.{u, v} l Ω i).carrier (commonField.{u, v} l Ω j).carrier
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y ≅
      sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
          (commonField.{u, v} l Ω i).carrier (commonField.{u, v} l Ω j).carrier
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c (commonField.{u, v} l Ω j).carrier
  scalarIntegralNormalized (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : sfIntegralConstructibleCategory l (commonField.{u, v} l Ω i).carrier X) :
    HEq (((scalarIntegral i j h).hom.app K).hom)
      (sfCompactSupportScalarSystemMap l D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c
        (commonField.{u, v} l Ω i).carrier (commonField.{u, v} l Ω j).carrier
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) K)
  /-- Raw localization of that same scalar comparison. -/
  scalarRational (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j) :
    sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c (commonField.{u, v} l Ω i).carrier ⋙
        rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) Y ≅
      rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X ⋙
        sfCompactSupportFiniteFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c (commonField.{u, v} l Ω j).carrier
  scalarRationalNormalized (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    HEq ((scalarRational i j h).hom.app K)
      ((sfRationalConstructibleLocalization l (commonField.{u, v} l Ω j).carrier Y).map
        ((scalarIntegral i j h).hom.app K.obj))
  /-- Fix the closed functor on transitions between different finite fields.
  STATEMENT-DISPUTED: in the old record, identity-normalized comparisons on each individual
  field do not determine this action. Conjugating by a scalar depending on the pair's
  field fixes every individual-stage restriction and changes cross-field arrows. -/
  commonTransitionNormalized (i j : AlgebraicallyClosedCoefficients.Index l Ω) (h : i ≤ j)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))) :
    (common i).q.hom.app K ≫
        (operation .closed).F.map ((commonTransition.{u, v} l Ω X i j h).inv.app K) ≫
        (common j).q.inv.app
          ((rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X).obj K) ≫
        (commonInclusion.{u, v} l Ω Y j).map
          ((rational (commonField.{u, v} l Ω j)).hom.app
            ((rationalScalar.{u, v} l Ω (commonField.{u, v} l Ω i) (commonField.{u, v} l Ω j)
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j h) X).obj K)) =
      (commonInclusion.{u, v} l Ω Y i).map ((rational (commonField.{u, v} l Ω i)).hom.app K) ≫
        (commonTransition.{u, v} l Ω Y i j h).inv.app
          ((sfCompactSupportFiniteFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
              (commonField.{u, v} l Ω i).carrier).obj K) ≫
        (commonInclusion.{u, v} l Ω Y j).map ((scalarRational i j h).hom.app K)


end WeilConjectures.ExceptionalRefinement
