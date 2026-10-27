# WeilConjectures.ExceptionalRefinement.Transport and refinement data extraction

## Reason

The old Transport fixes only within-field common-inclusion comparisons. It does not fix the
closed left functor on cross-field transition arrows, although the theorem requires exactly the
common-field image of a prescribed rational refinement. The old statement is disputed for this
specific omission. Conjugate one closed left functor by a nonzero scalar depending on the pair's
field: its action within any one field, its identity q components and its adjunction/shift
properties survive, while cross-field arrows change. The claimed objectwise normalized
refinement then need not be natural.

Retain the actual integral scalar comparison normalized by sfCompactSupportScalarSystemMap,
its raw rational localization, and the closed action on every transition through these maps.
These are properties of the prescribed transport in the node's mathematical statement,
not refinement maps or a refinement existence hypothesis. They are the fixed-map counterpart
of the existing CoefficientConstructionNormalization.commonTransitionNatural and the
common_morphism_normalized representative action. The scalar comparisons exist by the
published sfCompactSupportNormalizedScalarIsomorphisms construction.

Move the existing data into ExceptionalRefinementTransportData, ExceptionalRefinementMatesData
and ExceptionalRefinementSystemData so the two genuinely smaller proof obligations can use
their types without importing the theorem they prove. The separation follows profiling of
generated record checks, after explicit universes and inherited instances remove broad
definitional searches. Every existing public
name remains publicly re-exported by ExceptionalRefinementMates. The theorem signature is
literally unchanged. Transport alone gains five fields (two scalar isomorphisms, their fixed-map
normalizations, and the closed transition equation). No target uses Transport as a definition
in its signature; the five Challenge statements are untouched.

## Old

The original data were declared directly by Sheaf.Paper.ExceptionalRefinementMates:

```lean
/-- The inherited shift on finite and integral full inclusions, with the independent
coefficient-closure universe retained. Source: blueprint full finite-Tor categories
(blueprint: lem-sf-exceptional-refinement-mates). -/
instance ringInclusionShift (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T : Scheme.{max u v}) (s : RingStage.{max u v} l) :
    (RingStage.inclusion.{u, v} l Ω T s).CommShift ℤ :=
  match s with
  | .finite _ _ => inferInstance
  | .integral _ => inferInstance

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

variable {c d : Compactification f}

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The refinement maps on exactly the given operations. The two transpose formulas fix
both directions of the right isomorphism; the ring predicate fixes the open-unit inverse.
The rational and closed formulas include the comparisons on both sides, so they also
apply before identifying the prescribed representatives by their identity normalizations.
Source: blueprint retained steps 20--21
(blueprint: lem-sf-exceptional-refinement-mates). -/
structure Mates (A : Transport.{u, v} l Ω D hl c) (B : Transport.{u, v} l Ω D hl d)
    (r : c.Refinement d) where
  comparison (s : Stage.{max u v} l) :
    RefinementComparison.{u, v} l Ω (A.operation s) (B.operation s)
  normalized (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (A.left s) (B.left s) (comparison (s.stage l))
  transpose (s : Stage.{max u v} l) (L : C.{u, v} l Ω Y s) :
    (comparison s).right.hom.app L =
      (A.operation s).adjunction.homEquiv _ _
        ((comparison s).left.hom.app ((B.operation s).G.obj L) ≫
          (B.operation s).adjunction.counit.app L)
  inverseTranspose (s : Stage.{max u v} l) (L : C.{u, v} l Ω Y s) :
    (comparison s).right.inv.app L =
      (B.operation s).adjunction.homEquiv _ _
        ((comparison s).left.inv.app ((A.operation s).G.obj L) ≫
          (A.operation s).adjunction.counit.app L)
  rationalLeft (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    (A.localization E).q.inv.app K ≫
        (rationalization.{u, v} l Ω E Y).map ((comparison (.integral E)).left.hom.app K) ≫
        (B.localization E).q.hom.app K =
      (comparison (.rational E)).left.hom.app ((rationalization.{u, v} l Ω E X).obj K)
  rationalRight (E : FieldStage.{max u v} l) (L : C.{u, v} l Ω Y (.integral E)) :
    (B.localization E).b.inv.app L ≫
        (rationalization.{u, v} l Ω E X).map ((comparison (.integral E)).right.hom.app L) ≫
        (A.localization E).b.hom.app L =
      (comparison (.rational E)).right.hom.app ((rationalization.{u, v} l Ω E Y).obj L)
  commonLeft (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω E))) :
    (A.common E).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y E).map
          ((comparison (.rational (commonField.{u, v} l Ω E))).left.hom.app K) ≫
        (B.common E).q.hom.app K =
      (comparison .closed).left.hom.app ((commonInclusion.{u, v} l Ω X E).obj K)
  commonRight (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (L : C.{u, v} l Ω Y (.rational (commonField.{u, v} l Ω E))) :
    (B.common E).b.inv.app L ≫
        (commonInclusion.{u, v} l Ω X E).map
          ((comparison (.rational (commonField.{u, v} l Ω E))).right.hom.app L) ≫
        (A.common E).b.hom.app L =
      (comparison .closed).right.hom.app ((commonInclusion.{u, v} l Ω Y E).obj L)

/-- The actual reconstructed input, retaining every transition before total limit.
Source: Zheng Construction 5.15 (blueprint: lem-sf-exceptional-refinement-mates). -/
abbrev reducedInput (E : FieldStage.{max u v} l) :=
  RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙ (calculus l E.carrier X).reduction

/-- The normalized reduction shift is the adjunction conjugate of the Roos limit shift.
Source: blueprint termwise/Roos shifts (blueprint: lem-sf-exceptional-refinement-mates). -/
instance reducedInputShift (E : FieldStage.{max u v} l) :
    (reducedInput.{u, v} l Ω (X := X) E).CommShift ℤ :=
  letI := reductionShift l E.carrier X
  inferInstanceAs ((RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
    (calculus l E.carrier X).reduction).CommShift ℤ)

/-- The whole-system compact-support functor on normalized integral inputs.
Source: Zheng Construction 5.15 (blueprint: lem-sf-exceptional-refinement-mates). -/
abbrev systemSupport (E : FieldStage.{max u v} l) (o : Operations l E.carrier)
    (a : Compactification f) :=
  reducedInput.{u, v} l Ω (X := X) E ⋙ SystemProjectionFormula.support l E.carrier o a

/-- The support shift is termwise open shift followed by its proper adjoint shift.
Source: blueprint termwise shifts (blueprint: lem-sf-exceptional-refinement-mates). -/
instance systemSupportShift (E : FieldStage.{max u v} l) (o : Operations l E.carrier)
    (a : Compactification f) : (systemSupport.{u, v} l Ω E o a).CommShift ℤ :=
  letI := systemOpenShift l E.carrier o a.i
  letI := systemPushShift l E.carrier o a.g
  inferInstanceAs ((reducedInput.{u, v} l Ω (X := X) E ⋙
    (Operations.shriek l E.carrier o a.i ⋙ Operations.push l E.carrier o a.g)).CommShift ℤ)

/-- Realization of a support expression by its actual proper/open comparisons and the
inverse reconstruction unit. The inverse is evaluated only on the derived-complete input.
Source: blueprint retained step 20 (blueprint: lem-sf-exceptional-refinement-mates). -/
def realizationComponent (E : FieldStage.{max u v} l) (o : Operations l E.carrier)
    (R : Realizations l E.carrier D o) (a : Compactification f)
    (K : C.{u, v} l Ω X (.integral E))
    (hK : Good l E.carrier X ((reducedInput.{u, v} l Ω (X := X) E).obj K))
    (hJ : Good l E.carrier a.Z ((Operations.shriek l E.carrier o a.i).obj
      ((reducedInput.{u, v} l Ω (X := X) E).obj K))) :
    (coefficientSequenceLimit l E.carrier Y).obj ((systemSupport.{u, v} l Ω E o a).obj K) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) a).obj K.obj :=
  (R.realizationModel.push l E.carrier a.g).hom.app
      ((Operations.shriek l E.carrier o a.i).obj
        ((reducedInput.{u, v} l Ω (X := X) E).obj K)) ≫
    (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) a.g).map
      ((R.openRealization a.i (a.quasiCompact_openImmersion inferInstance)
        ((reducedInput.{u, v} l Ω (X := X) E).obj K) hK hJ).hom) ≫
    (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) a).map
      (SystemProjectionFormula.inverseOnDomain ((calculus l E.carrier X).adjunction.unit.app K.obj))

/-- The strict-system inverse refinement and its total-limit realization are kept together.
`word` is an equality in the derived category of systems, before any evaluation or limit.
`realizationNormalized` fixes all endpoint identifications by the actual primitive maps.
Source: Zheng 5.13--5.15; blueprint retained step 20
(blueprint: lem-sf-exceptional-refinement-mates). -/
structure SystemRealization (A : Transport.{u, v} l Ω D hl c)
    (B : Transport.{u, v} l Ω D hl d) (r : c.Refinement d)
    (P : Mates.{u, v} l Ω D hl A B r) (E : FieldStage.{max u v} l)
    (o : Operations l E.carrier) (R : Realizations l E.carrier D o) where
  alpha : systemSupport.{u, v} l Ω E o c ≅ systemSupport.{u, v} l Ω E o d
  word (K : C.{u, v} l Ω X (.integral E)) :
    alpha.inv.app K = (SystemProjectionFormula.refinement l E.carrier o R.compositors
      R.openComparisons R.canonicalBridge R.properOpen r).app
        ((reducedInput.{u, v} l Ω (X := X) E).obj K)
  inputGood (K : C.{u, v} l Ω X (.integral E)) :
    Good l E.carrier X ((reducedInput.{u, v} l Ω (X := X) E).obj K)
  openGood (a : Compactification f) (K : C.{u, v} l Ω X (.integral E)) :
    Good l E.carrier a.Z ((Operations.shriek l E.carrier o a.i).obj
      ((reducedInput.{u, v} l Ω (X := X) E).obj K))
  realization (a : Compactification f) :
    systemSupport.{u, v} l Ω E o a ⋙ coefficientSequenceLimit l E.carrier Y ≅
      RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) a
  realizationNormalized (a : Compactification f) (K : C.{u, v} l Ω X (.integral E)) :
    (realization a).hom.app K =
      realizationComponent.{u, v} l Ω D E o R a K (inputGood K) (openGood a K)
  integralMap (K : C.{u, v} l Ω X (.integral E)) :
    (coefficientSequenceLimit l E.carrier Y).map (alpha.hom.app K) ≫
        (realization d).hom.app K =
      (realization c).hom.app K ≫ (A.left (.integral E)).inv.app K ≫
        (RingStage.inclusion.{u, v} l Ω Y (.integral E)).map
          ((P.comparison (.integral E)).left.hom.app K) ≫
        (B.left (.integral E)).hom.app K
  shift : alpha.hom.CommShift ℤ
  realizationShift (a : Compactification f) (K : C.{u, v} l Ω X (.integral E)) (m : ℤ) :
    (realization a).hom.app (K⟦m⟧) ≫
        ((RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
          PurCompactSupport.image
            (PurCompactSupport.completed l E.carrier) a).commShiftIso m).hom.app K =
      (coefficientSequenceLimit l E.carrier Y).map
          (((systemSupport.{u, v} l Ω E o a).commShiftIso m).hom.app K) ≫
        ((Functor.commShiftIso (coefficientSequenceLimit l E.carrier Y)
          (self := limitShift l E.carrier Y) m).hom.app
            ((systemSupport.{u, v} l Ω E o a).obj K)) ≫
        ((realization a).hom.app K)⟦m⟧'

```

## New

The complete data modules below preserve the public names and specify the repair explicitly.

### lean/Sheaf/Paper/ExceptionalRefinementTransportData.lean

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q24 and Z6
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms

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
```

### lean/Sheaf/Paper/ExceptionalRefinementMatesData.lean

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q24 and Z6
-/
module

public import Sheaf.Paper.ExceptionalRefinementTransportData
public import Sheaf.Paper.ConstructibleExceptionalRefinementMate

/-! # Left refinements and their complete adjunction mate records -/

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

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

variable {c d : Compactification f}

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The refinement maps on exactly the given operations. The two transpose formulas fix
both directions of the right isomorphism; the ring predicate fixes the open-unit inverse.
The rational and closed formulas include the comparisons on both sides, so they also
apply before identifying the prescribed representatives by their identity normalizations.
Source: blueprint retained steps 20--21
(blueprint: lem-sf-exceptional-refinement-mates). -/
structure Mates (A : Transport.{u, v} l Ω D hl c) (B : Transport.{u, v} l Ω D hl d)
    (r : c.Refinement d) where
  comparison (s : Stage.{max u v} l) :
    RefinementComparison.{u, v} l Ω (A.operation s) (B.operation s)
  normalized (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (A.left s) (B.left s) (comparison (s.stage l))
  transpose (s : Stage.{max u v} l) (L : C.{u, v} l Ω Y s) :
    (comparison s).right.hom.app L =
      (A.operation s).adjunction.homEquiv _ _
        ((comparison s).left.hom.app ((B.operation s).G.obj L) ≫
          (B.operation s).adjunction.counit.app L)
  inverseTranspose (s : Stage.{max u v} l) (L : C.{u, v} l Ω Y s) :
    (comparison s).right.inv.app L =
      (B.operation s).adjunction.homEquiv _ _
        ((comparison s).left.inv.app ((A.operation s).G.obj L) ≫
          (A.operation s).adjunction.counit.app L)
  rationalLeft (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    (A.localization E).q.inv.app K ≫
        (rationalization.{u, v} l Ω E Y).map ((comparison (.integral E)).left.hom.app K) ≫
        (B.localization E).q.hom.app K =
      (comparison (.rational E)).left.hom.app ((rationalization.{u, v} l Ω E X).obj K)
  rationalRight (E : FieldStage.{max u v} l) (L : C.{u, v} l Ω Y (.integral E)) :
    (B.localization E).b.inv.app L ≫
        (rationalization.{u, v} l Ω E X).map ((comparison (.integral E)).right.hom.app L) ≫
        (A.localization E).b.hom.app L =
      (comparison (.rational E)).right.hom.app ((rationalization.{u, v} l Ω E Y).obj L)
  commonLeft (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω E))) :
    (A.common E).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y E).map
          ((comparison (.rational (commonField.{u, v} l Ω E))).left.hom.app K) ≫
        (B.common E).q.hom.app K =
      (comparison .closed).left.hom.app ((commonInclusion.{u, v} l Ω X E).obj K)
  commonRight (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (L : C.{u, v} l Ω Y (.rational (commonField.{u, v} l Ω E))) :
    (B.common E).b.inv.app L ≫
        (commonInclusion.{u, v} l Ω X E).map
          ((comparison (.rational (commonField.{u, v} l Ω E))).right.hom.app L) ≫
        (A.common E).b.hom.app L =
      (comparison .closed).right.hom.app ((commonInclusion.{u, v} l Ω Y E).obj L)

/-- The geometric left comparisons, without any right-mate or system-realization data.
The ring comparisons use the proper/open unit normalization; the other two equations
retain the prescribed coefficient comparisons. Source: retained refinement steps 1, 3,
4 and 6--8 (blueprint: def-sf-exceptional-refinement-left-data). -/
structure LeftMates (A : Transport.{u, v} l Ω D hl c) (B : Transport.{u, v} l Ω D hl d)
    (r : c.Refinement d) where
  left (s : Stage.{max u v} l) : (A.operation s).F ≅ (B.operation s).F
  leftShift (s : Stage.{max u v} l) : (left s).hom.CommShift ℤ
  normalized (s : RingStage.{max u v} l) :
    RingRefinementNormalized.{u, v} l Ω r s (A.left s) (B.left s)
      (refinementComparisonOfLeft l Ω (A.operation (s.stage l)) (B.operation (s.stage l))
        (left (s.stage l)) (leftShift (s.stage l)))
  rational (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω X (.integral E)) :
    (A.localization E).q.inv.app K ≫
        (rationalization.{u, v} l Ω E Y).map ((left (.integral E)).hom.app K) ≫
        (B.localization E).q.hom.app K =
      (left (.rational E)).hom.app ((rationalization.{u, v} l Ω E X).obj K)
  common (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω E))) :
    (A.common E).q.inv.app K ≫
        (commonInclusion.{u, v} l Ω Y E).map
          ((left (.rational (commonField.{u, v} l Ω E))).hom.app K) ≫
        (B.common E).q.hom.app K =
      (left .closed).hom.app ((commonInclusion.{u, v} l Ω X E).obj K)


end WeilConjectures.ExceptionalRefinement
```

### lean/Sheaf/Paper/ExceptionalRefinementSystemData.lean

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q24 and Z6
-/
module

public import Sheaf.Paper.ExceptionalRefinementMatesData
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.Paper.SystemProjectionFormulaMaps

/-! # Strict-system refinement words and normalized total-limit realizations -/

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
open WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

variable {c d : Compactification f}

/-- The actual reconstructed input, retaining every transition before total limit.
Source: Zheng Construction 5.15 (blueprint: lem-sf-exceptional-refinement-mates). -/
abbrev reducedInput (E : FieldStage.{max u v} l) :=
  RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙ (calculus l E.carrier X).reduction

/-- The normalized reduction shift is the adjunction conjugate of the Roos limit shift.
Source: blueprint termwise/Roos shifts (blueprint: lem-sf-exceptional-refinement-mates). -/
instance reducedInputShift (E : FieldStage.{max u v} l) :
    (reducedInput.{u, v} l Ω (X := X) E).CommShift ℤ :=
  letI := reductionShift l E.carrier X
  inferInstanceAs (((finiteTorConstructibleIntegral l E.carrier X).ι ⋙
    (calculus l E.carrier X).reduction).CommShift ℤ)

/-- The whole-system compact-support functor on normalized integral inputs.
Source: Zheng Construction 5.15 (blueprint: lem-sf-exceptional-refinement-mates). -/
abbrev systemSupport (E : FieldStage.{max u v} l) (o : Operations l E.carrier)
    (a : Compactification f) :=
  reducedInput.{u, v} l Ω (X := X) E ⋙ SystemProjectionFormula.support l E.carrier o a

/-- The support shift is termwise open shift followed by its proper adjoint shift.
Source: blueprint termwise shifts (blueprint: lem-sf-exceptional-refinement-mates). -/
instance systemSupportShift (E : FieldStage.{max u v} l) (o : Operations l E.carrier)
    (a : Compactification f) : (systemSupport.{u, v} l Ω E o a).CommShift ℤ :=
  letI := systemOpenShift l E.carrier o a.i
  letI := systemPushShift l E.carrier o a.g
  inferInstanceAs ((reducedInput.{u, v} l Ω (X := X) E ⋙
    (Operations.shriek l E.carrier o a.i ⋙ Operations.push l E.carrier o a.g)).CommShift ℤ)

/-- Realization of a support expression by its actual proper/open comparisons and the
inverse reconstruction unit. The inverse is evaluated only on the derived-complete input.
Source: blueprint retained step 20 (blueprint: lem-sf-exceptional-refinement-mates). -/
def realizationComponent (E : FieldStage.{max u v} l) (o : Operations l E.carrier)
    (R : Realizations l E.carrier D o) (a : Compactification f)
    (K : C.{u, v} l Ω X (.integral E))
    (hK : Good l E.carrier X ((reducedInput.{u, v} l Ω (X := X) E).obj K))
    (hJ : Good l E.carrier a.Z ((Operations.shriek l E.carrier o a.i).obj
      ((reducedInput.{u, v} l Ω (X := X) E).obj K))) :
    (coefficientSequenceLimit l E.carrier Y).obj ((systemSupport.{u, v} l Ω E o a).obj K) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) a).obj K.obj :=
  (R.realizationModel.push l E.carrier a.g).hom.app
      ((Operations.shriek l E.carrier o a.i).obj
        ((reducedInput.{u, v} l Ω (X := X) E).obj K)) ≫
    (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) a.g).map
      ((R.openRealization a.i (a.quasiCompact_openImmersion inferInstance)
        ((reducedInput.{u, v} l Ω (X := X) E).obj K) hK hJ).hom) ≫
    (PurCompactSupport.image (PurCompactSupport.completed l E.carrier) a).map
      (SystemProjectionFormula.inverseOnDomain ((calculus l E.carrier X).adjunction.unit.app K.obj))

/-- The strict-system inverse refinement and its total-limit realization are kept together.
`word` is an equality in the derived category of systems, before any evaluation or limit.
`realizationNormalized` fixes all endpoint identifications by the actual primitive maps.
Source: Zheng 5.13--5.15; blueprint retained step 20
(blueprint: lem-sf-exceptional-refinement-mates). -/
structure SystemRealization (A : Transport.{u, v} l Ω D hl c)
    (B : Transport.{u, v} l Ω D hl d) (r : c.Refinement d)
    (P : Mates.{u, v} l Ω D hl A B r) (E : FieldStage.{max u v} l)
    (o : Operations l E.carrier) (R : Realizations l E.carrier D o) where
  alpha : systemSupport.{u, v} l Ω E o c ≅ systemSupport.{u, v} l Ω E o d
  word (K : C.{u, v} l Ω X (.integral E)) :
    alpha.inv.app K = (SystemProjectionFormula.refinement l E.carrier o R.compositors
      R.openComparisons R.canonicalBridge R.properOpen r).app
        ((reducedInput.{u, v} l Ω (X := X) E).obj K)
  inputGood (K : C.{u, v} l Ω X (.integral E)) :
    Good l E.carrier X ((reducedInput.{u, v} l Ω (X := X) E).obj K)
  openGood (a : Compactification f) (K : C.{u, v} l Ω X (.integral E)) :
    Good l E.carrier a.Z ((Operations.shriek l E.carrier o a.i).obj
      ((reducedInput.{u, v} l Ω (X := X) E).obj K))
  realization (a : Compactification f) :
    systemSupport.{u, v} l Ω E o a ⋙ coefficientSequenceLimit l E.carrier Y ≅
      RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) a
  realizationNormalized (a : Compactification f) (K : C.{u, v} l Ω X (.integral E)) :
    (realization a).hom.app K =
      realizationComponent.{u, v} l Ω D E o R a K (inputGood K) (openGood a K)
  integralMap (K : C.{u, v} l Ω X (.integral E)) :
    (coefficientSequenceLimit l E.carrier Y).map (alpha.hom.app K) ≫
        (realization d).hom.app K =
      (realization c).hom.app K ≫ (A.left (.integral E)).inv.app K ≫
        (RingStage.inclusion.{u, v} l Ω Y (.integral E)).map
          ((P.comparison (.integral E)).left.hom.app K) ≫
        (B.left (.integral E)).hom.app K
  shift : alpha.hom.CommShift ℤ
  realizationShift (a : Compactification f) (K : C.{u, v} l Ω X (.integral E)) (m : ℤ) :
    letI := ringInclusionShift l Ω X (.integral E)
    (realization a).hom.app (K⟦m⟧) ≫
        ((RingStage.inclusion.{u, v} l Ω X (.integral E) ⋙
          PurCompactSupport.image
            (PurCompactSupport.completed l E.carrier) a).commShiftIso m).hom.app K =
      (coefficientSequenceLimit l E.carrier Y).map
          (((systemSupport.{u, v} l Ω E o a).commShiftIso m).hom.app K) ≫
        ((Functor.commShiftIso (coefficientSequenceLimit l E.carrier Y)
          (self := limitShift l E.carrier Y) m).hom.app
            ((systemSupport.{u, v} l Ω E o a).obj K)) ≫
        ((realization a).hom.app K)⟦m⟧'


end WeilConjectures.ExceptionalRefinement
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalRefinementMates | Z6 | Own theorem assembles the repaired transport data. |
| Sheaf.Paper.ExceptionalRefinementTransportData | new, Z6 | Owns Transport and its normalized scalar and transition fields. |
| Sheaf.Paper.ExceptionalRefinementSystemData | new, Z6 | Owns strict-system support and primitive realization data. |
| Sheaf.Paper.ExceptionalRefinementRightSquare | new, Z6 | Proves right descent by counit transposition independently of the geometric data. |
| Sheaf.Paper.ExceptionalRefinementMatesData | new, Z6 | Owns Mates and the left-only conclusion record. |
| Sheaf.Paper.ExceptionalRefinementLeftConstruction | new, Z6 | States only the normalized left construction. |
| Sheaf.Paper.ExceptionalRefinementSystemRealization | new, Z6 | States the strict-system lift of an existing normalized comparison. |

The downstream.py --uses Transport audit lists only the item itself. A source search of
lean/Sheaf and lean/WeilConjectures finds no existing direct importer of
ExceptionalRefinementMates and no external reference to its namespace or declarations.
There are therefore no existing Lean consumer adaptations or consumer compiles to perform.
The sole DAG citer is lem-sf-constructible-exceptional-left-refinements: its input records
already retain normalized scalar maps and the transition action, so its use still holds.
No other existing Lean module or existing node is changed.

## Status

landed 20261027T013016-L-2358323 2026-10-27 (merge of deliver/Z6/Sheaf.Paper.ExceptionalRefinementMates)
