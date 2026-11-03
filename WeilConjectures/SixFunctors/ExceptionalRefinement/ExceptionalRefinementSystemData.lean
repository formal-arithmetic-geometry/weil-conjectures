/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalRefinement.ExceptionalRefinementMatesData
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralOperationShiftData
public import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionFormulaMaps

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
