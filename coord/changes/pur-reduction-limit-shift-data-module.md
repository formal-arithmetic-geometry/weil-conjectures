# PurReductionLimitShiftData

## Reason

The finite normalization and Roos normalization lemmas must mention the existing
shift-data helpers. Keeping the definitions together with their inhabitation theorem
would cause an import cycle. Move the five declarations to
`Sheaf.Paper.PurReductionLimitShiftData`; publicly import that module from the
original module. This is a module/interface refactor, with no mathematical change.
The attached definition node follows the move. No source-library module changes.

## Old

In `Sheaf.Paper.PurReductionLimitShiftAdjunction`:

```lean
/-- The canonical comparison from the actual sequence limit to the termwise
limit of a specified K-injective replacement of the restricted sequence.
It is the exact restriction/localization comparison, followed by `Rlim(j)` and
`rightDerivedFunctorObjQIso`; no new choice of a derived functor is made.
Source: Stacks 0941 and 0D6E
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
def purCoefficientLimitModel
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j] :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (coefficientConstantTowerLimit l E W).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app N ≪≫
        asIso (DerivedCategory.Q.map j)) ≪≫
    Functor.rightDerivedFunctorObjQIso
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) I

/-- The shifted replacement map is exactly `j[r]`, with the canonical termwise
identification `U(N[r]) ≅ (UN)[r]` in its source.
Source: Stacks 0941, derived.tex 070H
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
def purCoefficientShiftedResolution
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ I) (r : ℤ) :
    ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (N⟦r⟧) ⟶ I⟦r⟧ :=
  (((coefficientSequenceRestriction l E W).mapHomologicalComplex
    (ComplexShape.up ℤ)).commShiftIso r).hom.app N ≫ j⟦r⟧'

/-- The canonical product comparison for the evaluated shifted tower, using
localization's cochain shift and preservation of products by the shift equivalence.
Source: Stacks 0941 and derived.tex 0BK6
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
def purCoefficientRoosProductShift
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E W))]
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (r : ℤ) :
    (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj ((I⟦r⟧).asFunctor.obj (op n))) ≅
      (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)))⟦r⟧ :=
  Limits.Pi.mapIso (fun n : ℕ ↦ (DerivedCategory.Q.commShiftIso r).app
    (I.asFunctor.obj (op n))) ≪≫
      (PreservesProduct.iso (shiftFunctor _ r)
        (fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)))).symm

/-- A Roos triangle whose first vertex is the actual sequence-limit functor,
computed on a specified simultaneous K-injective tower. Its first arrow is
normalized by the actual limit-cone projections through `purCoefficientLimitModel`.
Source: Stacks 0941 and 08TC
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
structure PurCoefficientRoosTriangle
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E W))]
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j] where
  p : (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N) ⟶
    ∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n))
  δ : (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n))) ⟶
    ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N))⟦(1 : ℤ)⟧
  triangle : IsDerivedLimitTriangle
    (fun n : ℕ ↦ DerivedCategory.Q.map
      (I.asFunctor.map (homOfLE (Nat.le_succ n)).op))
    ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N)) p δ
  projection : ∀ n : ℕ,
    p ≫ Limits.Pi.π _ n = (purCoefficientLimitModel l E W N I j).hom ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (lim.π (op n)) (ComplexShape.up ℤ)).app I)

/-- Normalized shifts for the given reduction/limit adjunction. Finite shifts
are fixed by the existing K-flat model, not chosen to match reduction afterwards.
The limit equation uses the fixed resolution comparison for `j` and `j[r]`.
The Roos connecting-map equation uses that same `limit_shift` and the actual
limit triangles, with the cochain sign `r.negOnePow`.
Source: Stacks 07A6, 0941 and derived.tex 0A8D
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
structure PurReductionLimitShiftData
    (S : CoefficientDerivedSystemCalculus l E W) where
  reduction_shift : S.reduction.CommShift ℤ
  finite_reduction_shift :
    ∀ n : ℕ, (coefficientFiniteDerivedExtension l E W n).CommShift ℤ
  finite_shift_model :
    ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
      (hQr : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          (Q⟦r⟧)),
      letI := finite_reduction_shift n
      (coefficientFiniteDerivedExtension l E W n).map
          ((DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
        ((coefficientFiniteDerivedExtension l E W n).commShiftIso r).hom.app
          (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteReductionModel l E W Q hQ n).hom⟦r⟧' =
      (coefficientFiniteReductionModel l E W (Q⟦r⟧) hQr n).hom ≫
        DerivedCategory.Q.map
          ((((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso r).hom.app Q) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)
  reduction_shift_evaluation :
    ∀ n : ℕ,
      letI := reduction_shift
      letI := finite_reduction_shift n
      NatTrans.CommShift (S.reductionEvaluation n).hom ℤ
  limit_shift : (coefficientSequenceLimit l E W).CommShift ℤ
  limit_shift_resolution :
    ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
      (r : ℤ) [(I⟦r⟧).IsKInjective]
      [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
      letI := limit_shift
      (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
        ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
          (DerivedCategory.Q.obj N) ≫
        (purCoefficientLimitModel l E W N I j).hom⟦r⟧' =
      (purCoefficientLimitModel l E W (N⟦r⟧) (I⟦r⟧)
        (purCoefficientShiftedResolution l E W N I j r)).hom ≫
        DerivedCategory.Q.map
          ((((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso r).hom.app I) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)
  products : HasCountableProducts (DerivedCategory (scalarReductionSource l E W))
  roos :
    letI := products
    ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j],
      PurCoefficientRoosTriangle l E W N I j
  roos_triangle_shift :
    letI := products
    letI := limit_shift
    ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
      (r : ℤ) [(I⟦r⟧).IsKInjective]
      [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).p ≫
        (purCoefficientRoosProductShift l E W I r).hom =
      (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
        ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
          (DerivedCategory.Q.obj N) ≫ (roos N I j).p⟦r⟧') ∧
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).δ ≫
        ((coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
          ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
            (DerivedCategory.Q.obj N))⟦(1 : ℤ)⟧' =
      r.negOnePow • ((purCoefficientRoosProductShift l E W I r).hom ≫
        (roos N I j).δ⟦r⟧' ≫ (shiftFunctorComm _ 1 r).hom.app
          ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N))))
  unit_shift :
    letI := reduction_shift
    letI := limit_shift
    ∀ r : ℤ,
      Adjunction.CommShift.CompatibilityUnit S.adjunction
        (S.reduction.commShiftIso r)
        ((coefficientSequenceLimit l E W).commShiftIso r)
  counit_shift :
    letI := reduction_shift
    letI := limit_shift
    ∀ r : ℤ,
      Adjunction.CommShift.CompatibilityCounit S.adjunction
        (S.reduction.commShiftIso r)
        ((coefficientSequenceLimit l E W).commShiftIso r)
```

## New

The five declarations above keep their names, signatures and attributes in
`Sheaf.Paper.PurReductionLimitShiftData`. Four bodies are verbatim. The canonical
limit-model body is normalized as follows, to avoid an expensive definitional
conversion while checking applications of the existing comparison-shift API:

```lean
  SequenceKInjectiveComparison.comparisonIso (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) N I j
```

Unfolding `comparisonIso`, `Functor.mapIso_trans` identifies the first two mapped
isomorphisms with the old map of their composite, and `Iso.trans_assoc` identifies
the parenthesization. Thus the model map, inverse and downstream equations have
exactly the same meaning; it uses the same restriction/localization comparison,
the same Q(j), and the same rightDerivedFunctorObjQIso. No choice is introduced.
The definition module publicly imports the existing comparison module for this body. The original module adds:

```lean
public import Sheaf.Paper.PurReductionLimitShiftData
```

The declarations' visibility remains public and exposed. The new module uses
local irreducibility on the large coefficient-existence witnesses, reduction
models and limit functors, and disables unneeded generated size-of/injectivity
auxiliaries. Their explicit declaration signatures are unchanged. The limit model has the normalization stated above; the other bodies are unchanged. There is no changed target meaning and
no mathematical statement-review reopening caused by these definitions.

## Users

`tools/downstream.py Sheaf.Paper.PurReductionLimitShiftAdjunction --uses
PurReductionLimitShiftData` lists the following fourteen downstream modules and the
item itself as a direct name user. Holders are the read-only snapshot, 2026-10-25.
No consumer edit is needed and no consumer module is delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientEnrichedGlobalShift | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.Paper.IntegralAdjunctionBijection | S6 | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.Paper.IntegralMappingLimitProjections | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.Paper.TwistedPullbackReductionTower | X2 | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | W4 | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed (local snapshot) | Unchanged; original module publicly re-exports all five declarations. |
| Sheaf.Paper.PurReductionLimitShiftAdjunction | C1 | Imports the extracted definitions; theorem signature unchanged. |
| Sheaf.Paper.PurReductionFiniteShiftNormalization | C1 (new in this packet) | Imports the extracted definitions to state finite normalization. |
| Sheaf.Paper.PurCoefficientRoosShiftNormalization | C1 (new in this packet) | Imports the extracted definitions to state Roos normalization. |

## Status

landed 20261025T205419-L-3232844 2026-10-25 (merge of deliver/C1/Sheaf.Paper.PurReductionLimitShiftAdjunction)
