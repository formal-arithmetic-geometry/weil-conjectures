# CategoryTheory.StrictTowerArithmetic

## Reason
Move the existing definitions into a dependency module so the three genuine proof clauses
can refer to them without an import cycle. No definition body, existing signature or
visibility changes. The original module publicly re-exports the definition module, including
the same five original public dependencies. No consumer source is adapted.

## Old
In lean/Sheaf/CategoryTheory/StrictTowerArithmeticRestriction.lean:

```lean
/-- The paper's level `e(n+1)`, encoded by its predecessor in `ℕ`.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
def index (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ →o ℕ from
    { toFun := fun n ↦ e * (n + 1) - 1
      monotone' := fun _ _ h ↦ Nat.sub_le_sub_right (Nat.mul_le_mul_left e
        (Nat.add_le_add_right h 1)) 1 }).monotone.functor.op

/-- Exact restriction of strict towers along the arithmetic index functor.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
abbrev restriction (A : Type a) [Category.{b} A] (e : ℕ) :
    (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft ℕᵒᵖ ℕᵒᵖ A).obj (index e)

/-- Restriction on complexes of strict towers, before localization.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
abbrev complexRestriction (A : Type a) [Category.{b} A] [Abelian A] (e : ℕ) :=
  (restriction A e).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical derived restriction, induced by the exact restriction functor.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable abbrev derivedRestriction (A : Type a) [Category.{b} A] [Abelian A]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] (e : ℕ) :=
  (restriction A e).mapDerivedCategory

/-- Coordinate selection on the source product of the Roos differential.
Source: Stacks Tag 0H9K, map φ′
(blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable def selection {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (e : ℕ) (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (∏ᶜ fun n : ℕ ↦ X.obj (op n)) ⟶
      ∏ᶜ (fun n : ℕ ↦ X.obj ((index e).obj (op n))) :=
  Pi.lift (fun n ↦ Pi.π (fun i : ℕ ↦ X.obj (op i)) (e * (n + 1) - 1))

/-- Finite-block summation on the target product of the Roos differential.
The summand `k` is the original level `e(n+1)+k`, for `0 ≤ k < e`.
Source: Stacks Tag 0H9K, map φ″
(blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable def block {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (e : ℕ) (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (∏ᶜ fun n : ℕ ↦ X.obj (op n)) ⟶
      ∏ᶜ (fun n : ℕ ↦ X.obj ((index e).obj (op n))) :=
  Pi.lift (fun n ↦ ∑ k ∈ Finset.range e,
    Pi.π (fun i : ℕ ↦ X.obj (op i)) (e * (n + 1) - 1 + k) ≫
      X.map (homOfLE (Nat.le_add_right (e * (n + 1) - 1) k)).op)

/-- The existing termwise inverse-limit functor, for the normalization of its derived unit.
Source: Stacks Tag 0941 (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable abbrev limitComplex (A : Type a) [Category.{b} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Ordinary limit restriction, degree by degree, using the actual limit cone.
Source: Stacks Tag 0H9K (blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable def limitMap {A : Type a} [Category.{b} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] (e : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (limitComplex A).obj X ⟶ (limitComplex A).obj ((complexRestriction A e).obj X) where
  f i := limit.pre (X.X i) (index e)
  comm' i j _ := by
    exact (limit.map_pre (X.d i j) (index e)).symm

/-- The existing transition differential, applied to the evaluated tower complex.
Source: Stacks Tags 08TC and 0H9K
(blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable abbrev boundary {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :=
  towerTransitionEndomorphism (K := fun n : ℕ ↦ X.asFunctor.obj (op n))
    (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)

/-- Mathlib's actual mapping cocone of the existing transition differential.
Source: Stacks Tags 08TC and 0941
(blueprint: lem-sp-strict-tower-arithmetic-restriction). -/
noncomputable abbrev model {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :=
  CochainComplex.mappingCocone (boundary X)
```

## New
The identical declarations above are in
lean/Sheaf/CategoryTheory/StrictTowerArithmeticRestrictionDefs.lean, publicly imported by
the original module. The theorem signature in the original module is unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.CategoryTheory.CompactSupportRoosCofinality | M8 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.CanonicalOriginCompactSupportComposition | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.CompactSupportSiteCoherence | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | Q3 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.CondensedERealization | Y9 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | S1 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | N1 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.IntegralModels | D4 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | A5 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.IntegralTensorPullback | J2 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | Direct importer: the theorem signature and re-exported definitions remain identical. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Not affected: the textual match is its unrelated PrimitiveSystemComparison.restriction constructor; all arithmetic restriction declarations retain their names, types, bodies and public visibility. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Not affected: declarations retain names, types, bodies and public visibility through the re-export. |

The current textual downstream inventory identifies 51 modules mentioning at least
one relocated name; matches on common short names overapproximate actual declaration use.
Each row records the current claim holder. No consumer source is adapted. The two direct
importers, CompactSupportRoosCofinality and RationalCompactSupportCoefficientCoherence,
compile unchanged against the delivered overlay in the resumed 2026-10-19 checks.
Relocation preserves all existing public constants and their values, so no target changes
meaning. The sole original theorem signature also remains identical.

Repair of the return at c470a2b99: refreshed the inventory against the current shared
repository and added SystemPrimitiveComparisonShift. Its short-name match is the
constructor declared in that module, not a reference to the relocated definition.
No consumer adaptation is needed.

## Status
landed 20261019T005415-L-2765462 2026-10-19 (merge of deliver/R7/Sheaf.CategoryTheory.StrictTowerArithmeticRestriction)
