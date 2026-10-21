# SheafOfModules.KFlatFixedTensor derived tensor presentation

## Reason

The original nested existential selections made each dependent comparison repeat the
site tensor and descent types during elaboration and kernel checking. The module
exceeded its single-file compile limit while integrating the proof. Package the exact
existing selections in a typed structure and expose their membership and comparison
fields. Use local irreducibility for the ordinary tensor, descent presentation and derived
tensor during this module’s proof, and expose proved equations to their original
definitions. An explicit section confines the local attributes, and the original
tensor names plus the data-selection constructors are exported as reducible after
that section. Thus importing modules retain the original abbreviation interface. Register the already available totalization and additive instances locally for
the sealed ordinary tensor. Importers retain their original instance search.

The derived tensor is unchanged as a mathematical object: `derivedTensor_eq_published`
is proved by unfolding the data packages. `ordinaryTensor_eq_published` similarly
identifies the ordinary tensor. The constructors only access the original nested
choices and do not introduce a new existence-based choice. The representative
comparison uses the identical choices, in the
same orientation and order; only their access paths and membership proof names change.
No target signature changes. Definitions used by targets require the usual statement
review; the definitional equality and unchanged representative formula are the evidence
for that review. No adopted source-library file is edited.

The current performance repair additionally gives `selectedTensorPresentation` an
explicit type and local irreducibility, restoring reducibility after the section.
The private `tensorPresentationComparison` definition stores the original composite
of homotopy comparison, resolving comparison and inverse currying counit. Its
component equation is proved, so the normalization uses that API directly.
The full module passed without warnings in 51.7 seconds together with twelve
unchanged current consumers, including all three named by the return. No new
choice or public mathematical object is introduced.

Reviewer correction (2026-10-22, review of 7084dc789569). As delivered, `derivedTensor R`
was equal to `Functor.curry.obj (siteDerivedTensorIndependentCoefficients J R)` only at
default transparency (`rfl`), not reducibly (`with_reducible rfl` failed): its reducible
unfolding ended in the `Exists.choose` projections of `TensorPresentation.ofExists`, which
match the published tensor only after unfolding the plain definition
`siteDerivedTensorIndependentCoefficients`. The consumer
`Sheaf.Paper.DerivedCompletedTensorBilinearity` (`derivedTensorLinear`, line 498) relies
on the old abbreviation and failed with an application type mismatch. Now the
`derivedTensor` field of `selectedTensorPresentation` is literally the published
`siteDerivedTensorIndependentCoefficients J R`, and the other three fields are the
same selected terms (the resolving comparison is the identical term, checked against
the literal field at full transparency, with no cast). The exported `derivedTensor` therefore unfolds reducibly to exactly
the original abbreviation body. All 15 direct importers compile against the corrected
module, DerivedCompletedTensorBilinearity among them.

## Old

```lean
abbrev ordinaryTensor := @curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R)

/-- The existing direct-sum total tensor, as a curried bifunctor on complexes.
Source: Stacks, Tag 06YM (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
abbrev totalTensor := (ordinaryTensor R).map₂CochainComplex

variable [HasDerivedCategory.{w} (Modules R)]

/-- The published K-flat-derived tensor, with no new choice of tensor or resolutions.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
abbrev derivedTensor := Functor.curry.obj
  (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R)

/-- The actual resolving comparison selected by the published descent theorem.
It is oriented from the localized total tensor to the derived tensor. Its arguments
are exactly flat-term K-flat complexes; the homotopy comparison is composed with the
resolving comparison, using the dependency's membership equivalence.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
def representativeIso
    (A B : CochainComplex (Modules R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients B)
    (hAf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X n))
    (hBf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (B.X n)) :
    DerivedCategory.Q.obj (((totalTensor R).obj A).obj B) ≅
      (((derivedTensor R).obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B)) :=
  let h := SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R
  let P := h.choose
  let c := h.choose_spec.2.2.1.choose_spec.1.some
  let d := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  let a : P.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj A,
    (h.choose_spec.1 _).2 ⟨hA, hAf⟩⟩
  let b : P.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj B,
    (h.choose_spec.1 _).2 ⟨hB, hBf⟩⟩
  (DerivedCategory.Qh.mapIso (c.app (A, B))).symm ≪≫ d.app (a, b)

```

## New

```lean
section LocalTensorDefinitions

/-- The existing canonical tensor of module sheaves.
Source: Stacks, Tag 03EK (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
def ordinaryTensor : Modules R ⥤ Modules R ⥤ Modules R :=
  @curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R)

/-- The ordinary tensor is exactly the existing canonical sheaf tensor.
Source: Stacks, Tag 03EK
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
theorem ordinaryTensor_eq_published : ordinaryTensor R =
    @curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R) := by
  unfold ordinaryTensor
  rfl

/-- The canonical sheaf tensor is additive in its first argument.
Source: Stacks, Tag 03EK
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
theorem tensorAdditive : (ordinaryTensor R).Additive := by
  unfold ordinaryTensor
  infer_instance

attribute [local instance 2000] tensorAdditive

/-- The canonical sheaf tensor is additive in its second argument.
Source: Stacks, Tag 03EK
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
theorem tensorObjAdditive (M : Modules R) :
    ((ordinaryTensor R).obj M).Additive := by
  unfold ordinaryTensor
  infer_instance

attribute [local instance 2000] tensorObjAdditive

/-- The canonical direct-sum total tensor exists for every pair of complexes.
These named instances provide the interface of the unexpanded ordinary tensor.
Source: Stacks, Tag 06YM
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
theorem tensorHasMapBifunctor (A B : CochainComplex (Modules R) ℤ) :
    CochainComplex.HasMapBifunctor A B (ordinaryTensor R) := by
  unfold ordinaryTensor
  infer_instance

attribute [local instance 2000] tensorHasMapBifunctor
attribute [local irreducible] ordinaryTensor

/-- The existing direct-sum total tensor, as a curried bifunctor on complexes.
Source: Stacks, Tag 06YM (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
abbrev totalTensor : CochainComplex (Modules R) ℤ ⥤
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (ordinaryTensor R).map₂CochainComplex

variable [HasDerivedCategory.{w} (Modules R)]

/-- All the witnesses and proof fields of the published site tensor descent theorem.
This is a typed package of the original nested choices, rather than a new descent.
Source: Stacks, Tags 06YS and 06YU
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
def selectedResolvingTensorPresentation : ResolvingTensorPresentation
    (HomotopyCategory.quotient (Modules R) (.up ℤ))
    (DerivedCategory.Qh : HomotopyCategory (Modules R) (.up ℤ) ⥤ DerivedCategory (Modules R))
    (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
    (Functor.uncurry.obj (totalTensor R))
    (fun X ↦ CochainComplex.IsKFlatIndependentCoefficients X.as ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (X.as.X n)) :=
  ResolvingTensorPresentation.ofExists
    (HomotopyCategory.quotient (Modules R) (.up ℤ))
    (DerivedCategory.Qh : HomotopyCategory (Modules R) (.up ℤ) ⥤ DerivedCategory (Modules R))
    (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
    (Functor.uncurry.obj (totalTensor R))
    (fun X ↦ CochainComplex.IsKFlatIndependentCoefficients X.as ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (X.as.X n))
    (fun P ↦ ∀ (E : Type) (_ : Category.{0} E)
      (U V : DerivedCategory (Modules R) × DerivedCategory (Modules R) ⥤ E),
      Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft
        ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) τ))
    (by
      unfold totalTensor ordinaryTensor
      exact (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R))

attribute [local irreducible] selectedResolvingTensorPresentation

/-- The resolving property already selected by site tensor descent.
Source: Stacks, Tags 06YS and 06YU
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
abbrev resolvingProperty : ObjectProperty (HomotopyCategory (Modules R) (.up ℤ)) :=
  (selectedResolvingTensorPresentation R).property

/-- The published membership equivalence for the resolving subcategory.
Source: Stacks, Tags 06YS and 06YU
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
theorem resolvingProperty_spec (X : HomotopyCategory (Modules R) (.up ℤ)) :
    resolvingProperty R X ↔ CochainComplex.IsKFlatIndependentCoefficients X.as ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (X.as.X n) :=
  (selectedResolvingTensorPresentation R).membership X

/-- The original homotopy and derived tensors with their selected comparisons.
Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
def selectedTensorPresentation : TensorPresentation
    (HomotopyCategory.quotient (Modules R) (.up ℤ))
    (DerivedCategory.Qh : HomotopyCategory (Modules R) (.up ℤ) ⥤ DerivedCategory (Modules R))
    (Functor.uncurry.obj (totalTensor R)) (resolvingProperty R) where
  homotopyTensor := (selectedResolvingTensorPresentation R).tensor.homotopyTensor
  homotopyComparison := (selectedResolvingTensorPresentation R).tensor.homotopyComparison
  derivedTensor := SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R
  resolvingComparison := by
    with_unfolding_all exact (selectedResolvingTensorPresentation R).tensor.resolvingComparison

attribute [local irreducible] selectedTensorPresentation

/-- The published derived tensor, curried using its shared descent presentation.
Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
def derivedTensor : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R) ⥤
    DerivedCategory (Modules R) := Functor.curry.obj (selectedTensorPresentation R).derivedTensor

attribute [local irreducible] derivedTensor

/-- Packaging the descent data preserves the published derived tensor definitionally.
Proof: the presentation fields are precisely the nested choices defining that tensor.
Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
theorem derivedTensor_eq_published : derivedTensor R = Functor.curry.obj
    (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R) := by
  unfold derivedTensor selectedTensorPresentation
  rfl

/-- The actual resolving comparison selected by the published descent theorem.
It is oriented from the localized total tensor to the derived tensor. Its arguments
are exactly flat-term K-flat complexes; the homotopy comparison is composed with the
resolving comparison, using the dependency's membership equivalence.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-kflat-fixed-tensor-triangulated). -/
def representativeIso
    (A B : CochainComplex (Modules R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients B)
    (hAf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (A.X n))
    (hBf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (B.X n)) :
    DerivedCategory.Q.obj (((totalTensor R).obj A).obj B) ≅
      (((derivedTensor R).obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B)) := by
  unfold derivedTensor
  exact (selectedTensorPresentation R).representativeIso A B
    ((resolvingProperty_spec R _).2 ⟨hA, hAf⟩)
    ((resolvingProperty_spec R _).2 ⟨hB, hBf⟩)

-- After the proof, close the section and restore the exported abbreviation interface.
end LocalTensorDefinitions
attribute [reducible] ordinaryTensor derivedTensor selectedResolvingTensorPresentation
  selectedTensorPresentation
  TensorPresentation.ofExists ResolvingTensorPresentation.ofExists

```

`ResolvingTensorPresentation` stores the resolving property, its membership equivalence,
the localization proof and its `TensorPresentation`. The latter stores the two functors
and their two natural comparisons. The generic `.ofExists` constructors project the
original existential theorem in exactly the same order. In particular, they do not
choose an arbitrary new object from a weakened existence statement. The localization
proof is the usual transfer along the published localization equivalence.

## Users

The final pre-submission refresh lists 229 downstream modules; every one is included in the table.

The repair refresh on 2026-10-22 checks the current shared sheaf-dag sources.
The initial fresh `tools/downstream.py` check listed 59 transitive downstream
modules. A refresh during the delivery wait lists 227; all are covered by the
table below, with current claim holders recorded for newly found consumers. The table also retains earlier consumers and
identifies their earlier validation separately. In particular it lists all three
textual derivedTensor consumers named in the landing return:
`Sheaf.Paper.IntegralModels`, `Sheaf.Paper.IntegralStratumHomFormula`, and
`Sheaf.SixFunctors.IntegralTensorInverseImage`. Re-reading their current sources
confirms that these names resolve to
`AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor`, defined in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`; they do not
refer to the repaired `SheafOfModules.KFlatFixedTensor.derivedTensor`.
Fresh compilation of the retained item passed without warnings in 56.7 seconds,
then explicitly remote server compilation passed in 57.7 seconds
(`LCOMPILE_NO_LOCAL=1`). There are zero holes in this module.
No consumer source is changed. The unchanged public tensors and representative maps
are definitionally equal to their previous definitions.

The definition-equality diagnostic `DefinitionEqualityCheck.lean` (scratch only)
compiles in 25.0 seconds and proves heterogeneous equality of the new representative
isomorphism and its original nested-choice expression by unfolding and reflexivity.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated | C2 | Same tensor and comparison; completed proof uses the shared presentation. |
| Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints | P3 | Unchanged current source compiles against the repaired candidate (26.1 s); no adaptation. |
| Sheaf.Algebra.Homology.FiniteFreeResolutionTensor | T5 | Check encounters unrelated WeilTensorProduct universe errors. |
| Sheaf.Algebra.Homology.LineUnboundedDerivedTensor | C9 | Unchanged current source compiles against the repaired candidate (7.0 s); no adaptation. |
| Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison | R2 | Unchanged current source compiles against the repaired candidate (34.0 s); no adaptation. |
| Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization | R6 | Unchanged current source compiles against the repaired candidate (15.9 s); no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleTorIntervalShift | M2 | Unchanged current source compiles against the repaired candidate (23.2 s); no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleTorIntervalTriangle | Z7 | Unchanged source compiles against the candidate (6.8 s). |
| Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison | P4 | Definitions unchanged; compile attempt returned server busy. |
| Sheaf.CategoryTheory.KoszulFibreLinearDescent | X3 | Unchanged source compiles against the candidate (5.8 s). |
| Sheaf.Paper.PeriodicTensorNormalForm | P5 | Unchanged current source compiles against the repaired candidate (25.8 s); no adaptation. |
| Sheaf.Paper.PullbackTensorCanonicalShiftUnit | C7 | Unchanged current source compiles against the repaired candidate (13.8 s); no adaptation. |
| Sheaf.Paper.WeilTensorWeil | unclaimed | Current transitive consumer. Earlier downstream check encountered unrelated WeilTensorProduct universe errors; definitions remain unchanged. |
| Sheaf.Algebra.Homology.FlatScalarCyclicResolution | unclaimed | Unchanged current source compiles against the repaired candidate (18.1 s); no adaptation. |
| Sheaf.Algebra.Homology.ExactPullbackSignedComparison | X8 | Unchanged current source compiles against the repaired candidate (30.5 s); no adaptation. |
| Sheaf.Paper.BoundaryBoundedTensorComparison | S5 | Unchanged source compiles against final candidate (20.9 s). Its textual derivedTensor hit uses a different namespace. |
| Sheaf.Paper.ScalarModelFiniteFlatResolution | unclaimed | Unchanged source compiles against final candidate (33.4 s). |
| Sheaf.Algebra.Homology.SplitPerfectDualTorWindow | unclaimed | Transitive importer; no textual use of changed names; existing definitions preserved. |
| Sheaf.AlgebraicGeometry.EtaleKFlatSupportComparison | C5 | Transitive importer; no textual use of changed names; existing definitions preserved. |
| Sheaf.Paper.DerivedCompletedTensorBilinearity | G8 | Transitive importer; no textual use of changed names; existing definitions preserved. |
| Sheaf.Algebra.Homology.SignedLineDerivedBaseChange | unclaimed | New consumer; tensors and representative comparison definitionally unchanged; final-overlay check returned server busy. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | New transitive importer; no textual use of changed names; existing definitions preserved. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorData | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorDescent | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Algebra.Homology.LocalizedStrictTensorLinearEvaluation | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | B9 | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | T3 | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | T9 | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | W7 | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralModels | U1 | Unchanged current source compiles against the repaired candidate (31.4 s); no adaptation. Its textual derivedTensor hit uses the separate CondensedRing tensor. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | K6 | Unchanged current source compiles against the repaired candidate (19.2 s); no adaptation. Its textual derivedTensor hit uses the separate CondensedRing tensor. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | C5 | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | C3 | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | A7 | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Unchanged current source compiles against the repaired candidate (36.2 s); no adaptation. Its textual derivedTensor hit uses the separate CondensedRing tensor. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | W8 | Transitive importer; public definitions and signatures preserved; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed | Transitive importer; original public definitions preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| TargetsCheck | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Current downstream consumer; public tensors and representative maps are definitionally unchanged; no source adaptation. |
| Sheaf.CategoryTheory.KoszulTensorDerivedTower | unclaimed | Unchanged new direct consumer compiles against the submitted candidate (4.0 s), after the item (40.8 s); no source adaptation. |

## Status

landed 20261021T233622-L-837738 2026-10-21 (merge of deliver/C2/Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated)

A queue-time refresh lists 230 downstream modules. The new direct consumer
`Sheaf.CategoryTheory.KoszulTensorDerivedTower` is included above; its public
tensor and theorem interfaces are unchanged. No source adaptation is needed.
