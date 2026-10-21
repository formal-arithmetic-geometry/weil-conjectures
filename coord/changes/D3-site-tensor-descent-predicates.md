# SheafOfModules.site_derived_tensor_descent_independentCoefficients

## Reason

The nested choice predicates repeatedly expand during type checking of the restriction
module. Name the three predicates transparently, retaining every original clause, and
name the original homotopy and derived existence proofs before selecting their witnesses. All universe arguments to the existence APIs are explicit. The tensor
signature is unchanged. Its body is definitionally the original nested choice by proof
irrelevance; no new tensor, hypothesis or weakened conclusion is introduced. Private
cone proofs are generalized to arbitrary abelian monoidal categories with the same
cone, bicomplex braiding and signed-flip argument. Its quotient comparison now uses
the existing generic bifunctor factorization API, and a private generic map equation
replaces repeated unfolding of the quotient construction. This source module is unclaimed.

## Old

```lean
theorem site_derived_tensor_descent_independentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ∃ P : ObjectProperty (HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)),
      (∀ X, P X ↔ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) X.as ∧
        ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (X.as.X n)) ∧
      (∃ F : ((HomotopyCategory.quasiIso (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up
          ℤ)).inverseImage P.ι).Localization ⥤ (DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))),
        F.IsEquivalence ∧ Nonempty (((HomotopyCategory.quasiIso (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up
          ℤ)).inverseImage P.ι).Q ⋙ F ≅ (P.ι ⋙ DerivedCategory.Qh))) ∧
      (∃ B : (HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)) ×
          (HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)) ⥤
          (HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)),
        Nonempty (((HomotopyCategory.quotient (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ)).prod
          (HomotopyCategory.quotient (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ))) ⋙ B ≅
          Functor.uncurry.obj
            ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) _
          (SheafOfModules.monoidalCategory.{v, u, r} R)).map₂HomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙
                (HomotopyCategory.quotient (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
          (ComplexShape.up ℤ))) ∧
        ∃ T : (DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ×
          (DerivedCategory
          (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ⥤
          (DerivedCategory
          (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))),
          Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
            ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙ T)) ∧
      (∀ (E : Type e) (_ : Category.{z} E)
        (U V : (DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ×
          (DerivedCategory
          (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ⥤ E),
        Function.Bijective (fun τ : U ⟶ V ↦
          Functor.whiskerLeft ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) τ))

/-- The derived tensor supplied by the resolving-class localization, in independent universes.
The natural representative comparison and unique-extension property of
`site_derived_tensor_descent_independentCoefficients` determine this functor up to the
unique compatible natural isomorphism. No functorial resolutions are chosen.
Source: Stacks, Tags 06YS, 0G7D, 06YT, 06YU
(blueprint: lem-weil-pbc-site-derived-tensor-descent). -/
noncomputable def siteDerivedTensorIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ×
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R).choose_spec.2.2.1.choose_spec.2.choose

```

## New

```lean
section TensorDescentPredicates

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasDerivedCategory.{w} (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]

set_option hygiene false in
local notation "𝓜" => SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The derived-comparison predicate used in the recorded descent witness.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-site-derived-tensor-descent). -/
noncomputable def SiteDerivedTensorDescentDerivedSpec
    (P : ObjectProperty (HomotopyCategory 𝓜 (.up ℤ)))
    (B : HomotopyCategory 𝓜 (.up ℤ) × HomotopyCategory 𝓜 (.up ℤ) ⥤
      HomotopyCategory 𝓜 (.up ℤ))
    (T : DerivedCategory 𝓜 × DerivedCategory 𝓜 ⥤ DerivedCategory 𝓜) : Prop :=
  Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
    ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙ T)

/-- The homotopy-comparison predicate, with its derived witness named separately.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-site-derived-tensor-descent). -/
noncomputable def SiteDerivedTensorDescentHomotopySpec
    (P : ObjectProperty (HomotopyCategory 𝓜 (.up ℤ)))
    (B : HomotopyCategory 𝓜 (.up ℤ) × HomotopyCategory 𝓜 (.up ℤ) ⥤
      HomotopyCategory 𝓜 (.up ℤ)) : Prop :=
  letI := monoidalCategory R
  Nonempty (((HomotopyCategory.quotient 𝓜 (.up ℤ)).prod
    (HomotopyCategory.quotient 𝓜 (.up ℤ))) ⋙ B ≅
    Functor.uncurry.obj ((MonoidalCategory.curriedTensor 𝓜).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ HomotopyCategory.quotient 𝓜 (.up ℤ)) ∧
  ∃ T : DerivedCategory 𝓜 × DerivedCategory 𝓜 ⥤ DerivedCategory 𝓜,
    SiteDerivedTensorDescentDerivedSpec J R P B T

/-- The full descent predicate, transparently identical to the expanded statement.
Naming its nested predicates keeps selected witnesses small during kernel checking.
Source: Stacks, Tags 06YS, 06YU, 04VK
(blueprint: lem-weil-pbc-site-derived-tensor-descent). -/
noncomputable def SiteDerivedTensorDescentSpec
    (P : ObjectProperty (HomotopyCategory 𝓜 (.up ℤ))) : Prop :=
  (∀ X, P X ↔ CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) X.as ∧
    ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (X.as.X n)) ∧
  (∃ F : ((HomotopyCategory.quasiIso 𝓜 (.up ℤ)).inverseImage P.ι).Localization ⥤
      DerivedCategory 𝓜,
    F.IsEquivalence ∧ Nonempty (((HomotopyCategory.quasiIso 𝓜 (.up ℤ)).inverseImage P.ι).Q ⋙
      F ≅ P.ι ⋙ DerivedCategory.Qh)) ∧
  (∃ B : HomotopyCategory 𝓜 (.up ℤ) × HomotopyCategory 𝓜 (.up ℤ) ⥤
      HomotopyCategory 𝓜 (.up ℤ), SiteDerivedTensorDescentHomotopySpec J R P B) ∧
  (∀ (E : Type e) (_ : Category.{z} E)
    (U V : DerivedCategory 𝓜 × DerivedCategory 𝓜 ⥤ E),
    Function.Bijective (fun τ : U ⟶ V ↦
      Functor.whiskerLeft ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) τ))

end TensorDescentPredicates

/-- The original homotopy-tensor existence proof, with its predicate kept named.
The quotient comparison determines this bifunctor up to compatible natural isomorphism.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-site-derived-tensor-descent). -/
theorem siteHomotopyTensorExistsIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ∃ B : HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ) ×
        HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ) ⥤
        HomotopyCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ),
      SiteDerivedTensorDescentHomotopySpec J R
        (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R).choose B :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R).choose_spec.2.2.1

/-- The original derived-tensor existence proof, with its predicate kept named.
This separates the proof from the selected data and retains the original witnesses.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-site-derived-tensor-descent). -/
theorem siteDerivedTensorExistsIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ∃ T : DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ×
        DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
        DerivedCategory (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)),
      SiteDerivedTensorDescentDerivedSpec J R
        (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R).choose
        (siteHomotopyTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose T :=
  (siteHomotopyTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose_spec.2

/-- The derived tensor supplied by the resolving-class localization, in independent universes.
The natural representative comparison and unique-extension property of
`site_derived_tensor_descent_independentCoefficients` determine this functor up to the
unique compatible natural isomorphism. No functorial resolutions are chosen.
Source: Stacks, Tags 06YS, 0G7D, 06YT, 06YU
(blueprint: lem-weil-pbc-site-derived-tensor-descent). -/
noncomputable def siteDerivedTensorIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ×
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
  (siteDerivedTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose

```

The existing existential theorem now concludes
`∃ P, SiteDerivedTensorDescentSpec.{u,v,r,w,e,z} J R P`, with its original binders.
Expanding this predicate gives exactly the Old statement. Its constructive proof is
retained. Every public import is retained. No adopted source-library module is edited.

## Users

Refreshed from the current shared sources on 2026-10-21. All existing declaration
users below retain their signatures; no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.CochainTensorModelRigidity | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints | P3 | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.DerivedTensorShiftDescent | V2 | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.ExactPullbackSignedComparison | X8 | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchange | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.FixedTensorLocalizationComparison | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.FlatDvrScalarTensor | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.FlatScalarCyclicResolution | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.FlatScalarTensorResolution | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.FlatScalarTensorUnits | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.FlatScalarTorComparison | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated | C2 | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.KFlatTotalTensorModel | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.SignedLineDerivedBaseChange | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients | unclaimed | Names existing predicates and existence proofs; preserves the selected tensor. |
| Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Algebra.Homology.SplitPerfectDualTorWindow | unclaimed | Definitionally compatible; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection | unclaimed | Definitionally compatible; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleTorIntervalShift | unclaimed | Definitionally compatible; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleTorIntervalTriangle | unclaimed | Definitionally compatible; no edit. |
| Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses | unclaimed | Definitionally compatible; no edit. |
| Sheaf.CategoryTheory.RingedKoszulSmallModelCompletedTensor | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Paper.CartesianCoefficientTwists | P2 | Definitionally compatible; no edit. |
| Sheaf.Paper.CompletedScalarShiftDescent | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Paper.DerivedCompletedTensorBilinearity | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Paper.PullbackTensorCanonicalShiftUnit | C7 | Definitionally compatible; no edit. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Paper.ScalarModelFiniteFlatResolution | unclaimed | Definitionally compatible; no edit. |
| Sheaf.Paper.ShiftedTensorMorphismCalculus | D8 | Definitionally compatible; no edit. |
| Sheaf.Paper.SiteDerivedTensorRestriction | D3 | Uses the additional proved APIs. |
| Sheaf.Paper.UniformCompleteTensor | unclaimed | Definitionally compatible; no edit. |
| Sheaf.SixFunctors.OpenTensorNormalization | unclaimed | Definitionally compatible; no edit. |

## Status

landed 20261021T233637-L-842487 2026-10-21 (merge of deliver/D3/Sheaf.Paper.SiteDerivedTensorRestriction)

## Compatibility validation

The rebuilt source, including both existence APIs and its generic quotient proof,
compiled in the packet check. The following probe also compiled: exact application
with the original expanded descent statement, and `rfl` equality of the selected
tensor with the original nested choice. The final complete three-module proof packet also
compiled cleanly, with the restriction module taking 54.2 seconds after the private
elaboration and totalization repairs. No diagnostic options or admissions remain.
