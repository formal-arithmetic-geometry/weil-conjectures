# WeilConjectures.OpenProjectionRoos public completion interfaces

## Reason

Extract the existing public interface into OpenProjectionRoosCompletionData so that the
ordinary, completed-square and restriction construction steps can state their conclusions
without importing their consumer. The original module publicly reexports the data module.
Existing signatures, abbreviations and structures remain verbatim. CompletionData names
three existing clauses through OrdinaryRepresentative, CompletedRepresentative and
RestrictionRepresentative; expanding those names restores its original body byte for byte. All original
public imports remain visible through this reexport. No target statement or definition
meaning changes; no source-library file is edited. Local transparency annotations in the
consumer bound unfolding of existing chosen tensor and coefficient constructions. The
three new predicates are real proposition definitions with the exact original formulas,
not extra assumptions or choices. They prevent repeated elaboration of long chain
expressions across the construction lemmas.

## Old

In Sheaf.SixFunctors.OpenProjectionRoosCompletion, the following public block preceded the
existence theorem:

```lean
section Roos
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]

/-- The boundary of the recorded strict Roos model, without changing its signs.
Source: Stacks 0941 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev boundary (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ T.obj (op n)) (integralOperationsTowerStep T)

/-- Postcomposition of strict towers by the actual termwise functor.
Source: Stacks 0941 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev onTowers (F : A ⥤ B) [F.Additive] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ))

/-- The normalized exact-product comparison. The first and shifted projection
identities specify its action on both summands of the signed mapping fiber.
The augmentation clause supplies the maps with coordinates (a,0) and states their
actual equality, before localization; it does not infer equality from limit projections.
Source: Stacks 09BP and lem-cbc-exact-product-functor-strict-limit
(blueprint: lem-sf-open-projection-roos-completion). -/
structure RoosComparison (F : A ⥤ B) [F.Additive] where
  products : ∀ T : ℕᵒᵖ ⥤ CochainComplex A ℤ,
    (F.mapHomologicalComplex (.up ℤ)).obj (∏ᶜ fun n ↦ T.obj (op n)) ≅
      ∏ᶜ fun n ↦ ((onTowers F).obj T).obj (op n)
  projections : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (n : ℕ),
    (products T).hom ≫ Pi.π (fun k ↦ ((onTowers F).obj T).obj (op k)) n =
      (F.mapHomologicalComplex (.up ℤ)).map (Pi.π (fun k ↦ T.obj (op k)) n)
  iso : integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    onTowers F ⋙ integralOperationsRoosFunctor
  first : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ),
    (iso.hom.app T) ≫ CochainComplex.mappingCocone.fst (boundary ((onTowers F).obj T)) =
      (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.fst (boundary T)) ≫ (products T).hom
  shifted : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i k : ℤ) (h : i + -1 = k),
    (iso.hom.app T).f i ≫
        (CochainComplex.mappingCocone.snd (boundary ((onTowers F).obj T))).v i k h =
      F.map ((CochainComplex.mappingCocone.snd (boundary T)).v i k h) ≫
        ((products T).hom.f k)
  augmentations : ∀ (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) (P : CochainComplex A ℤ)
    (a : (Functor.const ℕᵒᵖ).obj P ⟶ T),
    ∃ (b : P ⟶ integralOperationsRoos T)
      (b' : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶
        integralOperationsRoos ((onTowers F).obj T)),
      b ≫ CochainComplex.mappingCocone.fst (boundary T) =
          Pi.lift (fun n ↦ a.app (op n)) ∧
      (∀ (i k : ℤ) (h : i + -1 = k),
        b.f i ≫ (CochainComplex.mappingCocone.snd (boundary T)).v i k h = 0) ∧
      b' ≫ CochainComplex.mappingCocone.fst (boundary ((onTowers F).obj T)) =
          Pi.lift (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (a.app (op n))) ∧
      (∀ (i k : ℤ) (h : i + -1 = k), b'.f i ≫
        (CochainComplex.mappingCocone.snd (boundary ((onTowers F).obj T))).v i k h = 0) ∧
      (F.mapHomologicalComplex (.up ℤ)).map b ≫ iso.hom.app T = b'

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]

/-- The same lambda in the derived category, through the canonical exact-functor
comparison. Roos computes the total right derived limit by the recorded strict-Roos
comparison, including its augmentation. No new derived-limit object is chosen.
Source: Stacks 0941 (blueprint: lem-sf-open-projection-roos-completion). -/
def RoosComparison.derived (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (r : RoosComparison F) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    F.mapDerivedCategory.obj (DerivedCategory.Q.obj (integralOperationsRoos T)) ≅
      DerivedCategory.Q.obj (integralOperationsRoos ((onTowers F).obj T)) :=
  F.mapDerivedCategoryFactors.app (integralOperationsRoos T) ≪≫
    DerivedCategory.Q.mapIso (r.iso.app T)
end Roos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

/-- The source pair insertion for the open projection formula.
Source: blueprint open factor (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev leftInputs := (IntegralOpenReduction.shriek l E j o).prod
  (𝟭 (DerivedCategory (scalarReductionSource l E X)))

/-- The target pair insertion, with actual exact restriction.
Source: blueprint open factor (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev rightInputs := (𝟭 (DerivedCategory (scalarReductionSource l E U))).prod
  (IntegralOpenReduction.star l E j o)

/-- Inclusion of precisely the two bounded constructible integral domains.
Source: Bhatt--Scholze 6.5.8 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev pairs := (sfIntegralConstructible l E U).ι.prod (sfIntegralConstructible l E X).ι

/-- The actual completed source functor on the stated constructible domain.
Source: Bhatt--Scholze 3.4.10 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev completedLeft := pairs l E (U := U) (X := X) ⋙ leftInputs l E j o ⋙
  integralCompletedTensor l E X

/-- The actual completed tensor on U, before its extension.
Source: Bhatt--Scholze 3.4.10 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev completedInside := pairs l E (U := U) (X := X) ⋙ rightInputs l E j o ⋙
  integralCompletedTensor l E U

/-- The actual completed target functor on the stated constructible domain.
Source: Bhatt--Scholze 3.4.10 (blueprint: lem-sf-open-projection-roos-completion). -/
abbrev completedRight := completedInside l E j o ⋙ IntegralOpenReduction.shriek l E j o

attribute [local irreducible] integralOperationsTensorTowerFunctor
  coefficientTotalTensor integralOperationsTensorLevel
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralComplexFunctor scalarReductionExistence unrestrictedIntegralReductionExistence

variable
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
  (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
  (c : IntegralOpenReduction.Comparison l E j o SX SU st)
  (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)

set_option maxHeartbeats 800000 in
-- The predicate retains simultaneous natural transformations and all representative equations.
/-- The completion of the specified augmented square. Every isomorphism is pinned
by chain or unit equations, including restriction and every strict finite reduction.
`ordinary` is gamma^B, `gamma` is Gamma, `extension` is lambda_j.
Source: Stacks 09BP; Bhatt--Scholze 6.5.5, 6.5.8
(blueprint: lem-sf-open-projection-roos-completion). -/
def CompletionData
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)] :
    Prop :=
    ∃ (extension : RoosComparison (IntegralOpenReduction.extension l E j o)),
    ∃ (restriction : RoosComparison (IntegralOpenReduction.restriction l E j o)),
    ∃ (moduleUnit : 𝟭 (scalarReductionSource l E U) ≅
    IntegralOpenReduction.extension l E j o ⋙ IntegralOpenReduction.restriction l E j o),
    ∃ (_moduleUnit_hom : moduleUnit.hom = (IntegralOpenReduction.ordinaryAdjunction l E j o).unit),
    ∃ (unit : 𝟭 (DerivedCategory (scalarReductionSource l E U)) ≅
    IntegralOpenReduction.shriek l E j o ⋙ IntegralOpenReduction.star l E j o),
    ∃ (_unit_hom : unit.hom = (IntegralOpenReduction.openAdjunction l E j o).unit),
    ∃ (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
    integralOperationsGoodComplex l E W P →
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P),
    ∃ (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P)),
    ∃ (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P)),
    ∃ (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
    rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o),
    ∃ (_ordinary_representative : ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (F : CochainComplex (scalarReductionSource l E X) ℤ)
      (hQ : integralOperationsGoodComplex l E U Q)
      (hF : integralOperationsGoodComplex l E X F),
    HEq (q.tensorX.ordinary.representative.hom.app
        (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q,
          flat X _ (extendGood Q hQ)⟩, ⟨F, flat X F hF⟩) ≫
      q.tensorX.ordinary.tensor.map (Prod.mkHom
        ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.inv.app Q) (𝟙 _)) ≫
      ordinary.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj F) ≫
      (IntegralOpenReduction.shriek l E j o).map
        (q.tensorU.ordinary.tensor.map (Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        (q.tensorU.ordinary.representative.inv.app
          (⟨Q, flat U Q hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            flat U _ (restrictGood F hF)⟩)) ≫
      (IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app
        ((constructibleTensorTotal l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)))
      (DerivedCategory.Q.map (m.totalComparison.chain Q F).hom)),
    ∃ (gamma : completedLeft l E j o ≅ completedRight l E j o),
    ∃ (_units : ∀ K : sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    (q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj)) ≫
        gamma.hom.app K =
      ordinary.hom.app (K.1.obj, K.2.obj) ≫
        (IntegralOpenReduction.shriek l E j o).map
          ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    ∃ (_invertibleUnits : ∀ K :
      sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    IsIso ((q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj))) ∧
      IsIso ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    ∃ (_representative : ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (F : CochainComplex (scalarReductionSource l E X) ℤ)
      (hQ : integralOperationsGoodComplex l E U Q)
      (hF : integralOperationsGoodComplex l E X F)
      (hK : sfIntegralConstructible l E U (DerivedCategory.Q.obj Q))
      (hP : sfIntegralConstructible l E X (DerivedCategory.Q.obj F))
      (z : OpenTensorQuotient.StrictSquare l E j o m.totalComparison q.scalar st
        q.strictScalar Q F),
    OpenTensorQuotient.RoosNormalization l E X q.tensorX
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper →
    OpenTensorQuotient.RoosNormalization l E U q.tensorU Q
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower →
    gamma.hom.app (⟨DerivedCategory.Q.obj Q, hK⟩, ⟨DerivedCategory.Q.obj F, hP⟩) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensor l E U).map (Prod.mkHom (𝟙 _)
          ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F))) ≫
      (IntegralOpenReduction.shriek l E j o).map
        ((integralCompletedTensorComparison l E U).hom.app
          (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
            restrictGood F hF⟩)) ≫
      (extension.derived (IntegralOpenReduction.extension l E j o)
        ((integralOperationsTensorTowerFunctor l E U).obj
          (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F))).hom =
      (integralCompletedTensor l E X).map (Prod.mkHom
        ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q) (𝟙 _)) ≫
      (integralCompletedTensorComparison l E X).hom.app
        (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, extendGood Q hQ⟩, ⟨F, hF⟩) ≫
      DerivedCategory.Q.map (integralOperationsRoosMap z.gamma.hom)),
    ∃ (tensorRestriction : completedLeft l E j o ⋙ IntegralOpenReduction.star l E j o ≅
    completedInside l E j o),
    ∃ (_restriction_identity : ∀ K :
      sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    (IntegralOpenReduction.star l E j o).map (gamma.hom.app K) ≫
        unit.inv.app ((completedInside l E j o).obj K) = tensorRestriction.hom.app K),
    ∀ (Q : CochainComplex (scalarReductionSource l E U) ℤ)
      (F : CochainComplex (scalarReductionSource l E X) ℤ)
      (hQ : integralOperationsGoodComplex l E U Q)
      (hF : integralOperationsGoodComplex l E X F)
      (hK : sfIntegralConstructible l E U (DerivedCategory.Q.obj Q))
      (hP : sfIntegralConstructible l E X (DerivedCategory.Q.obj F))
      (z : OpenTensorQuotient.StrictSquare l E j o m.totalComparison q.scalar st
        q.strictScalar Q F),
    OpenTensorQuotient.RoosNormalization l E X q.tensorX
      ((OpenSemilinearTensor.extensionComplex l E j o).obj Q) F z.upper →
    OpenTensorQuotient.RoosNormalization l E U q.tensorU Q
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj F) z.lower →
    ∃ delta : (onTowers (IntegralOpenReduction.restriction l E j o)).obj
        ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F)) ≅
      (integralOperationsTensorTowerFunctor l E U).obj
        (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F),
    (∀ (n : ℕ) (i : ℤ),
      ((delta.hom.app (op n)).f i) =
        (IntegralOpenReduction.restriction l E j o).map ((z.gamma.hom.app (op n)).f i) ≫
          moduleUnit.inv.app
            ((((integralOperationsTensorTowerFunctor l E U).obj
              (Q, (OpenSemilinearTensor.restrictionComplex l E j o).obj F)).obj (op n)).X i)) ∧
    tensorRestriction.hom.app
        (⟨DerivedCategory.Q.obj Q, hK⟩, ⟨DerivedCategory.Q.obj F, hP⟩) ≫
      (integralCompletedTensor l E U).map (Prod.mkHom (𝟙 _)
        ((IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.hom.app F)) ≫
      (integralCompletedTensorComparison l E U).hom.app
        (⟨Q, hQ⟩, ⟨(OpenSemilinearTensor.restrictionComplex l E j o).obj F,
          restrictGood F hF⟩) =
      (IntegralOpenReduction.star l E j o).map
        ((integralCompletedTensor l E X).map (Prod.mkHom
          ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.hom.app Q)
          (𝟙 _)) ≫
          (integralCompletedTensorComparison l E X).hom.app
            (⟨(OpenSemilinearTensor.extensionComplex l E j o).obj Q, extendGood Q hQ⟩,
              ⟨F, hF⟩)) ≫
      (restriction.derived (IntegralOpenReduction.restriction l E j o)
        ((integralOperationsTensorTowerFunctor l E X).obj
          ((OpenSemilinearTensor.extensionComplex l E j o).obj Q, F))).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosMap delta.hom)

/-- Exactness together with the specified comparison predicate. The exactness
witnesses are supplied by the conclusion, not imposed as additional hypotheses.
Source: Stacks 09BP (blueprint: lem-sf-open-projection-roos-completion). -/
def Completion : Prop :=
  ∃ (hL : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o))
    (hC : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)),
  CompletionData l E j o SX SU AX AU st m c q
    (restrictionLimits := hL) (restrictionColimits := hC)

attribute [local irreducible] CompletionData Completion

```

## New

The identical block above is declared in
`Sheaf.SixFunctors.OpenProjectionRoosCompletionData` and reexported by
`public import Sheaf.SixFunctors.OpenProjectionRoosCompletionData` in the original module.
The original theorem's signature and docstring are unchanged. Its proof now assembles
three separate construction statements, proves flatness conversion and extension
preservation, and explicitly constructs the canonical completed restriction isomorphism.

The three public predicate definitions added to the data module name the ordinary,
completed and restriction representative clauses. CompletionData uses these names in
place of their bodies. A script expanded all three names and verified the entire original
CompletionData/Completion declaration block byte for byte. The construction-step signatures
also refer to these names. This is a definitional refactor with no change in strength.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | C4 | Same public interface, complete assembly proof. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | new | Identical extracted interface, no sorry. |
| Sheaf.SixFunctors.OpenProjectionOrdinaryRoos | new | Ordinary and signed Roos construction step. |
| Sheaf.SixFunctors.OpenProjectionCompletedSquare | new | Completed augmentation construction step. |
| Sheaf.SixFunctors.OpenProjectionRestrictionNormalization | new | Strict restriction/unit construction step. |

`tools/downstream.py Sheaf.SixFunctors.OpenProjectionRoosCompletion` reports zero downstream
Lean modules. Searching both source trees for the module and namespace found no external
uses. DAG parents continue to cite the unchanged original theorem; none is withdrawn or
adapted. The extracted declaration block was compared verbatim against the original.

## Status

landed 20261025T094942-L-3276214 2026-10-25 (merge of deliver/C4/Sheaf.SixFunctors.OpenProjectionRoosCompletion)
