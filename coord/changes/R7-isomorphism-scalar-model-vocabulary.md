# IsomorphismScalarTensor: move the unchanged model vocabulary to its cochain specialization

## Reason

The completed and finite comparison specializations must be separate statement modules.
They use the existing model functors and normalization predicates. Move that vocabulary
verbatim to `Sheaf.Paper.IsomorphismScalarCompletedModel`, publicly imported by the item,
to avoid a cycle. No definition body, signature, universe, attribute or mathematical meaning
changes. All original public imports are retained. The sole original theorem is proved
from two strictly smaller cochain obligations and an actual normalized derived descent proof.
This is a decomposition, not a net reduction of sorry count.

The unchanged definitions remain real constructions. No witness is selected from either
new holed theorem. The completed comparison obligation has no finite or derived content;
the finite obligation takes its completed comparison as input and has no preservation or
derived content. The private derived proof uses the existing generic categorical descent
helpers, whose universes are independent, instead of the published geometric specialization
which fixes its coefficient universe to the site universe.

## Old

The item declared the following vocabulary directly:

```lean
/-- The existing ordinary extension at a finite level, supplied with its universal
counit. Its objects and maps are fixed by the sheafified balanced tensor.
Source: Stacks 03EK and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def finiteChangeData (W : Scheme.{t}) (n : ℕ) :=
  Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (integralScalarQuotientSheafMap l E L ι W n))

/-- Ordinary extension from E's finite coefficient ring to L's, with the same index.
Source: Stacks 03EK (blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev finiteExtension (W : Scheme.{t}) (n : ℕ) :=
  (finiteChangeData l E L ι W n).E

/-- The actual balanced pure tensor in finite extension, including the witness's
object identification. Source: Stacks 03EK
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def finitePure (W : Scheme.{t}) (n : ℕ)
    (M : integralOperationsFiniteModules l E W n) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : M.val.obj U) :
    ((finiteExtension l E L ι W n).obj M).val.obj U :=
  (eqToHom ((finiteChangeData l E L ι W n).obj_eq M).symm).val.app U
    ((toSheafify (ProEt.topology W)
      (SheafOfModules.changeOfRingsPresheaf
        (integralScalarQuotientSheafMap l E L ι W n) M).presheaf).app U
      (s ⊗ₜ[(integralCoefficientCommRingSheaf l E W n).obj.obj U,
        ((integralScalarQuotientSheafMap l E L ι W n).hom.app U).hom] x))

/-- Completed-coefficient inverse image on complexes.
Source: Stacks 03D6 (blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev inverseComplex :=
  (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)

/-- Z as a functor of P. Source: Stacks 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev leftComplex :=
  inverseComplex l E g ⋙ completedOrdinaryScalarComplex l E L ι X

/-- G_L Q as a functor of P. Source: Stacks 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev rightComplex :=
  completedOrdinaryScalarComplex l E L ι Y ⋙ inverseComplex l L g

/-- The lower left: reduce over E, transport its finite action, then extend to L.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev finiteLeft (n : ℕ) :=
  unrestrictedIntegralFiniteComplex l E Y n ⋙
    (inverseImageFiniteModules l E g n).mapHomologicalComplex (.up ℤ) ⋙
      (finiteExtension l E L ι X n).mapHomologicalComplex (.up ℤ)

/-- The lower right: extend directly to L's finite coefficients, then inverse image.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev finiteRight (n : ℕ) :=
  integralScalarFiniteComplex l E L ι Y n ⋙
    (inverseImageFiniteModules l L g n).mapHomologicalComplex (.up ℤ)

/-- Lower-left complex with its completed L action, for quotient and transition maps.
Source: Stacks 03D2 (blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev restrictedLeft (n : ℕ) :=
  finiteLeft l E L ι g n ⋙ integralOperationsRestrict l L X n

/-- Lower-right complex with its completed L action, for quotient and transition maps.
Source: Stacks 03D2 (blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
abbrev restrictedRight (n : ℕ) :=
  finiteRight l E L ι g n ⋙ integralOperationsRestrict l L X n

/-- A double tensor in the lower-left complex, in the canonical sectionwise model.
Source: Stacks 03EK and 03EL
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def doublePure (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (U : X.ProEt)
    (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((restrictedLeft l E L ι g n).obj P).X i).val.obj (op U) :=
  finitePure l E L ι X n
    ((inverseImageFiniteModules l E g n).obj
      ((unrestrictedIntegralReductionFunctor l E Y n).obj (P.X i))) (op U) s
    (unrestrictedIntegralTensorSection l E Y n (P.X i)
      (op ((proEtaleIsoPostcompose g).obj U)) a x)

attribute [local irreducible] completedScalarChangeData completedOrdinaryScalarExtension
  completedDerivedScalarExtension completedScalarCounit completedScalarTensorSection
  integralScalarReductionWitness integralScalarReduction integralScalarTensorSection
  unrestrictedIntegralReductionExistence unrestrictedIntegralReductionFunctor
  unrestrictedIntegralTensorSection inverseImageCompletedCoefficientMap finiteChangeData
  finitePure doublePure

/-- K-flatness and flat terms for inverse image, Q and Z.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def PreservesModels : Prop :=
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      integralOperationsGoodComplex l E X ((inverseComplex l E g).obj P.obj) ∧
      integralOperationsGoodComplex l L Y
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj) ∧
      integralOperationsGoodComplex l L X ((leftComplex l E L ι g).obj P.obj)

/-- The local formula for the completed tensor isomorphism.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def CompletedFormula
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g) : Prop :=
    ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory) (i : ℤ) (U : X.ProEt)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      ((b.hom.app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι X
          (((inverseComplex l E g).obj P.obj).X i) (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s) x) =
        completedScalarTensorSection l E L ι Y (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x

/-- The finite comparison on double pure tensors.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def FiniteFormula
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L X n).obj.obj (op U))
      (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((integralOperationsRestrict l L X n).map ((bfin n).hom.app P)).f i).val.app (op U)
        (doublePure l E L ι g n P.obj i U s a x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((@id ((integralCoefficientCommRingSheaf l L Y n).obj.obj
            (op ((proEtaleIsoPostcompose g).obj U)))
          ((inv (inverseImageFiniteCoefficientMap l L g n)).hom.app (op U) s)) *
          (integralScalarQuotientSheafMap l E L ι Y n).hom.app
            (op ((proEtaleIsoPostcompose g).obj U)) a) x

/-- The canonical quotient from Z on pure tensors.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def LeftQuotientFormula
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((vleft n).app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι X
          (((inverseComplex l E g).obj P.obj).X i) (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s) x) =
      doublePure l E L ι g n P.obj i U
        ((completedIntegralCommRingProjectionUnrestricted l L X n).hom.app (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s)) 1 x

/-- The inverse image of the coefficient quotient from Q.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def RightQuotientFormula
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((vright n).app P).f i).val.app (op U)
        (completedScalarTensorSection l E L ι Y (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) s) x

/-- The specified completed-to-finite square.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def QuotientSquare
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory),
      b.hom.app P ≫ (vright n).app P =
        (vleft n).app P ≫ (integralOperationsRestrict l L X n).map ((bfin n).hom.app P)

/-- The quotient transition on the two scalar factors on the left.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def LeftTransitionFormula
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L X (n + 1)).obj.obj (op U))
      (a : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((tleft n).app P).f i).val.app (op U)
        (doublePure l E L ι g (n + 1) P.obj i U s a x) =
      doublePure l E L ι g n P.obj i U
        ((integralCoefficientSheafTransition l L X n).hom.app (op U) s)
        ((integralCoefficientSheafTransition l E Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) a) x

/-- The quotient transition on the final scalar factor on the right.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def RightTransitionFormula
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (i : ℤ) (U : X.ProEt)
      (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (x : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((tright n).app P).f i).val.app (op U)
        (integralScalarTensorSection l E L ι Y (n + 1) (P.obj.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) s x) =
      integralScalarTensorSection l E L ι Y n (P.obj.X i)
        (op ((proEtaleIsoPostcompose g).obj U))
        ((integralCoefficientSheafTransition l L Y n).hom.app
          (op ((proEtaleIsoPostcompose g).obj U)) s) x

/-- The specified finite comparison commutes with quotient transitions.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def TransitionSquare
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n) : Prop :=
    ∀ (n : ℕ) (P : (integralOperationsGoodComplex l E Y).FullSubcategory),
      (integralOperationsRestrict l L X (n + 1)).map ((bfin (n + 1)).hom.app P) ≫
          (tright n).app P =
        (tleft n).app P ≫ (integralOperationsRestrict l L X n).map ((bfin n).hom.app P)

/-- Canonical K-flat computations and descent of the same chain comparison.
Source: the node calculation, Steps 1–7; Stacks 03EK, 03EL and 06YY
(blueprint: lem-weil-isomorphism-scalar-tensor-kflat-model). -/
def DerivedModel
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (β : inverseImageIntegralDerived l E g ⋙ completedDerivedScalarExtension l E L ι X ≅
        completedDerivedScalarExtension l E L ι Y ⋙ inverseImageIntegralDerived l L g) : Prop :=
    ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      IsIso (completedScalarCounit l E L ι Y P.obj) ∧
      IsIso (completedScalarCounit l E L ι X ((inverseComplex l E g).obj P.obj)) ∧
      β.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (inverseImageIntegralDerived l L g).map (completedScalarCounit l E L ι Y P.obj) ≫
          (inverseImageIntegralModules l L g).mapDerivedCategoryFactors.hom.app
            ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj) =
        (completedDerivedScalarExtension l E L ι X).map
            ((inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
          completedScalarCounit l E L ι X ((inverseComplex l E g).obj P.obj) ≫
          DerivedCategory.Q.map (b.hom.app P)

```

## New

The exact declarations above, including their docstrings, are now in
`lean/Sheaf/Paper/IsomorphismScalarCompletedModel.lean`.
The item retains all its original public imports and publicly imports that module:

```lean
public import Sheaf.Paper.IsomorphismScalarCompletedModel
```

All qualified names, signatures, declaration bodies and visibility remain the same.
The item theorem itself keeps its exact signature. Only theorem proofs and proof imports
otherwise change. No target declaration or definition used by a target changes meaning;
the statement review can check literal equality of the moved vocabulary.

## Users

The table conservatively includes every transitive importer. The five direct importers
compiled unchanged against the delivered overlay, all accepted by the compile service;
their unchanged temporary source copies have been removed. No consumer adaptation was needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicClosureScalarCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreZeroMap | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageHeartExactness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicFiniteConstructibilityComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicFiniteScalarCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStageData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreScalar | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | G3 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicReindexingCore | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicReindexingFunctoriality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicReindexingHom | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionConstructions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | E2 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.AutomorphismSquareRationalScalar | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.BarrettIndRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartDncNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartDncSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationDiagramFibres | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationExactDiagram | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteConstruction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteOperations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRealizationLocalSpectrum | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRealizationPunctualPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationTransportData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CochainLocalizationTensorIso | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonConstantUnitFrobenius | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonFrobeniusSquareNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageEvaluationNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageOpenHeartAdjunction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | F7 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportStageActionAdjunction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompletedContinuousHomHypotheses | T9 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompletedPullbackFractionDescent | C3 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompositionIteratedMateExpansion | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CompositionSingleMatePresentation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionCyclicSheetPartition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackSheetComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetTensorSplitting | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | Z9 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateAdjunctionComposition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateCartierBoundarySign | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionSiteTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateSupportedProductRecursion | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerCompactTranspose | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerExceptionalCompositors | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationFusion | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CurveClassicalPullbackExists | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.CurveRestrictionLocalPowers | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DerivedTensorRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementSystemData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementSystemRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ExplicitScalarConeWordCoordinates | M8 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricOrientationExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityCoordinates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityFactors | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricTensorExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarTensorData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteScalarTensorSource | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTateSourceMap | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorLineChartReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorPullbackTensorReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusCompactIntegralNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusCompactRationalNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackOrdinaryExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.FrobeniusWitnessedCompactification | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.GeometricCommonStageDirectImage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.GeometricSmoothReconstructionSetup | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralEquivarianceMate | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralEquivarianceNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralGeometricComparisonData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralGeometricComparisonRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralGeometricPurityRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralGeometricReindexingRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralGeometricSupportRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralGeometricTransposeIdentity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralLissePullbackNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IsomorphismFieldTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IsomorphismFieldTransportClauses | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IsomorphismFieldTransportCommonStage | Q9 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IsomorphismFieldTransportFiniteStage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IsomorphismFieldTransportRationalScalar | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IsomorphismScalarAugmentationCone | R6 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | R7 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.IteratedTateSourceComposite | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.KummerSiteCohomologyNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeChoiceExistence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLiftData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeLisseDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeNormalizedRealizations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeRealizationFaithful | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeSingleComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeScalarTower | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusStepCompatibility | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | G6 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.LocallyFiniteCompactSupportStageAction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeCoefficientInverseImage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeCompactSupportFiniteComparison | G8 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeCompactSupportGeometry | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeDirectImageSections | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilComparisonStructure | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilDerivedInductionComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilFreeCoproduct | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilHeartProperties | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilInductionComparisonData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilInductionSummands | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilProperNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedCommonEvaluationForStructure | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedCommonEvaluationNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedPullbackCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedPullbackNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedPullbackObjects | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.OpenWeilCarrierRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.OpenWeilCoefficientFibres | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.OpenWeilFiniteStageFrobenius | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.OpenWeilGeometricFibres | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.OpenWeilPunctualSpectrum | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.OrientationCoordinateBoundaryPullback | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.OrientationCoordinateModelBoundary | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.OrientationLocalResidue | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodNormalizedTensorSignedShifts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodReindexingCompletedEvaluationReflection | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodReindexingCompletionUnitTensor | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodReindexingDerivedComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodReindexingGoodComplex | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodReindexingRestrictedTower | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PodReindexingStrictComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PoincareDualityConventions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointFiniteMultiplicationInverse | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointFrobeniusNormalizationDefinitions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointIdentityExchangeRecipe | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointInverseImageCoefficientTower | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointQuotientComparisonCoordinates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointRealizationStandardCohomology | F1 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointRestrictionOrdinaryTensorSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointScalarPunctualSpectrum | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointWeilAlgebraicFlag | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlagData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | T6 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProjectionIdentityAssembly | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProjectionIdentityPullbackUnits | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProjectionTensorIntegration | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProjectionUnitPresentationNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProperSupportCoefficientAdjunction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProperSupportFiniteAdjunction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityCompactSupportTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityKappaStages | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityKummerTriangleConcentration | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityTateDatum | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalAmbientPullComposition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalAmbientPullModels | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalBalancedFreePullback | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalContinuousComparisonCoherence | H8 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalContinuousFiltrationModels | K7 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalContinuousPullbackTransport | K8 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPullSingleComputation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | K9 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPullbackFlatComputationCounit | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationHomTransport | Y5 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarBalancedLocalization | M5 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarMixedUnitCancellation | M6 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackModels | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ReindexingSystemHomReductionSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RelativeKunnethClosedFibre | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RelativeKunnethConstructions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ScalarFibreCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ScalarFibreComponentData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ScalarFibreComponents | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ScalarFibreNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SectionEtaleOpenCancellation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SectionsRationalModelComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearCommonOrdinaryCubes | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearCommonRefinementCubes | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearCommonSupportCubes | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearRationalOrdinaryCubes | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearRationalRefinementCubes | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SemilinearRationalSupportCubes | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TensorHeartSpecialization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorIntegrationIdentityAdjunct | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilGeometricFiberProperties | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilIndOpenRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilIndOpenRepresentability | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilIndProperHigherRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilIndProperHigherRepresentability | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilIndProperOpenHigher | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlImmersionRestrictionAssembly | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlOpenExtensionAssembly | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlWeilPullCompositorEquivariance | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityCommonComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.CoefWeilNormalizedDuality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralSystemExistence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyCoefficientCocycle | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyComparisonFactors | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRationalCocycle | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.KappaCoefficientCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.KappaGeometricComparisons | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.KappaMixedCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeSingleShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeSystemSquare | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.TensorExchangeNormalizedModels | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportBrownConstructibility | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | F8 | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same exported signatures and definition bodies via public reexport; no adaptation. |

## Status

landed 20261027T123533-L-2318397 2026-10-27 (merge of deliver/R7/Sheaf.Paper.IsomorphismScalarTensorKFlatModel)
